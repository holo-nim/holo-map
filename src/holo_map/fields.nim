## utilities for handling pragmas in object fields

import std/[macros, tables], ./caseutils

type
  NamePatternKind* = enum
    NoName,
    NameOriginal, ## uses the field name
    NameString, ## uses custom string and ignores field name
    NameSnakeCase ## converts field name to snake case
    # maybe raw json unquoted name
    NameConcat
  NamePattern* = object
    ## string pattern to apply to a given field name to use in json
    case kind*: NamePatternKind
    of NoName: discard
    of NameOriginal: discard
    of NameString: str*: string
    of NameSnakeCase: discard
    of NameConcat: concat*: seq[NamePattern]
  FieldMapping* = object
    ## json serialization/deserialization options for an object field
    readNames*: seq[NamePattern]
      ## names that are accepted for this field when encountered in json
      ## if none are given, this defaults to the original field name and a snake case version of it
    ignoreRead*, ignoreDump*: bool
      ## whether or not to ignore a field when encountered in json or when dumping to json
    dumpName*: NamePattern
      ## name to dump this field in json by
      ## if not given, this defaults to the original field name
    # maybe normalize case option
  FieldMappingArg* = concept
    ## argument allowed for mapping pragma
    proc toFieldMapping(self: Self): FieldMapping
  MappingGroup* = string
    ## filter to set mapping settings for a specific format
    ## currently just a string identifier for the format
    ## empty allows everything

const AnyMappingGroup* = MappingGroup("")

proc `<=`*(a, b: MappingGroup): bool =
  ## returns true if `a` is a subset of `b`
  if b == AnyMappingGroup:
    result = true
  else:
    result = a == b

template mapping*(options: FieldMapping) {.pragma.}
  ## sets the json serialization/deserialization options for a field
template mapping*(options: FieldMappingArg) {.pragma.}
  ## convenience wrapper that calls `toFieldMapping` on the given argument

template mapping*(group: static MappingGroup, options: FieldMapping) {.pragma.}
  ## sets the json serialization/deserialization options for a field
  ## filtered to formats encompassed by the given mapping group
template mapping*(group: static MappingGroup, options: FieldMappingArg) {.pragma.}
  ## convenience wrapper that calls `toFieldMapping` on the given argument
  ## filtered to formats encompassed by the given mapping group

proc toName*(str: string): NamePattern =
  ## creates a name pattern that uses a specific string instead of the field name
  NamePattern(kind: NameString, str: str)

proc snakeCase*(): NamePattern =
  ## creates a name pattern that just converts a field name to snake case
  NamePattern(kind: NameSnakeCase)

proc verbatim*(): NamePattern =
  NamePattern(kind: NameOriginal)

proc toFieldMapping*(options: FieldMapping): FieldMapping {.inline.} =
  ## hook called on the argument to the `json` pragma to convert it to a full field option object
  options

proc toFieldMapping*(name: NamePattern): FieldMapping =
  ## hook called on the argument to the `json` pragma to convert it to a full field option object,
  ## for a name pattern this sets both the serialization and deserialization name of the field to it
  FieldMapping(readNames: @[name], dumpName: name)

proc toFieldMapping*(name: string): FieldMapping =
  ## hook called on the argument to the `json` pragma to convert it to a full field option object,
  ## for a string this sets both the serialization and deserialization name of the field to it
  toFieldMapping(toName(name))

proc toFieldMapping*(enabled: bool): FieldMapping =
  ## hook called on the argument to the `json` pragma to convert it to a full field option object,
  ## for a bool this sets whether or not to enable serialization and deserialization for this field
  FieldMapping(ignoreRead: not enabled, ignoreDump: not enabled)

proc ignore*(): FieldMapping =
  ## creates a field option object that ignores this field in both serialization and deserialization
  FieldMapping(ignoreRead: true, ignoreDump: true)

proc apply*(pattern: NamePattern, name: string): string =
  ## applies a name pattern to a given name
  case pattern.kind
  of NoName:
    result = ""
  of NameOriginal:
    result = name
  of NameString:
    result = pattern.str
  of NameSnakeCase:
    result = toSnakeCase(name)
  of NameConcat:
    if pattern.concat.len == 0: return ""
    result = apply(pattern.concat[0], name)
    for i in 1 ..< pattern.concat.len: result.add apply(pattern.concat[i], name)

proc hasReadNames*(options: FieldMapping): bool =
  options.readNames.len != 0

proc getReadNames*(fieldName: string, options: FieldMapping, default: seq[NamePattern]): seq[string] =
  ## gives the names accepted for this field when encountered in json
  ## if none are given, this defaults to the original field name and a snake case version of it
  result = @[]
  let names = if hasReadNames(options): options.readNames else: default
  for pat in names:
    let name = apply(pat, fieldName)
    if name notin result: result.add name

proc hasDumpName*(options: FieldMapping): bool =
  options.dumpName.kind == NoName

proc getDumpName*(fieldName: string, options: FieldMapping, default: NamePattern): string =
  ## gives the name to dump this field in json by
  ## if not given, this defaults to the original field name
  let name = if hasDumpName(options): options.dumpName else: default
  result = apply(name, fieldName)

proc realBasename(n: NimNode): string =
  var n = n
  if n.kind == nnkPragmaExpr: n = n[0]
  if n.kind == nnkPostfix: n = n[^1]
  result = $n

proc iterFieldNames(names: var seq[(string, NimNode)], list: NimNode) =
  case list.kind
  of nnkRecList, nnkTupleTy:
    for r in list:
      iterFieldNames(names, r)
  of nnkRecCase:
    iterFieldNames(names, list[0])
    for bi in 1 ..< list.len:
      expectKind list[bi], {nnkOfBranch, nnkElifBranch, nnkElse}
      iterFieldNames(names, list[bi][^1])
  of nnkRecWhen:
    for bi in 0 ..< list.len:
      expectKind list[bi], {nnkElifBranch, nnkElse}
      iterFieldNames(names, list[bi][^1])
  of nnkIdentDefs:
    for i in 0 ..< list.len - 2:
      let name = realBasename(list[i])
      var prag: NimNode = nil
      if list[i].kind == nnkPragmaExpr:
        prag = list[i][1]
      block doAdd:
        for existing in names.mitems:
          if existing[0] == name:
            break doAdd
        names.add (name, prag)
  of nnkSym:
    when defined(holojsonySymPragmaWarning):
      warning "got just sym for object field, maybe missing pragma information", list
    let name = $list
    names.add (name, nil)
  of nnkDiscardStmt, nnkNilLit, nnkEmpty: discard
  else:
    error "unknown object field AST kind " & $list.kind, list

const
  nnkPragmaCallKinds = {nnkExprColonExpr, nnkCall, nnkCallStrLit}

proc matchCustomPragma(sym: NimNode): bool =
  result = sym.kind == nnkSym and sym.eqIdent"mapping"
  if result:
    let impl = getImpl(sym)
    result = impl != nil and impl.kind == nnkTemplateDef

proc getMappingGroupFromNode(node: NimNode): MappingGroup =
  if node.kind in {nnkStrLit..nnkTripleStrLit, nnkIdent, nnkAccQuoted, nnkSym, nnkOpenSymChoice, nnkClosedSymChoice}:
    result = MappingGroup($node)
  else:
    when false:
      # as expected does not work lol
      result = cast[MappingGroup](node)
    else:
      error("invalid node for mapping group constant: " & treeRepr(node), node)

proc buildFieldMappingPairs*(obj: NimNode, group: MappingGroup): NimNode =
  var names: seq[(string, NimNode)] = @[]
  var t = obj
  var supportsCustomPragma = false
  while t != nil:
    # very horribly try to copy macros.customPragma:
    var impl = getTypeInst(t)
    while true:
      if impl.kind in {nnkRefTy, nnkPtrTy, nnkVarTy, nnkOutTy}:
        if impl[^1].kind == nnkObjectTy:
          impl = impl[^1]
        else:
          impl = getTypeInst(impl[^1])
      elif impl.kind == nnkBracketExpr and impl[0].eqIdent"typeDesc":
        impl = getTypeInst(impl[1])
      elif impl.kind == nnkBracketExpr and impl[0].kind == nnkSym:
        impl = getImpl(impl[0])[^1]
      elif impl.kind == nnkSym:
        impl = getImpl(impl)[^1]
      else:
        break
    case impl.kind
    of nnkTupleTy:
      supportsCustomPragma = false
      iterFieldNames(names, impl)
      t = nil
    #of nnkEnumTy:
    #  supportsCustomPragma = false
    #  t = nil
    of nnkObjectTy:
      supportsCustomPragma = true
      iterFieldNames(names, impl[^1])
      t = nil
      if impl[1].kind != nnkEmpty:
        expectKind impl[1], nnkOfInherit
        t = impl[1][0]
    else:
      error "got unknown object type kind " & $impl.kind, impl
  result = newNimNode(nnkBracket, obj)
  for name, prag in names.items:
    var val: NimNode = nil
    var lastFilter = AnyMappingGroup
    if prag != nil and supportsCustomPragma:
      # again copied from macros.customPragma
      for p in prag:
        if p.kind in nnkPragmaCallKinds and p.len > 0 and p[0].kind == nnkSym and matchCustomPragma(p[0]):
          let def = p[0].getImpl[3]
          let arg = if def.len == 3: p[2] else: p[1] 
          let filter = if def.len == 3: getMappingGroupFromNode(p[1]) else: AnyMappingGroup
          if group <= filter and filter <= lastFilter:
            val = arg
            lastFilter = filter
          when false:
            if p.len == 2 or
                # ??? generics support?
                (p.len == 3 and p[1].kind == nnkSym and p[1].symKind == nskType):
              val = p[1]
            else:
              let def = p[0].getImpl[3]
              val = newTree(nnkPar)
              for i in 1 ..< def.len:
                let key = def[i][0]
                let val = p[i]
                val.add newTree(nnkExprColonExpr, key, val)
    if val == nil:
      val = quote do: FieldMapping()
    else:
      val = quote do: toFieldMapping(`val`)
    result.add(newTree(nnkTupleConstr,
      newLit(name),
      val))
    when false:
      let ident = ident(name)
      if isTuple:
        quote do:
          FieldMapping()
      else:
        quote do:
          when hasCustomPragma(`obj`.`ident`, `pragmaSym`):
            toFieldMapping(getCustomPragmaVal(`obj`.`ident`, `pragmaSym`))
          else:
            FieldMapping()
  result = newCall(bindSym"@", result)

type
  FieldedType* = (object | ref object | tuple)
    # XXX also maybe enum
  FieldMappingPairs* = seq[(string, FieldMapping)]

macro defaultFieldMappingPairs*[T: FieldedType](obj: typedesc[T], group: static MappingGroup = AnyMappingGroup): FieldMappingPairs =
  result = buildFieldMappingPairs(obj, group)

template fieldMappingPairs*[T: FieldedType](obj: typedesc[T], group: static MappingGroup = AnyMappingGroup): FieldMappingPairs =
  # XXX check if overloadable, so that types can define their own mappings?
  defaultFieldMappingPairs(obj, group)

type HasFieldMappings* = concept
  proc fieldMappingPairs(obj: typedesc[Self], group: static MappingGroup): FieldMappingPairs

template fieldMappingTable*[T: HasFieldMappings](obj: typedesc[T], group: static MappingGroup = AnyMappingGroup): Table[string, FieldMapping] =
  mixin fieldMappingPairs
  toTable fieldMappingPairs(obj, group)

when false: # runtime overloadable?
  macro fieldMappingPairs*[T: FieldedType](obj: T, group: static MappingGroup = AnyMappingGroup): untyped =
    result = buildFieldMappingPairs(obj, group)

  template fieldMappingTable*[T: FieldedType](obj: T, group: static MappingGroup = AnyMappingGroup): Table[string, FieldMapping] =
    mixin fieldMappingPairs
    toTable fieldMappingPairs(obj, group)
else:
  template defaultFieldMappingPairs*[T: FieldedType](obj: T, group: static MappingGroup = AnyMappingGroup): untyped =
    defaultFieldMappingPairs(T, group)

  template fieldMappingPairs*[T: HasFieldMappings](obj: T, group: static MappingGroup = AnyMappingGroup): untyped =
    mixin fieldMappingPairs
    fieldMappingPairs(T, group)

  template fieldMappingTable*[T: HasFieldMappings](obj: T, group: static MappingGroup = AnyMappingGroup): Table[string, FieldMapping] =
    mixin fieldMappingTable
    fieldMappingTable(T, group)
