## utilities for mapping fields of types

import std/[macros, tables], ./[groups, caseutils], private/macroutils

type
  NamePatternKind* = enum
    NoName,
    NameOriginal, ## uses the field name
    NameString, ## uses custom string and ignores field name
    NameSnakeCase ## converts field name to snake case
    # maybe raw name like unquoted json
    NameConcat
  NamePattern* = object
    ## string pattern to apply to a given field name to use in mapping
    case kind*: NamePatternKind
    of NoName: discard
    of NameOriginal: discard
    of NameString: str*: string
    of NameSnakeCase: discard
    of NameConcat: concat*: seq[NamePattern]
  InputFieldMapping* = object
    ## mapped values for input of a field
    names*: seq[NamePattern]
      ## names that are accepted for this field when encountered in input
      ## if none are given, a default set of names can be used instead
    ignore*: bool
      ## whether or not to ignore a field when encountered in input
  OutputFieldMapping* = object
    name*: NamePattern
      ## name for this field in output
      ## if not given or set to `NoName`, a default name can be used instead
    ignore*: bool
      ## whether or not to ignore a field when generating output
  FieldMapping* = object
    ## mapping options for a type field
    input*: InputFieldMapping
    output*: OutputFieldMapping
    # maybe normalize case option - needs to be done for the type overall
  FieldMappingArg* = concept
    ## argument allowed for mapping pragma
    proc toFieldMapping(self: Self): FieldMapping

template mapping*(options: FieldMapping) {.pragma.}
  ## sets the mapping options for a field
template mapping*(options: FieldMappingArg) {.pragma.}
  ## convenience wrapper that calls `toFieldMapping` on the given argument

template mapping*(group: static MappingGroup, options: FieldMapping) {.pragma.}
  ## sets the mapping options for a field
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
  ## hook called on the argument to the `mapping` pragma to convert it to a full field option object
  options

proc toFieldMapping*(name: NamePattern): FieldMapping =
  ## hook called on the argument to the `mapping` pragma to convert it to a full field option object,
  ## for a name pattern this sets both the serialization and deserialization name of the field to it
  FieldMapping(input: InputFieldMapping(names: @[name]), output: OutputFieldMapping(name: name))

proc toFieldMapping*(name: string): FieldMapping =
  ## hook called on the argument to the `mapping` pragma to convert it to a full field option object,
  ## for a string this sets both the serialization and deserialization name of the field to it
  toFieldMapping(toName(name))

proc toFieldMapping*(enabled: bool): FieldMapping =
  ## hook called on the argument to the `mapping` pragma to convert it to a full field option object,
  ## for a bool this sets whether or not to enable serialization and deserialization for this field
  FieldMapping(input: InputFieldMapping(ignore: not enabled), output: OutputFieldMapping(ignore: not enabled))

proc ignore*(): FieldMapping =
  ## creates a field option object that ignores this field in both serialization and deserialization
  FieldMapping(input: InputFieldMapping(ignore: true), output: OutputFieldMapping(ignore: true))

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

proc hasInputNames*(options: FieldMapping): bool =
  options.input.names.len != 0

proc getInputNames*(fieldName: string, options: FieldMapping, default: seq[NamePattern]): seq[string] =
  ## gives the names accepted for this field when encountered in input
  ## if none are given, this defaults to the patterns in `default`
  result = @[]
  let names = if hasInputNames(options): options.input.names else: default
  for pat in names:
    let name = apply(pat, fieldName)
    if name notin result: result.add name

proc hasOutputName*(options: FieldMapping): bool =
  options.output.name.kind != NoName

proc getOutputName*(fieldName: string, options: FieldMapping, default: NamePattern): string =
  ## gives the name for this field in output
  ## if not given, this defaults to the pattern in `default`
  let name = if hasOutputName(options): options.output.name else: default
  result = apply(name, fieldName)

type
  FieldedType* = (object | ref object | tuple)
    # XXX also maybe enum
  FieldMappingPairs* = seq[(string, FieldMapping)]
  HasFieldMappings* = concept
    proc fieldMappings(obj: typedesc[Self], group: static MappingGroup): FieldMappingPairs

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
    when defined(holomapSymPragmaWarning):
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
          let filter = if def.len == 3: getMappingGroupFromLiteral(p[1]) else: AnyMappingGroup
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

macro defaultFieldMappings*[T: FieldedType](obj: typedesc[T], group: static MappingGroup = AnyMappingGroup): FieldMappingPairs =
  result = buildFieldMappingPairs(obj, group)

template fieldMappings*[T: FieldedType](obj: typedesc[T], group: static MappingGroup = AnyMappingGroup): FieldMappingPairs =
  ## overloadable, so that types can define their own mappings
  defaultFieldMappings(obj, group)

template fieldMappingTable*[T: HasFieldMappings](obj: typedesc[T], group: static MappingGroup = AnyMappingGroup): Table[string, FieldMapping] =
  mixin fieldMappings
  toTable fieldMappings(obj, group)

when false: # runtime overloadable?
  macro fieldMappings*[T: FieldedType](obj: T, group: static MappingGroup = AnyMappingGroup): untyped =
    result = buildFieldMappingPairs(obj, group)

  template fieldMappingTable*[T: FieldedType](obj: T, group: static MappingGroup = AnyMappingGroup): Table[string, FieldMapping] =
    mixin fieldMappings
    toTable fieldMappings(obj, group)
else:
  template defaultFieldMappings*[T: FieldedType](obj: T, group: static MappingGroup = AnyMappingGroup): untyped =
    defaultFieldMappings(T, group)

  template fieldMappings*[T: HasFieldMappings](obj: T, group: static MappingGroup = AnyMappingGroup): untyped =
    mixin fieldMappings
    fieldMappings(T, group)

  template fieldMappingTable*[T: HasFieldMappings](obj: T, group: static MappingGroup = AnyMappingGroup): Table[string, FieldMapping] =
    mixin fieldMappingTable
    fieldMappingTable(T, group)

proc toUnique[T](x: openArray[T]): seq[T] =
  result = newSeqOfCap[T](x.len)
  for a in x:
    if a notin result:
      result.add(x)

proc isNilAst(n: NimNode): bool =
  n.isNil or n.kind == nnkNilLit or n.eqIdent"nil"

proc wrapNormalizer(normalizer, n: NimNode): NimNode =
  if not isNilAst(normalizer):
    newCall(normalizer, n)
  else:
    n

macro wrapNormalizerMacro(normalizer: typed, n: untyped): untyped =
  result = wrapNormalizer(normalizer, n)

proc addInputNamesToBranch(branch: NimNode, fieldName: string, options: FieldMapping, normalizer: NimNode, defaultInputs: seq[NamePattern]) =
  let inputNames = getInputNames(fieldName, options, defaultInputs)
  if isNilAst(normalizer):
    for name in inputNames:
      branch.add newLit(name)
  else:
    var namesNode = newNimNode(nnkBracket, normalizer)
    for name in inputNames:
      namesNode.add newCall(normalizer, newLit(name))
    branch.add newCall(bindSym"toUnique", namesNode)

macro mapFieldInput*[T: FieldedType](
    v: T, key: string,
    # type of v not used yet but maybe in the future to manually complete `fields` XXX #5
    fields: static FieldMappingPairs,
    normalizer: typed,
    defaultInputs: static seq[NamePattern],
    templToCall, elseBody: untyped): untyped =
  ## calls `templToCall` with the address of the mapped field of `v`
  ## 
  ## if `normalizer` is not `nil`, calls it for both `key` and the generated input names
  ##
  ## warning: currently requires importing `std/importutils` and calling `privateAccess` on the object type to work with private fields
  result = newNimNode(nnkCaseStmt, key)
  result.add wrapNormalizer(normalizer, key)
  for fieldName, options in fields.items:
    if not options.input.ignore:
      var branch = newTree(nnkOfBranch)
      addInputNamesToBranch(branch, fieldName, options, normalizer, defaultInputs)
      branch.add newCall(templToCall, newDotExpr(copy v, ident fieldName))
      #branch.add crudeReplaceIdent(body, "field", newDotExpr(copy v, ident fieldName))
      result.add branch
  if result.len == 1:
    result = newTree(nnkDiscardStmt, newEmptyNode())
  else:
    result.add newTree(nnkElse, elseBody)

import ./variants

macro mapInputVariantFieldName*[T: VariantType](
    obj: typedesc[T], key: string,
    fields: static FieldMappingPairs,
    normalizer: typed,
    defaultInputs: static seq[NamePattern],
    innerFieldTempl, variantFieldTempl, elseBody: untyped) =
  ## finds the variant field name for `key` based on `variants`:
  ## if `key` maps to a variant discriminator, calls `variantFieldTempl` with an identifier of the original field
  ## if `key` maps to a field inside a variant branch, calls `innerFieldTempl` with:
  ##   1. the original field identifier of `key`
  ##   2. the original identifier of the variant field
  ##   3. the first acceptable value of the variant field for the branch that the inner field is in
  ## otherwise, emits `elseBody`
  ## 
  ## if `normalizer` is not `nil`, calls it for both `key` and the generated input names
  result = newNimNode(nnkCaseStmt, key)
  result.add wrapNormalizer(normalizer, key)
  let variants = buildVariants(obj)
  let mappingTable = toTable fields
  if variants.variants.len == 0:
    error("got no object variants", obj)
  for variant in variants.variants:
    block variantField:
      let options = mappingTable.getOrDefault(variant.discrimName, FieldMapping())
      if not options.input.ignore:
        var branch = newNimNode(nnkOfBranch, variantFieldTempl)
        addInputNamesToBranch(branch, variant.discrimName, options, normalizer, defaultInputs)
        branch.add newCall(variantFieldTempl, ident variant.discrimName)
        result.add branch
    for fieldName, branchIndex in variant.fieldsToBranch:
      let options = mappingTable.getOrDefault(fieldName, FieldMapping())
      if not options.input.ignore:
        var branch = newNimNode(nnkOfBranch, variantFieldTempl)
        addInputNamesToBranch(branch, fieldName, options, normalizer, defaultInputs)
        let discrimValue = firstValue(variant.branches[branchIndex])
        branch.add newCall(innerFieldTempl,
          ident fieldName,
          ident variant.discrimName,
          copy discrimValue)
        result.add branch
  if result.len == 1:
    result = newTree(nnkDiscardStmt, newEmptyNode())
  else:
    result.add newTree(nnkElse, elseBody)

template mapInputVariantField*[T: VariantType](
    obj: T, key: string,
    fields: static FieldMappingPairs,
    normalizer: typed,
    defaultInputs: static seq[NamePattern],
    innerFieldTempl, variantFieldTempl, elseBody: untyped) =
  ## finds the variant for `key` in `obj`:
  ## if `key` is a variant discriminator, calls `variantFieldTempl` with the address of `key` in `obj`
  ## if `key` is a field inside a variant branch, calls `innerFieldTempl` with:
  ##   1. the address of `key` in `obj`
  ##   2. the address of the variant field
  ##   3. the first acceptable value of the variant field for the branch that the inner field is in
  ## otherwise, emits `elseBody`
  ## 
  ## if `normalizer` is not `nil`, calls it for both `key` and the generated input names
  template onInnerField(f, discrimName, discrimValue) =
    `innerFieldTempl`(`obj`.`f`, `obj`.`discrimName`, `discrimValue`)
  template onVariantField(f) =
    `variantFieldTempl`(`obj`.`f`)
  mapInputVariantFieldName(T, key, fields, normalizer, defaultInputs, onInnerField, onVariantField, elseBody)

template mapFieldOutput*[T: FieldedType](
    v: T,
    fields: static FieldMappingPairs,
    normalizer: typed,
    defaultOutput: static NamePattern,
    templToCall: untyped): untyped =
  ## calls `templToCall` with: 1. the mapped field address from `v`, 2. the mapped field name
  ## 
  ## if `normalizer` is not `nil`, calls it for both `key` and the generated input names
  const fieldTable = toTable fields
  for k, e in v.fieldPairs:
    const options = fieldTable.getOrDefault(k)
    when not options.output.ignore:
      const outputName = wrapNormalizerMacro(normalizer, getOutputName(k, options, defaultOutput))
      templToCall(e, outputName)

macro mapEnumFieldInput*[T: enum](
  t: typedesc[T], s: string,
  mappings: static FieldMappingPairs,
  normalizer: typed,
  templToCall: untyped) =
  ## calls `templToCall` with the mapped enum field from `s`
  ## 
  ## if `normalizer` is not `nil`, calls it for both `key` and the generated input names
  # XXX missing default arg because of enum string value #6
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
  if impl.kind != nnkEnumTy:
    error "expected enum type for type impl of " & repr(t), impl
  let mappingTable = toTable(mappings)
  result = newNimNode(nnkCaseStmt, s)
  result.add wrapNormalizer(normalizer, s)
  for f in impl:
    # copied from std/enumutils.genEnumCaseStmt
    var fieldSym: NimNode = nil
    var fieldStrNodes: seq[NimNode] = @[]
    case f.kind
    of nnkEmpty: continue # skip first node of `enumTy`
    of nnkSym, nnkIdent, nnkAccQuoted, nnkOpenSymChoice, nnkClosedSymChoice:
      fieldSym = f
    of nnkEnumFieldDef:
      fieldSym = f[0]
      case f[1].kind
      of nnkStrLit .. nnkTripleStrLit:
        fieldStrNodes = @[f[1]]
      of nnkTupleConstr:
        fieldStrNodes = @[f[1][1]]
      of nnkIntLit:
        discard
      else:
        let fAst = f[0].getImpl
        if fAst != nil:
          case fAst.kind
          of nnkStrLit .. nnkTripleStrLit:
            fieldStrNodes = @[fAst]
          of nnkTupleConstr:
            fieldStrNodes = @[fAst[1]]
          else: discard
    else: error("Invalid node for enum type `" & $f.kind & "`!", f)
    let fieldName = $fieldSym
    let mapping = mappingTable.getOrDefault(fieldName, FieldMapping())
    if hasInputNames(mapping):
      for inputName in mapping.input.names:
        fieldStrNodes.add newLit apply(inputName, fieldName)
    elif fieldStrNodes.len == 0:
      fieldStrNodes = @[newLit fieldName]
    var branch = newTree(nnkOfBranch)
    if not isNilAst(normalizer):
      var namesNode = newNimNode(nnkBracket, normalizer)
      for strNode in fieldStrNodes:
        namesNode.add newCall(normalizer, strNode)
      branch.add newCall(bindSym"toUnique", namesNode)
    else:
      branch.add fieldStrNodes
    branch.add newCall(templToCall, newDotExpr(t, fieldSym))
    result.add branch

macro mapEnumFieldOutput*[T: enum](
  t: typedesc[T], v: T,
  mappings: static FieldMappingPairs,
  normalizer: typed,
  templToCall: untyped) =
  ## calls `templToCall` with the mapped field name of `v`
  ## 
  ## if `normalizer` is not `nil`, calls it for both `key` and the generated input names
  # XXX missing default arg because of enum string value #6
  var impl = getTypeInst(v)
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
  if impl.kind != nnkEnumTy:
    error "expected enum type for type impl of " & repr(t), impl
  let mappingTable = toTable(mappings)
  result = newNimNode(nnkCaseStmt, v)
  result.add v
  for f in impl:
    # copied from std/enumutils.genEnumCaseStmt
    var fieldSym, fieldStrNode: NimNode = nil
    case f.kind
    of nnkEmpty: continue # skip first node of `enumTy`
    of nnkSym, nnkIdent, nnkAccQuoted, nnkOpenSymChoice, nnkClosedSymChoice:
      fieldSym = f
    of nnkEnumFieldDef:
      fieldSym = f[0]
      case f[1].kind
      of nnkStrLit .. nnkTripleStrLit:
        fieldStrNode = f[1]
      of nnkTupleConstr:
        fieldStrNode = f[1][1]
      of nnkIntLit:
        discard
      else:
        let fAst = f[0].getImpl
        if fAst != nil:
          case fAst.kind
          of nnkStrLit .. nnkTripleStrLit:
            fieldStrNode = fAst
          of nnkTupleConstr:
            fieldStrNode = fAst[1]
          else: discard
    else: error("Invalid node for enum type `" & $f.kind & "`!", f)
    let fieldName = $fieldSym
    let mapping = mappingTable.getOrDefault(fieldName, FieldMapping())
    if hasOutputName(mapping):
      fieldStrNode = newLit apply(mapping.output.name, fieldName)
    elif fieldStrNode == nil or fieldStrNode.kind notin {nnkStrLit..nnkTripleStrLit}:
      fieldStrNode = newLit fieldName
    fieldStrNode = wrapNormalizer(normalizer, fieldStrNode)
    result.add newTree(nnkOfBranch,
      newDotExpr(t, fieldSym),
      newCall(templToCall, fieldStrNode))
