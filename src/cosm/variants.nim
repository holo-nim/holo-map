import std/[macros, tables], private/macroutils

type
  VariantType* = (object | ref object)
  VariantBranch* = object
    values*: seq[NimNode]
    fields*: seq[string] # XXX nested variants not supported
  VariantInfo* = object
    discrimName*: string
    branches*: seq[VariantBranch]
    fieldsToBranch*: Table[string, int] # index in branches seq
  ObjectVariantInfos* = object
    variants*: seq[VariantInfo]

proc isElse*(branch: VariantBranch): bool =
  branch.values.len == 0

proc skipToFirstValue(val: NimNode): NimNode =
  case val.kind
  of nnkBracket, nnkCurly:
    result = val[0]
  of nnkRange:
    result = val[0]
  of nnkCallKinds:
    if val.len > 1 and val[0].eqIdent"..":
      result = val[1]
    else:
      result = val
  else:
    result = val

proc firstValue*(branch: VariantBranch): NimNode =
  if branch.isElse:
    result = nil
  else:
    result = skipToFirstValue(branch.values[0])

proc hasVariants*(variants: ObjectVariantInfos): bool =
  variants.variants.len != 0

proc iterVariantBranch(branch: var VariantBranch, list: NimNode) =
  case list.kind
  of nnkRecList, nnkTupleTy:
    for r in list:
      iterVariantBranch(branch, r)
  of nnkRecCase:
    # XXX nested variants not supported
    error("nested object variant not supported", list)
  of nnkRecWhen:
    for bi in 0 ..< list.len:
      expectKind list[bi], {nnkElifBranch, nnkElse}
      iterVariantBranch(branch, list[bi][^1])
  of nnkIdentDefs:
    for i in 0 ..< list.len - 2:
      let name = realBasename(list[i])
      block doAdd:
        for existing in branch.fields.mitems:
          if existing == name:
            break doAdd
        branch.fields.add name
  of nnkSym:
    let name = $list
    branch.fields.add name
  of nnkDiscardStmt, nnkNilLit, nnkEmpty: discard
  else:
    error "unknown object field AST kind " & $list.kind, list

proc buildVariantInfo*(variant: NimNode): VariantInfo =
  assert variant.kind == nnkRecCase
  expectKind variant[0], nnkIdentDefs
  expectLen variant[0], 3
  result = VariantInfo(discrimName: realBasename(variant[0][0]))
  for i in 1 ..< variant.len:
    let branchNode = variant[i]
    let last = branchNode.len - 1
    var branch = VariantBranch(values: @[])
    if branchNode.kind == nnkOfBranch:
      for j in 0 ..< last:
        branch.values.add branchNode[j]
    iterVariantBranch(branch, branchNode[last])
    let index = result.branches.len
    result.branches.add branch
    for field in branch.fields:
      # don't override first found branch?
      discard result.fieldsToBranch.mgetOrPut(field, index)

proc buildFirstVariant*(variant: var VariantInfo, list: NimNode): bool =
  case list.kind
  of nnkRecList, nnkTupleTy:
    for r in list:
      if buildFirstVariant(variant, r): return true
  of nnkRecCase:
    variant = buildVariantInfo(list)
    return true
  of nnkRecWhen:
    for bi in 0 ..< list.len:
      expectKind list[bi], {nnkElifBranch, nnkElse}
      if buildFirstVariant(variant, list[bi][^1]): return true
  of nnkIdentDefs:
    discard
  of nnkSym:
    discard
  of nnkDiscardStmt, nnkNilLit, nnkEmpty: discard
  else:
    error "unknown object field AST kind " & $list.kind, list

proc buildVariants*(obj: NimNode): ObjectVariantInfos =
  result = ObjectVariantInfos()
  var t = obj
  while t != nil:
    # very horribly try to copy macros.customPragma:
    var impl = getTypeImpl(t)
    while true:
      if impl.kind in {nnkRefTy, nnkPtrTy, nnkVarTy, nnkOutTy}:
        if impl[^1].kind == nnkObjectTy:
          impl = impl[^1]
        else:
          impl = getTypeImpl(impl[^1])
      elif impl.kind == nnkBracketExpr and impl[0].eqIdent"typeDesc":
        impl = getTypeImpl(impl[1])
      elif impl.kind == nnkBracketExpr and impl[0].kind == nnkSym:
        impl = getImpl(impl[0])[^1]
      elif impl.kind == nnkSym:
        impl = getImpl(impl)[^1]
      else:
        break
    case impl.kind
    of nnkObjectTy:
      var variant: VariantInfo
      if buildFirstVariant(variant, impl[^1]):
        # XXX multiple object variants not supported
        result.variants = @[variant]
        return
      t = nil
      if impl[1].kind != nnkEmpty:
        expectKind impl[1], nnkOfInherit
        t = impl[1][0]
    else:
      error "got unknown object type kind " & $impl.kind, impl

macro hasVariants*[T: VariantType](t: type T): bool =
  let val = buildVariants(t)
  result = newLit(val.variants.len != 0)

macro withFirstVariantFieldName*[T: VariantType](obj: typedesc[T], templToCall: untyped) =
  ## calls `templToCall` with the identifier of the first variant discriminator field of `obj`
  let info = buildVariants(obj)
  if info.variants.len == 0:
    error("object has no variants", obj)
  else:
    result = newCall(templToCall, ident info.variants[0].discrimName)

macro withFirstVariantField*[T: VariantType](obj: T, templToCall: untyped) =
  ## calls `templToCall` with the address of the first variant discriminator field of `obj`
  let info = buildVariants(obj)
  if info.variants.len == 0:
    error("object has no variants", obj)
  else:
    result = newCall(templToCall, newDotExpr(obj, ident info.variants[0].discrimName))
