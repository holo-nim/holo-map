import std/macros

type MappingGroup* = object
  ## info to describe specific formats at compile time
  id*: string
    ## string identifier for the format
    ## empty allows everything
  mimeType*: string
  parents*: seq[MappingGroup]
    ## groups that this group is a "subset" of, does not need an effective meaning other than for filters
    ## in the future might be replaced with imperative declarations (i.e. `declareSubset(HoloJson, Json)`)
    ## but this might require using `macrocache` or other unstable nim features

const AnyMappingGroup* = MappingGroup(id: "")
  ## matches any mapping group without having to be declared as parent

proc `<=`*(a, b: MappingGroup): bool =
  ## returns true if `a` is a subset of `b`
  if b.id == AnyMappingGroup.id:
    result = true
  elif a.id == b.id:
    result = true
  else:
    result = false
    for ap in a.parents:
      if ap <= b:
        return true

proc getMappingGroupFromLiteral*(obj: NimNode): MappingGroup =
  expectKind obj, nnkObjConstr
  result = MappingGroup()
  for i in 1 ..< obj.len:
    expectKind obj[i], nnkExprColonExpr
    let fieldName = $obj[i][0]
    let val = obj[i][1]
    case fieldName
    of "id":
      expectKind val, {nnkStrLit..nnkTripleStrLit}
      result.id = val.strVal
    of "mimeType":
      expectKind val, {nnkStrLit..nnkTripleStrLit}
      result.mimeType = val.strVal
    of "parents":
      expectKind val, nnkBracket
      result.parents.newSeq(val.len)
      for i in 0 ..< val.len:
        result.parents[i] = getMappingGroupFromLiteral(val[i])
    else:
      warning("unknown field in mapping group literal: " & fieldName, obj[i])

# common formats, won't be needed if imperative declarations are implemented
const Json* = MappingGroup(id: "json", mimeType: "application/json", parents: @[])
