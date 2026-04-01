import ./[groups, caseutils]

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

proc toFieldMapping*(input: InputFieldMapping): FieldMapping {.inline.} =
  ## hook called on the argument to the `mapping` pragma to convert it to a full field option object
  FieldMapping(input: input)

proc toFieldMapping*(output: OutputFieldMapping): FieldMapping {.inline.} =
  ## hook called on the argument to the `mapping` pragma to convert it to a full field option object
  FieldMapping(output: output)

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
    # XXX maybe use NimNode for name too to make use of eqIdent performance
  HasFieldMappings* = concept
    ## implement to override mappings for a type
    proc getFieldMappings(obj: typedesc[Self], group: static MappingGroup): FieldMappingPairs
