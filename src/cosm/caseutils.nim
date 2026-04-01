import std/strutils

proc toSnakeCase*(s: string): string =
  # originally written by treeform in jsony https://github.com/treeform/jsony
  if s.len == 0:
    return
  var prevCap = false
  for i, c in s:
    if c in {'A'..'Z'}:
      if i == 0:
        result.add c
      else:
        if result[result.len-1] != '_' and not prevCap:
          result.add '_'
        result.add c.toLowerAscii()
      prevCap = true
    else:
      prevCap = false
      result.add c
