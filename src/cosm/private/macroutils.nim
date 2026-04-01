import std/macros

proc realBasename*(n: NimNode): string =
  var n = n
  if n.kind == nnkPragmaExpr: n = n[0]
  if n.kind == nnkPostfix: n = n[^1]
  result = $n
