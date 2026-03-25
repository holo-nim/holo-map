# Package

version       = "0.1.0"
author        = "metagn"
description   = "generalized mappings between types, i.e. serialization, parsing, conversions"
license       = "MIT"
srcDir        = "src"


# Dependencies

requires "nim >= 1.6.0"

task docs, "build docs for all modules":
  exec "nim r ci/build_docs.nim"

task tests, "run tests for multiple backends and defines":
  exec "nim r ci/run_tests.nim"
