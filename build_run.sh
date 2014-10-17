#!/bin/bash
cabal build

./run_tests.sh --no-colour >runtestoutput.txt
./dist/build/minhs-2/minhs-2 tests/main_tests/5_let/0_simple/000.mhs