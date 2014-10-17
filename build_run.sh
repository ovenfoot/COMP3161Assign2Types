#!/bin/bash
cabal build

./run_tests.sh --no-colour >runtestoutput.txt
./dist/build/minhs-2/minhs-2 tests/main_tests/1_primops/primops/003.mhs