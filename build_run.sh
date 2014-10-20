#!/bin/bash
cabal build

./run_tests.sh --no-colour >runtestoutput.txt
./dist/build/minhs-2/minhs-2 tests/main_tests/8_sums/0_left/0.mhs 