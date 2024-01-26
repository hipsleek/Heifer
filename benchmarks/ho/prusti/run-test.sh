#!/bin/bash

export PRINT_DESUGARED_SPECS=true
export PRUSTI_DUMP_VIPER_PROGRAM=true
export PRUSTI_LOG=debug
export CHECK_TIMEOUT=20

PRUSTI_USE_MORE_COMPLETE_EXHALE=false prusti-rustc --edition=2018 "$1" --verbose
