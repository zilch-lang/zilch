#!/usr/bin/env bash

set -e

if [ "$1" == "-c" ]; then
  shift
  CLEAN_BUILD="-c"
else
  CLEAN_BUILD=""
fi

./patch-isabelle-symbols.sh
./isabelle-generate.sh $CLEAN_BUILD
stack run -- "$@"
