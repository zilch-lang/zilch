#!/usr/bin/env bash

CWD=$(pwd)
DEMANGLE_GHCI=$(find $CWD -name 'demangle.ghci' -print -quit)

stack ghci --ghci-options="-ghci-script $DEMANGLE_GHCI" --no-load
