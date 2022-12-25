#!/usr/bin/env bash
set -e

# This will regenerate all the necessary code in the `generated/` top folder.
isabelle build -D . -j$(nproc) EntryPoint

# Finally, patch the generated Haskell code to include our parser, etc.
cd generated
patch < EntryPoint.patch
