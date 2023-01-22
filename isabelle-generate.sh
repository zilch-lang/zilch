#!/usr/bin/env bash
set -e

# This will regenerate all the necessary code in the `generated/` top folder.
isabelle build -D . -j$(nproc) "$@" EntryPoint

# Finally, patch the generated Haskell code to include our parser, etc.
# Edit the generated file using `ed` to add some of our stuff in here.
ed generated/EntryPoint.hs <generated/EntryPoint_patch.ed
