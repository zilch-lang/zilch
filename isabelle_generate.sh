#!/usr/bin/env bash

# This will regenerate all the necessary code in the `generated/` top folder.
isabelle build -D . -j$(nproc) EntryPoint
