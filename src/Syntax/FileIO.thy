theory FileIO
  imports
    Main
    Hello_World.IO
begin

axiomatization
    does_file_exist :: \<open>String.literal \<Rightarrow> bool io\<close>
and read_file :: \<open>String.literal \<Rightarrow> String.literal io\<close>

code_printing
  constant does_file_exist \<rightharpoonup> (Haskell) "FileIO.doesFileExist"
| constant read_file \<rightharpoonup> (Haskell) "FileIO.readFile"

| code_module FileIO \<rightharpoonup> (Haskell) \<open>
{-# LANGUAGE NoImplicitPrelude #-}
module FileIO (module Export) where

import Prelude as Export (readFile)
import System.Directory as Export (doesFileExist)
\<close>

end
