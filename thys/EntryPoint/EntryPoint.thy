theory EntryPoint
  imports
    Main
    Parser.Lexer
    Parser.Parser
    Parser.CST
    ExternalLibrary.Located
    ExternalLibrary.Diagnose
    Hello_World.IO
begin

axiomatization
  does_file_exist :: \<open>String.literal \<Rightarrow> bool io\<close> and 
  read_file :: \<open>String.literal \<Rightarrow> String.literal io\<close>

definition entry_point :: \<open>String.literal \<Rightarrow> (String.literal diagnostic + CST.module located) io\<close> where
  \<open>entry_point path \<equiv> do {
    file_exists \<leftarrow> does_file_exist path;
    case file_exists of
      True \<Rightarrow> do {
        file_content \<leftarrow> read_file path;
        case run_lexer path file_content of
          Inl diag \<Rightarrow> IO.return (Inl (add_file diag path file_content)) 
        | Inr (tokens, warns1) \<Rightarrow> do {
            case run_parser path tokens of
              Inl diag \<Rightarrow> IO.return (Inl (add_file diag path file_content))
            | Inr (cst, warns2) \<Rightarrow> IO.return (Inr cst)
          }
      }
    | False \<Rightarrow> IO.return undefined 
  }\<close> 

section \<open>Additional code generator setup\<close>

text \<open>
  We need some basic file handling primitives in the IO monad.
\<close>

code_printing
  code_module FileIO \<rightharpoonup> (Haskell) \<open>
{-# LANGUAGE NoImplicitPrelude #-}

module FileIO (module Export) where

import Prelude as Export (readFile)
import System.Directory as Export (doesFileExist)
\<close>

code_printing
  constant does_file_exist \<rightharpoonup> (Haskell) "FileIO.doesFileExist"
| constant read_file \<rightharpoonup> (Haskell) "FileIO.readFile"

text \<open>
  Anonymous sum types are not setup to be serialized to Haskell's \<open>Either\<close> type.
  We introduce this notation so that it conforms to the Haskell part of our code base.
\<close> 

code_printing
  type_constructor sum \<rightharpoonup> (Haskell) "Prelude.Either _ _" 
| constant Inl \<rightharpoonup> (Haskell) "Prelude.Left"
| constant Inr \<rightharpoonup> (Haskell) "Prelude.Right"

end