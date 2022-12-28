theory ImportResolver
  imports
    Main
    Hello_World.IO

    Diagnose.Diagnostic

    Syntax.AST
    Syntax.Digraph
    Syntax.Constraints
    Syntax.Errors
begin

fun bind_sum :: \<open>'a + 'b \<Rightarrow> ('b \<Rightarrow> 'a + 'c) \<Rightarrow> 'a + 'c\<close>
where \<open>bind_sum (Inl x) _ = Inl x\<close>
    | \<open>bind_sum (Inr x) f = f x\<close>
adhoc_overloading bind bind_sum

code_printing
  constant bind_sum \<rightharpoonup> (Haskell) infixl 1 "Prelude.>>="

(***************************************************)

type_synonym registered_files = \<open>String.literal \<rightharpoonup> String.literal\<close>

type_synonym modules = \<open>String.literal \<rightharpoonup> AST.module located\<close>

type_synonym module_order = \<open>String.literal list\<close>

type_synonym import_graph = \<open>String.literal digraph\<close>

datatype module_origin =
  CommandLine
| InSource position

type_synonym mod_list = \<open>(module_origin \<times> String.literal) list\<close>

fun origin_to_position :: \<open>module_origin \<Rightarrow> position option\<close>
where \<open>origin_to_position CommandLine = None\<close>
    | \<open>origin_to_position (InSource pos) = Some pos\<close>

(************************************************)

axiomatization
    parse_module_name :: \<open>position option \<Rightarrow> String.literal \<Rightarrow> String.literal diagnostic + String.literal list\<close>
and mk_constraint_system :: \<open>String.literal list \<Rightarrow> String.literal list \<Rightarrow> system\<close>

fun try_mk_constraints_for_module :: \<open>String.literal list \<Rightarrow> module_origin \<Rightarrow> String.literal \<Rightarrow> (String.literal diagnostic + system)\<close>
where \<open>try_mk_constraints_for_module idirs orig m = do {
         parts \<leftarrow> parse_module_name (origin_to_position orig) m;
         Inr (mk_constraint_system idirs parts)
       }\<close>

code_printing
  constant parse_module_name \<rightharpoonup> (Haskell) "ImportResolver.parseModuleName"
| constant mk_constraint_system \<rightharpoonup> (Haskell) "ImportResolver.mkConstraintSystem"
| code_module ImportResolver \<rightharpoonup> (Haskell) \<open>
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module ImportResolver (Formula (..), Constraint, System, parseModuleName, mkConstraintSystem) where

import Data.Bifunctor (first)
import Data.Functor ((<&>))
import Data.Void (Void)
import Error.Diagnose (Diagnostic, Position, file)
import Error.Diagnose.Compat.Megaparsec (HasHints (..), errorDiagnosticFromBundle)
import System.FilePath (joinPath, (<.>), (</>))
import qualified Text.Megaparsec as MP
import qualified Text.Megaparsec.Char as MPC

data Namespace
  = Module FilePath
  | Access Namespace String
  deriving (Show)

data Formula
  = Top
  | Bottom
  | Exists FilePath
  | In String Namespace
  deriving (Show)

type Constraint = [Formula]

type System = [Constraint]

--------------------------------------------

type MonadParser m = (MP.MonadParsec Void String m)

instance HasHints Void String where
  hints _ = []

parseModuleName :: Maybe Position -> String -> Either (Diagnostic String) [String]
parseModuleName pos modName =
  let fileName = maybe "<command-line>" file pos
   in first
        (errorDiagnosticFromBundle Nothing "Invalid module name" Nothing)
        (MP.runParser parseName fileName modName)

parseName :: MonadParser m => m [String]
parseName = parsePart `MP.sepBy1` parseSeparator
  where
    parsePart = MP.some (MP.noneOf ":\",;=∷")

    parseSeparator = MPC.string "::" MP.<|> MPC.string "∷"

--------------------------------------------

mkConstraintSystem :: [FilePath] -> [String] -> System
mkConstraintSystem idirs mods =
  let paths = generateAllPossiblePaths [] idirs mods
   in uncurry makeConstraint <$> paths
  where
    generateAllPossiblePaths :: [String] -> [FilePath] -> [String] -> [(FilePath, [String])]
    generateAllPossiblePaths _ _ [] = []
    generateAllPossiblePaths acc idirs (m : ms)
      | all isValidName acc && isValidName m =
          let local = idirs <&> \dir -> (dir </> joinPath acc </> m <.> "zc", ms)
              xs = generateAllPossiblePaths (acc <> [m]) idirs ms
           in local <> xs
      | otherwise = generateAllPossiblePaths (acc <> [m]) idirs ms

    makeConstraint :: FilePath -> [String] -> Constraint
    makeConstraint file fields =
      let fieldFormulae = mkAccesses (Module file) fields
       in Exists file : fieldFormulae

    mkAccesses :: Namespace -> [String] -> [Formula]
    mkAccesses _ [] = []
    mkAccesses ns (f : fs) = In f ns : mkAccesses (Access ns f) fs

    isValidName :: String -> Bool
    isValidName = not . any fsReserved
    {-# INLINEABLE isValidName #-}

    fsReserved :: Char -> Bool
    fsReserved '/' = True
    fsReserved '\\' = True
    fsReserved ':' = True
    fsReserved '"' = True
    fsReserved ';' = True
    fsReserved _ = False
\<close>

code_reserved Haskell ImportResolver parseModuleName mkConstraintSystem

(***********************************************)

(* TODO: We will need to check for cycles every time we insert a new module in the import graph.
 *       In case we do not, we will not be able to parse and resolve modules which mutually export each other
 *       (the function infinitely will loop for this corner case).
 *
 *       By checking that no cycle occurs at each step, we will be able to fail early while generating
 *       the namespace of our current module.
 * *)
(* TODO: add the imports of the new module to be processed (if not already processed) *)

fun make_initial_constraint_system :: \<open>String.literal list \<Rightarrow> mod_list \<Rightarrow> (String.literal diagnostic + global_system)\<close>
where \<open>make_initial_constraint_system _ [] = Inr []\<close>
    | \<open>make_initial_constraint_system idirs ((orig, m) # ms) = do {
         csts \<leftarrow> try_mk_constraints_for_module idirs orig m;
         sys \<leftarrow> make_initial_constraint_system idirs ms;
         Inr (csts # sys)
       }\<close>

fun try_solve_system_incrementally :: \<open>import_graph \<Rightarrow> global_system \<Rightarrow> mod_list \<Rightarrow> ((String.literal diagnostic + modules) \<times> import_graph \<times> registered_files \<times> mod_list) io\<close>
where \<open>try_solve_system_incrementally g [] [] = IO.return (Inr Map.empty, g, Map.empty, [])\<close>
      (* Erroneous cases: module import has no associated constraint *)
    | \<open>try_solve_system_incrementally g ([] # _) ((CommandLine, m) # ms) =
         IO.return (Inl (mk_cannot_import_cli_module_error m), g, Map.empty, (CommandLine, m) # ms)\<close>
    | \<open>try_solve_system_incrementally g ([] # _) ((InSource p, m) # ms) =
         IO.return undefined\<close>
      (* Still at least one constraint to solve *)
    | \<open>try_solve_system_incrementally g (c # cs) ((orig, m) # ms) = do {
         IO.return undefined
       }\<close>
      (* Inconsistent state: more constraints than modules, or more modules than constraints *)
    | \<open>try_solve_system_incrementally _ _ _ = undefined\<close>

fun parse_and_resolve_modules :: \<open>String.literal list \<Rightarrow> String.literal list \<Rightarrow> ((String.literal diagnostic + modules \<times> module_order) \<times> registered_files) io\<close>
where \<open>parse_and_resolve_modules idirs mods = do {
         let mods' = map (Pair CommandLine) mods;
         let sys = make_initial_constraint_system idirs mods';
         case sys of
           Inl diag \<Rightarrow> IO.return (Inl diag, Map.empty)
         | Inr sys \<Rightarrow> do {
             (res, g, files, _) \<leftarrow> try_solve_system_incrementally Digraph.empty sys mods';
             let res = do {
                   mods \<leftarrow> res;
                   map_sum undefined (Pair mods) (topsort g)
                 };
             IO.return (res, files)
           }
       }\<close>

hide_type module_origin
hide_const CommandLine InSource

(* Prevent using \<open>bind_sum\<close> outside this theory. *)
hide_const bind_sum

end
