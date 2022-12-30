theory ImportResolver
  imports
    Main
    Hello_World.IO

    Diagnose.Diagnostic

    Syntax.AST
    Syntax.Digraph
    Syntax.Constraints
    Syntax.Errors
    Syntax.FileIO
    Syntax.Lexer
    Syntax.Parser
    Syntax.Desugarer
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

type_synonym mod_list = \<open>(module_origin \<times> String.literal list) list\<close>

fun origin_to_position :: \<open>module_origin \<Rightarrow> position option\<close>
where \<open>origin_to_position CommandLine = None\<close>
    | \<open>origin_to_position (InSource pos) = Some pos\<close>

fun pos_or :: \<open>module_origin \<Rightarrow> 'a \<Rightarrow> position + 'a\<close>
where \<open>pos_or CommandLine x = Inr x\<close>
    | \<open>pos_or (InSource p) _ = Inl p\<close>

datatype interface =
  Iface \<open>String.literal \<rightharpoonup> interface\<close>

type_synonym namespaces = \<open>String.literal \<rightharpoonup> interface option\<close>

type_synonym global_state = \<open>system list \<times> mod_list \<times> namespaces \<times> modules \<times> import_graph\<close>

type_synonym 'a resolver = \<open>[global_state, registered_files] \<Rightarrow> ((String.literal diagnostic + global_state \<times> 'a) \<times> registered_files) io\<close>

fun bind_resolver :: \<open>'a resolver \<Rightarrow> ('a \<Rightarrow> 'b resolver) \<Rightarrow> 'b resolver\<close>
where \<open>bind_resolver r f st fs = do {
         (res, fs) \<leftarrow> r st fs;
         case res of
           Inl diag \<Rightarrow> IO.return (Inl diag, fs)
         | Inr (st, x) \<Rightarrow> f x st fs
       }\<close>
adhoc_overloading bind bind_resolver

definition return :: \<open>'a \<Rightarrow> 'a resolver\<close>
where \<open>return x st fs = IO.return (Inr (st, x), fs)\<close>

definition throw :: \<open>String.literal diagnostic \<Rightarrow> 'a resolver\<close>
where \<open>throw diag _ fs = IO.return (Inl diag, fs)\<close>

definition append_system :: \<open>system \<Rightarrow> unit resolver\<close>
where \<open>append_system s \<equiv> (\<lambda>(ss, ml, ns, ms, g) fs. IO.return (Inr ((s # ss, ml, ns, ms, g), ()), fs))\<close>

definition set_system :: \<open>[nat, system] \<Rightarrow> unit resolver\<close>
where \<open>set_system n s = (\<lambda>(ss, ml, ns, ms, g) fs. IO.return (Inr ((ss[n := s], ml, ns, ms, g), ()), fs))\<close>

definition insert_interface :: \<open>[String.literal, interface option] \<Rightarrow> unit resolver\<close>
where \<open>insert_interface name iface \<equiv> (\<lambda>(ss, ml, ns, ms, g) fs. IO.return (Inr ((ss, ml, ns(name \<mapsto> iface), ms, g), ()), fs))\<close>

definition insert_module :: \<open>[String.literal, AST.module located] \<Rightarrow> unit resolver\<close>
where \<open>insert_module name m \<equiv> (\<lambda>(ss, ml, ns, ms, g) fs. IO.return (Inr ((ss, ml, ns, ms(name \<mapsto> m), g), ()), fs))\<close>

definition register_module :: \<open>[String.literal list, module_origin] \<Rightarrow> unit resolver\<close>
where \<open>register_module m orig \<equiv> (\<lambda>(ss, ml, ns, ms, g) fs. IO.return (Inr ((ss, (orig, m) # ml, ns, ms, g), ()), fs))\<close>

definition insert_dependency :: \<open>[String.literal, String.literal] \<Rightarrow> unit resolver\<close>
where \<open>insert_dependency a b \<equiv> (\<lambda>(ss, ml, ns, ms, g) fs. IO.return (Inr ((ss, ml, ns, ms, add_edge (a, b) g), ()), fs))\<close>

definition get :: \<open>global_state resolver\<close>
where \<open>get \<equiv> (\<lambda>st fs. IO.return (Inr (st, st), fs))\<close>

definition lift_io :: \<open>'a io \<Rightarrow> 'a resolver\<close>
where \<open>lift_io act \<equiv> (\<lambda>st fs. do { x \<leftarrow> act; IO.return (Inr (st, x), fs) })\<close>

definition lift_sum :: \<open>String.literal diagnostic + 'a \<Rightarrow> 'a resolver\<close>
where \<open>lift_sum res \<equiv> (\<lambda>st fs. IO.return (map_sum id (Pair st) res, fs))\<close>

fun contains :: \<open>String.literal \<Rightarrow> interface \<Rightarrow> bool\<close>
where \<open>contains x (Iface binds) = (binds x \<noteq> None)\<close>

(************************************************)

axiomatization
    parse_module_name :: \<open>position option \<Rightarrow> String.literal \<Rightarrow> String.literal diagnostic + String.literal list\<close>
and mk_constraint_system :: \<open>String.literal list \<Rightarrow> String.literal list \<Rightarrow> system\<close>

fun try_mk_constraints_for_module :: \<open>String.literal list \<Rightarrow> module_origin \<Rightarrow> String.literal \<Rightarrow> (String.literal diagnostic + system \<times> String.literal list)\<close>
where \<open>try_mk_constraints_for_module idirs orig m = do {
         parts \<leftarrow> parse_module_name (origin_to_position orig) m;
         Inr (mk_constraint_system idirs parts, parts)
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

module ImportResolver (Formula (..), Namespace (..), Constraint, System, parseModuleName, mkConstraintSystem) where

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
  = Top Formula
  | Bottom Formula
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

fun make_initial_constraint_system :: \<open>[String.literal list, (module_origin \<times> String.literal) list] \<Rightarrow> (String.literal diagnostic + system list \<times> mod_list)\<close>
where \<open>make_initial_constraint_system _ [] = Inr ([], [])\<close>
    | \<open>make_initial_constraint_system idirs ((orig, m) # ms) = do {
         (csts, m) \<leftarrow> try_mk_constraints_for_module idirs orig m;
         (sys, ms) \<leftarrow> make_initial_constraint_system idirs ms;
         Inr (csts # sys, (orig, m) # ms)
       }\<close>

fun find_unsolved_system :: \<open>unit \<Rightarrow> ((nat \<times> system) option) resolver\<close>
where \<open>find_unsolved_system () = do {
         (ss, _, _, _, _) \<leftarrow> get;
         case [(i, s) \<leftarrow> enumerate 0 ss. \<not> is_fully_solved s] of
           [] \<Rightarrow> return None
         | c # _ \<Rightarrow> return (Some c)
       }\<close>

text \<open>
  Returns a two-level \<open>option\<close> :
  \<^item> The first \<open>option\<close> level tells whether the interface has been generated, or if it is
    held back by additional constraints;
  \<^item> The second \<open>option\<close> level tells whether an access could be performed within the generated interface.
    For example, imagine that you need to check that \<open>x \<in> (MOD f)∷y\<close>, but \<open>MOD f\<close> does not contain \<open>y\<close>.
    Then \<open>Some None\<close> will be returned.
\<close>
fun try_generate_interface :: \<open>namespace \<Rightarrow> (interface option option \<times> nat) resolver\<close>
where \<open>try_generate_interface _ = undefined\<close>

fun try_solve_constraint :: \<open>constraint \<Rightarrow> (constraint \<times> nat) resolver\<close>
where \<open>try_solve_constraint [] = return ([], 0)\<close>
    | \<open>try_solve_constraint (Top f # fs) = do {
         (fs, n) \<leftarrow> try_solve_constraint fs;
         return (Top f # fs, n)
       }\<close>
    | \<open>try_solve_constraint (Bottom f # fs) = do {
         (fs, n) \<leftarrow> try_solve_constraint fs;
         return (Bottom f # fs, n)
       }\<close>
    | \<open>try_solve_constraint (Exists path # fs) = do {
         file_exists \<leftarrow> lift_io (does_file_exist path);
         if file_exists
           then do {
             (_, _, ms, _) \<leftarrow> get;
             (case ms path of
               None \<Rightarrow> do {
                 content \<leftarrow> lift_io (read_file path);
                 (tokens, _) \<leftarrow> lift_sum (run_lexer path content);
                 (cst, _) \<leftarrow> lift_sum (run_parser path tokens);
                 (ast, _) \<leftarrow> lift_sum (run_desugarer cst);
                 insert_module path ast
               }
             | Some _ \<Rightarrow> return ());
             (fs, n) \<leftarrow> try_solve_constraint fs;
             return (Top (Exists path) # fs, n)
           }
           else return (Bottom (Exists path) # fs, 0)
        }\<close>
     | \<open>try_solve_constraint (In x n # fs) = do {
          (iface, i) \<leftarrow> try_generate_interface n;
          case iface of
            None \<Rightarrow> return (In x n # fs, i)
          | Some None \<Rightarrow> return (Bottom (In x n) # fs, i)
          | Some (Some iface) \<Rightarrow>
              if contains x iface
                then do {
                  (fs, k) \<leftarrow> try_solve_constraint fs;
                  return (Top (In x n) # fs, i + k)
                }
                else return (Bottom (In x n) # fs, i)
        }\<close>

fun try_solve_each_constraint :: \<open>system \<Rightarrow> (system \<times> nat) resolver\<close>
where \<open>try_solve_each_constraint [] = return ([], 0)\<close>
    | \<open>try_solve_each_constraint (c # cs) = do {
         (c, i) \<leftarrow> if is_solved c then return (c, 0) else try_solve_constraint c;
         (cs, n) \<leftarrow> try_solve_each_constraint cs;
         return (c # cs, i + n)
       }\<close>

fun try_solve_system :: \<open>[nat, system] \<Rightarrow> unit resolver\<close>
where \<open>try_solve_system i s = do {
         (cs, n) \<leftarrow> try_solve_each_constraint s;
         set_system (i + n) cs
       }\<close>

function try_solve_systems_incrementally :: \<open>unit \<Rightarrow> unit resolver\<close>
where \<open>try_solve_systems_incrementally _ = do {
         sys \<leftarrow> find_unsolved_system ();
         case sys of
           None \<Rightarrow> return ()
         | Some (i, s) \<Rightarrow> try_solve_system i s \<bind> try_solve_systems_incrementally
       }\<close>
by pat_completeness auto

termination try_solve_systems_incrementally
  sorry
(* NOTE: need to prove termination for \<open>try_solve_systems_incrementally\<close> to get code equations *)

fun check_all_systems :: \<open>system list \<Rightarrow> mod_list \<Rightarrow> unit resolver\<close>
where \<open>check_all_systems [] _ = return ()\<close>
    | \<open>check_all_systems (s # ss) ((orig, m) # ms) =
         (case [c \<leftarrow> s. is_true c] of
           [] \<Rightarrow> throw (mk_cannot_resolve_import_error (pos_or orig m) (map (the \<circ> only_false_constraint) s))
         | (a # b # cs) \<Rightarrow> throw undefined
         | [_] \<Rightarrow> check_all_systems ss ms)\<close>
    (* Inconsistent state: all systems must have an associated module *)
    | \<open>check_all_systems _ _ = undefined\<close>
(* TODO: fetch the position of the import associated to this system.
         also fetch the name of the import if it is a CLI import (i.e. no position).

         \<open>mk_cannot_resolve_import_error\<close> must take a \<open>String.literal + position\<close> as argument. *)

fun check_final_systems :: \<open>unit \<Rightarrow> unit resolver\<close>
where \<open>check_final_systems () = do {
         (ss, ml, _, _, _) \<leftarrow> get;
         check_all_systems ss ml
       }\<close>

fun parse_and_resolve_modules :: \<open>[String.literal list, String.literal list] \<Rightarrow> ((String.literal diagnostic + modules \<times> module_order) \<times> registered_files) io\<close>
where \<open>parse_and_resolve_modules idirs mods = do {
         let mods = map (Pair CommandLine) mods;
         let sys = make_initial_constraint_system idirs mods;
         case sys of
           Inl diag \<Rightarrow> IO.return (Inl diag, Map.empty)
         | Inr (sys, mods) \<Rightarrow> do {
             (res, files) \<leftarrow> (do {
               try_solve_systems_incrementally ();
               check_final_systems ()
             }) (sys, mods, Map.empty, Map.empty, Digraph.empty) Map.empty;
             let res = do {
                   ((_, _, _, mods, g), ()) \<leftarrow> res;
                   map_sum undefined (Pair mods) (topsort g)
                 };
             IO.return (res, files)
           }
       }\<close>

hide_type module_origin
hide_const CommandLine InSource

(* Prevent using \<open>bind_sum\<close> outside this theory. *)
hide_const bind_sum bind_resolver return

end
