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

type_synonym registered_files = \<open>String.literal list \<times> (String.literal \<rightharpoonup> String.literal)\<close>

fun union_files :: \<open>[registered_files, registered_files] \<Rightarrow> registered_files\<close> (infixl \<open>U\<close> 30)
where \<open>union_files (l1, m1) (l2, m2) = (List.remdups (l1 @ l2), m1 ++ m2)\<close>

definition no_files :: \<open>registered_files\<close>
where \<open>no_files = ([], Map.empty)\<close>

text \<open>
  File system path to parsed CST, to prevent reparsing files we have parsed before.
\<close>
type_synonym modules = \<open>String.literal \<rightharpoonup> CST.module located\<close>

type_synonym module_order = \<open>String.literal list list\<close>

type_synonym import_graph = \<open>String.literal list digraph\<close>

datatype module_origin =
  CommandLine
| InSource position

text \<open>
  All module names (and their origin) that we know of.
\<close>
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

type_synonym 'a resolver = \<open>global_state \<Rightarrow> ((String.literal diagnostic + global_state \<times> 'a) \<times> registered_files) io\<close>

fun bind_resolver :: \<open>'a resolver \<Rightarrow> ('a \<Rightarrow> 'b resolver) \<Rightarrow> 'b resolver\<close>
where \<open>bind_resolver r f st = do {
         (res, fs1) \<leftarrow> r st;
         case res of
           Inl diag \<Rightarrow> IO.return (Inl diag, fs1)
         | Inr (st, x) \<Rightarrow> do {
             (res, fs2) \<leftarrow> f x st;
             IO.return (res, fs1 U fs2)
           }
       }\<close>
adhoc_overloading bind bind_resolver

definition return :: \<open>'a \<Rightarrow> 'a resolver\<close>
where \<open>return x st = IO.return (Inr (st, x), no_files)\<close>

definition throw :: \<open>String.literal diagnostic \<Rightarrow> 'a resolver\<close>
where \<open>throw diag _ = IO.return (Inl diag, no_files)\<close>

definition prepend_system :: \<open>system \<Rightarrow> unit resolver\<close>
where \<open>prepend_system s \<equiv> (\<lambda>(ss, ml, ns, ms, g). IO.return (Inr ((s # ss, ml, ns, ms, g), ()), no_files))\<close>

definition set_system :: \<open>[nat, system] \<Rightarrow> unit resolver\<close>
where \<open>set_system n s = (\<lambda>(ss, ml, ns, ms, g). IO.return (Inr ((ss[n := s], ml, ns, ms, g), ()), no_files))\<close>

definition insert_interface :: \<open>[String.literal, interface option] \<Rightarrow> unit resolver\<close>
where \<open>insert_interface name iface \<equiv> (\<lambda>(ss, ml, ns, ms, g). IO.return (Inr ((ss, ml, ns(name \<mapsto> iface), ms, g), ()), no_files))\<close>

definition insert_module :: \<open>[String.literal, CST.module located] \<Rightarrow> unit resolver\<close>
where \<open>insert_module name m \<equiv> (\<lambda>(ss, ml, ns, ms, g). IO.return (Inr ((ss, ml, ns, ms(name \<mapsto> m), g), ()), no_files))\<close>

definition register_module :: \<open>[String.literal list, module_origin] \<Rightarrow> unit resolver\<close>
where \<open>register_module m orig \<equiv> (\<lambda>(ss, ml, ns, ms, g). IO.return (Inr ((ss, (orig, m) # ml, ns, ms, g), ()), no_files))\<close>

definition insert_dependency :: \<open>[String.literal list, String.literal list] \<Rightarrow> unit resolver\<close>
where \<open>insert_dependency a b \<equiv> (\<lambda>(ss, ml, ns, ms, g). IO.return (Inr ((ss, ml, ns, ms, add_edge (a, b) g), ()), no_files))\<close>

definition insert_file :: \<open>[String.literal, String.literal] \<Rightarrow> unit resolver\<close>
where \<open>insert_file name content \<equiv> (\<lambda>st. IO.return (Inr (st, ()), ([name], Map.empty(name \<mapsto> content))))\<close>

definition get :: \<open>global_state resolver\<close>
where \<open>get \<equiv> (\<lambda>st. IO.return (Inr (st, st), no_files))\<close>

definition lift_io :: \<open>'a io \<Rightarrow> 'a resolver\<close>
where \<open>lift_io act \<equiv> (\<lambda>st. do { x \<leftarrow> act; IO.return (Inr (st, x), no_files) })\<close>

definition lift_sum :: \<open>String.literal diagnostic + 'a \<Rightarrow> 'a resolver\<close>
where \<open>lift_sum res \<equiv> (\<lambda>st. IO.return (map_sum id (Pair st) res, no_files))\<close>

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

fun insert_dependencies_and_constraints :: \<open>[String.literal list, String.literal list located list, String.literal list] \<Rightarrow> nat resolver\<close>
where \<open>insert_dependencies_and_constraints _ [] _ = return 0\<close>
    | \<open>insert_dependencies_and_constraints idirs ((i @@ p) # is) m = do {
         (_, _, _, _, g) \<leftarrow> get;
         k \<leftarrow> (if i \<in> vertices g
              then return 0
              else do {
                insert_dependency m i;
                prepend_system (mk_constraint_system idirs i);
                return 1
              });
         n \<leftarrow> insert_dependencies_and_constraints idirs is m;
         return (k + n)
       }\<close>

fun try_solve_constraint :: \<open>[String.literal list, String.literal list, constraint] \<Rightarrow> (constraint \<times> nat) resolver\<close>
where \<open>try_solve_constraint _ _ [] = return ([], 0)\<close>
    | \<open>try_solve_constraint idirs m (Top f # fs) = do {
         (fs, n) \<leftarrow> try_solve_constraint idirs m fs;
         return (Top f # fs, n)
       }\<close>
    | \<open>try_solve_constraint _ m (Bottom f # fs) = return (Bottom f # fs, 0)\<close>
    | \<open>try_solve_constraint idirs m (Exists path # fs) = do {
         file_exists \<leftarrow> lift_io (does_file_exist path);
         if file_exists
           then do {
             (_, _, ms, _) \<leftarrow> get;
             i \<leftarrow> case ms path of
                   None \<Rightarrow> do {
                     content \<leftarrow> lift_io (read_file path);
                     insert_file path content;
                     (tokens, _) \<leftarrow> lift_sum (run_lexer path content);
                     (cst, _) \<leftarrow> lift_sum (run_parser path tokens);
                     let flattened_imports = extract_imports cst;
                     i \<leftarrow> insert_dependencies_and_constraints idirs flattened_imports m;
                     insert_module path cst;
                     return i
                   }
                 | Some _ \<Rightarrow> return 0;
             (fs, n) \<leftarrow> try_solve_constraint idirs m fs;
             return (Top (Exists path) # fs, i + n)
           }
           else return (Bottom (Exists path) # fs, 0)
        }\<close>
     | \<open>try_solve_constraint idirs m (In x n # fs) = do {
          (iface, i) \<leftarrow> try_generate_interface n;
          case iface of
            None \<Rightarrow> return (In x n # fs, i)
          | Some None \<Rightarrow> return (Bottom (In x n) # fs, i)
          | Some (Some iface) \<Rightarrow>
              if contains x iface
                then do {
                  (fs, k) \<leftarrow> try_solve_constraint idirs m fs;
                  return (Top (In x n) # fs, i + k)
                }
                else return (Bottom (In x n) # fs, i)
        }\<close>

(* TODO: when parsing a file, fetch imports and add them to the import_graph
         also add constraint system for each new import, to be resolved before *)
(* NOTE: add new systems only if they have not been added earlier
         we can check if an import was already added by using our \<open>import_graph\<close> *)

fun try_solve_each_constraint :: \<open>String.literal list \<Rightarrow> module_origin \<times> String.literal list \<Rightarrow> system \<Rightarrow> (system \<times> nat) resolver\<close>
where \<open>try_solve_each_constraint _ _ [] = return ([], 0)\<close>
    | \<open>try_solve_each_constraint idirs (orig, m) (c # cs) = do {
         (c, i) \<leftarrow> if is_solved c then return (c, 0) else try_solve_constraint idirs m c;
         (cs, n) \<leftarrow> try_solve_each_constraint idirs (orig, m) cs;
         return (c # cs, i + n)
       }\<close>

fun try_solve_system :: \<open>[String.literal list, nat, system] \<Rightarrow> unit resolver\<close>
where \<open>try_solve_system idirs i s = do {
         (_, ml, _, _, _) \<leftarrow> get;
         (cs, n) \<leftarrow> try_solve_each_constraint idirs (ml ! i) s;
         set_system (i + n) cs
       }\<close>

(* WARN: please do NOT remove the \<open>unit\<close> argument, otherwise \<open>pat_completeness\<close> hangs in the
   definition for \<^const>{parse_and_resolve_modules}. *)
function try_solve_systems_incrementally :: \<open>String.literal list \<Rightarrow> unit \<Rightarrow> unit resolver\<close>
where \<open>try_solve_systems_incrementally idirs () = do {
         sys \<leftarrow> find_unsolved_system ();
         case sys of
           None \<Rightarrow> return ()
         | Some (i, s) \<Rightarrow> try_solve_system idirs i s \<bind> try_solve_systems_incrementally idirs
       }\<close>
by pat_completeness auto

(* TODO: try to detect if system gets stuck solving the same constraint over and over,
         in which case we need to throw an error or something *)

termination
  sorry
(* TODO: need to prove termination
 *
 *       I don't really know how to yet…
 *       Moreover, this proofs relies on the postulate that there is a finite number of files.
 *       When this may not be the case (for example in the presence of symbolic links),
 *       then this function should actually not terminate, unless paths are normalized.
 *       What's true (or at least seems true) is that there is a finite store of normal paths.
 *)

fun check_all_systems :: \<open>system list \<Rightarrow> mod_list \<Rightarrow> unit resolver\<close>
where \<open>check_all_systems [] _ = return ()\<close>
    | \<open>check_all_systems (s # ss) ((orig, m) # ms) =
         (case [c \<leftarrow> s. is_true c] of
           [] \<Rightarrow> throw (mk_cannot_resolve_import_error (pos_or orig m) (map (the \<circ> only_false_constraint) s))
         | (a # b # cs) \<Rightarrow> throw (mk_ambiguous_import_error (pos_or orig m) [c \<leftarrow> a @ b @ (cs \<bind> id). is_true_exists c])
         | [_] \<Rightarrow> check_all_systems ss ms)\<close>
    (* Inconsistent state: all systems must have an associated module *)
    | \<open>check_all_systems _ _ = undefined\<close>

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
           Inl diag \<Rightarrow> IO.return (Inl diag, ([], Map.empty))
         | Inr (sys, mods) \<Rightarrow> do {
             (res, files) \<leftarrow> (do {
               try_solve_systems_incrementally [] ();
               check_final_systems ()
             }) (sys, mods, Map.empty, Map.empty, Digraph.empty);
             let res = do {
                   ((_, _, _, mods, g), ()) \<leftarrow> res;
                   map_sum undefined (Pair mods) (topsort g)
                 };
             IO.return (res, files)
           }
       }\<close>
(* FIXME: little hickup: we can't find the path of a module only knowing the module name,
          yet we return a list of modules (the topsort) along with a list of filepaths mapped to CSTs *)
(* TODO: return all the interfaces generated for later use in the name resolver and the typechecker
         we only need to generate them once *)

hide_type module_origin
hide_const CommandLine InSource

(* Prevent using \<open>bind_sum\<close> outside this theory. *)
hide_const bind_sum bind_resolver return

end
