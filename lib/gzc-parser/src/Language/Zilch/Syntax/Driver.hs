{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoOverloadedLists #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.Zilch.Syntax.Driver (parseModules) where

import qualified Algebra.Graph.AdjacencyMap as Cyclic
import qualified Algebra.Graph.AdjacencyMap.Algorithm as Graph
import Control.Applicative ((<|>))
import Control.Monad (forM_, when)
import Control.Monad.Except (MonadError, liftEither, runExceptT, throwError)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State (MonadState, gets, modify, runStateT)
import Control.Monad.Writer (MonadWriter, runWriterT)
import Data.Bifunctor (bimap, first, second)
import Data.Containers.ListUtils (nubOrdOn)
import Data.Foldable (fold, foldl', foldrM)
import Data.Functor ((<&>))
import Data.List (intercalate, partition)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Located (Located ((:@)), Position (file), getPos, spanOf, unLoc)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes, fromJust)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Error.Diagnose (Diagnostic, addFile, addReport, def, defaultStyle, hasReports, printDiagnostic, warningsToErrors)
import GHC.Stack (HasCallStack)
import Language.Zilch.CLI.Flags (WarningFlags (..))
import qualified Language.Zilch.CLI.Flags as W (WarningFlags (..))
import qualified Language.Zilch.Syntax.Core.AST as AST
import qualified Language.Zilch.Syntax.Core.CST as CST
import Language.Zilch.Syntax.Core.Lexeme (Token)
import Language.Zilch.Syntax.Desugarer (desugarCST)
import Language.Zilch.Syntax.Errors
import Language.Zilch.Syntax.Lexer (lexFile)
import Language.Zilch.Syntax.Parser (parseTokens)
import Language.Zilch.Typecheck.Core.Multiplicity (Multiplicity (..))
import System.Directory (doesFileExist)
import System.Exit (exitFailure)
import System.FilePath (joinPath, splitDirectories, splitExtension, (<.>), (</>))
import System.IO (stderr)

type ModName = [Located Text]

type ImportGraph = Cyclic.AdjacencyMap ModName

type Files = [(FilePath, Text)]

type ParsedFiles = [(FilePath, ModName, Either (Located AST.Module) Interface)]

type MonadDriver m = (?warnings :: WarningFlags, ?includeDirs :: [FilePath], MonadState (Files, [DisSystem]) m, MonadWriter [DriverWarning] m, MonadError DriverError m, MonadIO m, HasCallStack)

data Interface
  = Iface
      [ModName]
      -- ^ Dependencies on other namespaces
      (Map (Located Text) (Located Multiplicity, Interface))
      -- ^ Public exported items
      (Map (Located Text) (Located Multiplicity, Interface))
      -- ^ Private items
  deriving (Show)

data Module
  = Mod ModName FilePath
  | Access Module (Located Text)
  deriving (Eq)

instance Show Module where
  show (Mod mod path) = "MODULE " <> show' mod <> " \"" <> path <> "\""
    where
      show' = Text.unpack . Text.intercalate "∷" . fmap unLoc
  show (Access mod (x :@ _)) = "(" <> show mod <> ")∷" <> Text.unpack x

data Constraint
  = In (Located Text) Module
  | TrueC
  | FalseC
  deriving (Eq)

instance Show Constraint where
  show (In (x :@ _) mod) = Text.unpack x <> " ∈ " <> show mod
  show TrueC = "TRUE"
  show FalseC = "FALSE"

type FileConstraint = (Unit, [Constraint])

instance {-# OVERLAPPING #-} Show FileConstraint where
  show (path, constraints) = unUnit path <> ": " <> intercalate " ∧ " (show <$> constraints)

type DisSystem = ([Located Text], [FileConstraint])

instance {-# OVERLAPPING #-} Show DisSystem where
  show (path, sys) = show' path <> ":\n    " <> if null sys then "FALSE" else intercalate "\n  ∨ " (show <$> sys)
    where
      show' = Text.unpack . Text.intercalate "∷" . fmap unLoc

instance {-# OVERLAPPING #-} Show [DisSystem] where
  show sys = unlines (show <$> sys)

parseModules :: (?warnings :: WarningFlags, ?includeDirs :: [FilePath], MonadIO m) => [Text] -> m ([(FilePath, Text)], Either (Diagnostic String) ([(FilePath, [Located Text], Located AST.Module)], Diagnostic String))
parseModules modules = do
  ((res, (files, _)), warns) <- runWriterT $
    flip runStateT ([], []) $ runExceptT do
      let modules' = (:@ dummy) <$> modules
      -- - resolve all modules on the command-line
      (asts, graph) <-
        foldrM
          (\mod (asts, graph) -> resolveModule False graph asts mod)
          ([], Cyclic.empty)
          modules'
      -- - generate modules interfaces, solve constraints
      --   and remove graph vertices when conjunctive constraints are @FALSE@
      modify $ second (nubOrdOn fst)

      -- gets snd >>= liftIO . print

      ifaces <- foldrM (\(path, mod, iface) cache -> generateInterface path mod iface asts cache) [] asts
      (_, cache') <-
        foldrM (\mod (res, cache) -> first (: res) <$> resolveNamespace mod asts cache []) ([], ifaces)
          =<< traverse tryParseModuleName modules'

      constr <- gets snd
      -- - remove all the graph vertices which are not within the remaining solved constraints
      let remainingModules = fst <$> constr
          graph' = Cyclic.induce (`elem` remainingModules) graph
          modules'' = constr <&> \(mod, [(f, _)]) -> (mod, f)
          graph'' = flip Cyclic.gmap graph' \mod -> (mod, fromJust $ lookup mod modules'')
      -- - check if the remaining graph contains cycles via a simple DFS
      topsort <- case Graph.topSort (Cyclic.transpose graph'') of
        -- transpose the graph in order not to reverse the topsort afterwards
        Left (NonEmpty.toList -> cycle) -> throwError $ CyclicModuleImports (second unUnit <$> cycle)
        Right sort -> pure sort

      let asts' = nubOrdOn (\(path, _, _) -> path) asts
          topsort' = nubOrdOn snd topsort

      asts' <- patchImports asts' constr

      pure (asts', topsort')

  -- TODO: error out if a CLI module name is a non-module namespace (e.g. an @enum@ namespace)

  pure (files, adjust res warns)
  where
    toErrorDiagnostic (LexingE d) = d
    toErrorDiagnostic (ParsingE d) = d
    toErrorDiagnostic (DesugaringE d) = d
    toErrorDiagnostic err = addReport def $ fromDriverError err

    toWarningDiagnostic warns = foldl' addReport def (fromDriverWarning <$> warns)

    adjust (Left err) _ = Left $ toErrorDiagnostic err
    adjust (Right (mods, sorted)) warns =
      let mods' = Map.fromList $ catMaybes $ mods <&> \(path, mod, ast) -> ((path, mod),) <$> eitherToMaybe (swapEither ast)
       in Right (fetch mods' <$> sorted, toWarningDiagnostic warns)

    fetch mods (_, u) = (unUnit u, unit2Mod u, mods Map.! (unUnit u, unit2Mod u))

    dummy = def {file = "command-line"}

    eitherToMaybe (Left _) = Nothing
    eitherToMaybe (Right x) = Just x

    swapEither (Left x) = Right x
    swapEither (Right x) = Left x

resolveModule :: forall m. MonadDriver m => Bool -> ImportGraph -> ParsedFiles -> Located Text -> m (ParsedFiles, ImportGraph)
resolveModule isSourceImport graph cache mod = do
  -- liftIO do putStrLn $ "Resolving module " <> Text.unpack (unLoc mod)

  -- - create constraints from all the module names
  constr <- pruneConstraints =<< generateConstraints [mod]
  -- - check that all modules have at least a single constraint
  --   if not, at least one of them could not be found in the include path
  checkThatNamespacesExist isSourceImport constr
  -- - remove the @.zc@ files if there is also a @.zci@ file for the same exact file prefix
  constr <- pruneDuplicatedWithInterface constr
  -- - parse every possible modules (or decipher .zci files) and generate entries in the include graph
  (cache', graph) <- parseAllFiles graph cache constr

  modify $ second (<> constr)

  pure (cache', graph)

generateConstraints :: forall m. MonadDriver m => [Located Text] -> m [DisSystem]
generateConstraints [] = pure []
generateConstraints (m : ms) = do
  m' <- tryParseModuleName m
  cs <- mkConstraints m'

  cs2 <- generateConstraints ms
  pure $ (m', cs) : cs2
  where
    mkConstraints :: forall m. MonadDriver m => [Located Text] -> m [FileConstraint]
    mkConstraints modParts = do
      -- - generate all possible paths from @modParts@
      --   for example, @x::y@ yields the paths @[("x.zc", ["y"]), ("x/y.zc", [])]@
      let paths = genPathAndComponents [] modParts :: [(FilePath, [Located Text])]
      -- - then concatenate every include directory in front of each path generated
      --   (copy all the paths for every include directory)
      let withDirs =
            ?includeDirs >>= \dir ->
              paths <&> \(path, comps) -> case splitExtension path of
                (path, ".zc") -> (File dir path, comps)
                (path, ".zci") -> (Interface dir path, comps)
                (_, ext) -> error $ "Unknown file extension '" <> ext <> "'"
      -- - finally make all the necessary constraints (where an empty component list is transformed into a @TrueC@ constraint)
      pure $ uncurry mkConstraints' <$> withDirs

    genPathAndComponents _ [] = []
    genPathAndComponents acc (x : xs) =
      let x' = Text.unpack (unLoc x)
          comp1 = (joinPath $ acc <> [x' <.> "zc"], xs)
          comp2 = (joinPath $ acc <> [x' <.> "zci"], xs)
          xs' = genPathAndComponents (acc <> [x']) xs
       in comp1 : comp2 : xs'

    mkConstraints' path [] = (path, [TrueC])
    mkConstraints' path xs = (path, reverse . snd $ foldl' genConstraint (Mod (unit2Mod path) (unUnit path), []) xs)

    genConstraint (mod, cs) id = (Access mod id, In id mod : cs)

pruneConstraints :: forall m. MonadDriver m => [DisSystem] -> m [DisSystem]
pruneConstraints [] = pure []
pruneConstraints ((mod, constrs) : sys) = do
  constrs' <- catMaybes <$> traverse removeConstraintIfFileDoesNotExist constrs
  sys' <- pruneConstraints sys
  pure $ (mod, constrs') : sys'
  where
    removeConstraintIfFileDoesNotExist c@(unUnit -> file, _) = do
      fileExists <- liftIO $ doesFileExist file
      pure
        if fileExists
          then Just c
          else Nothing

checkThatNamespacesExist :: forall m. MonadDriver m => Bool -> [DisSystem] -> m ()
checkThatNamespacesExist isSource sys = forM_ sys \(mod, constrs) -> case constrs of
  [] ->
    throwError
      if isSource
        then UnresolvedImport mod ?includeDirs
        else ModuleNotFound mod ?includeDirs
  _ -> pure ()

pruneDuplicatedWithInterface :: forall m. MonadDriver m => [DisSystem] -> m [DisSystem]
pruneDuplicatedWithInterface sys = pure $ sys <&> \(mod, constr) -> (mod, go constr)
  where
    go constr =
      let interfaces = filter isInterface (fst <$> constr) <&> \(Interface _ path) -> path
       in flip filter constr \case
            (File _ path, _) -> path `notElem` interfaces
            _ -> True

parseAllFiles :: forall m. MonadDriver m => ImportGraph -> ParsedFiles -> [DisSystem] -> m (ParsedFiles, ImportGraph)
parseAllFiles graph asts sys = do
  let units = sys >>= \(mod, constr) -> (mod,) . fst <$> constr
  (asts, graph) <- go graph units asts
  pure (asts, graph)
  where
    go :: forall m. MonadDriver m => ImportGraph -> [(ModName, Unit)] -> ParsedFiles -> m (ParsedFiles, ImportGraph)
    go graph [] cache = pure (cache, graph)
    go graph ((mod, u) : us) cache = do
      (cache', graph') <- go graph us cache

      case u of
        Interface _ _ -> error "TODO: decipher .zci and add imports to graph"
        File _ _ -> do
          let path' = unUnit u
              mod' = unit2Mod u

          case lookup' (mod', path') cache' of
            Nothing -> do
              content <- liftIO $ Text.readFile path'
              modify $ first ((path', content) :)

              (tks, warns) <- tryLexing path' content
              liftIO $ doOutputWarnings path' content warns

              (cst, warns) <- tryParsing path' tks
              liftIO $ doOutputWarnings path' content warns

              (imports, ast, warns) <- tryDesugaring cst
              liftIO $ doOutputWarnings path' content warns

              -- try to also resolve all the imports right now
              (cache'', graph'') <-
                foldrM
                  (\mod (asts, graph) -> resolveModule True graph asts mod)
                  ((path', mod', Left ast) : cache', graph')
                  (mkMod <$> imports)

              pure (cache'', graph'' `Cyclic.overlay` (Cyclic.edges $ (mod,) <$> imports) `Cyclic.overlay` Cyclic.vertex mod')
            Just _ -> pure (cache', graph')

    mkMod :: [Located Text] -> Located Text
    mkMod mod =
      let pos = foldr1 spanOf (getPos <$> mod)
       in (:@ pos) . Text.intercalate "::" $ unLoc <$> mod

    lookup' :: (ModName, FilePath) -> ParsedFiles -> Maybe (Either (Located AST.Module) Interface)
    lookup' _ [] = Nothing
    lookup' (m, p) ((path, mod, r) : cs)
      | m == mod && p == path = Just r
      | otherwise = lookup' (m, p) cs

generateInterface :: forall m. MonadDriver m => FilePath -> ModName -> Either (Located AST.Module) Interface -> ParsedFiles -> [(FilePath, ModName, Interface)] -> m [(FilePath, ModName, Interface)]
generateInterface path mod (Right iface) _ cache = pure $ (path, mod, iface) : cache
generateInterface path mod (Left ast) asts cache = do
  -- liftIO do putStrLn $ "Generating interface for module " <> show (unLoc <$> mod) <> " " <> path

  (items, deps, cache') <- accumItemsAndDeps ast cache
  let (pub, priv) = bimap (Map.map keepIface) (Map.map keepIface) $ Map.partition snd3 items
  pure $ (path, mod, Iface deps pub priv) : cache'
  where
    accumItemsAndDeps :: forall m. MonadDriver m => Located AST.Module -> [(FilePath, ModName, Interface)] -> m (Map (Located Text) (Located Multiplicity, Bool, Interface), [ModName], [(FilePath, ModName, Interface)])
    accumItemsAndDeps (AST.Mod toplevel :@ _) cache = fold <$> traverse (flip accumItemsAndDepsToplevel cache) toplevel

    accumItemsAndDepsToplevel (AST.TopLevel isPublic _ def :@ _) cache = case def of
      AST.Let _ mult name ty ex :@ _ ->
        let imps = findImports ty <> findImports ex
         in pure (Map.singleton name (mult, isPublic, Iface imps mempty mempty), imps, cache)
      AST.Val mult name ty :@ _ ->
        let imps = findImports ty
         in pure (Map.singleton name (mult, isPublic, Iface imps mempty mempty), imps, cache)
      AST.Import isOpen path' x _ :@ _ -> do
        -- - if the import is open:
        --   - if @...path::x@ is a namespace, bring every public item into the scope
        --   - if @...path::x@ is not a namespace, act as if the import is not opened (and emit a warning)
        -- - otherwise:
        --   - add @x@ into the scope
        let ns = path' <> x
        (resolved, cache') <- resolveNamespace ns asts cache [path]
        let intoScope =
              case resolved of
                ResolvedNamespace iface@(Iface _ pub _) ->
                  if isOpen
                    then pub <&> \(mult, iface) -> (mult, isPublic, iface)
                    else Map.singleton (last ns) (W :@ dummy, isPublic, iface)
                ResolvedItem id mult -> Map.singleton id (mult, isPublic, Iface [] mempty mempty)
        pure (intoScope, [ns], cache')

    dummy = def {file = "unknown"}

    findImports :: Located AST.Expression -> [ModName]
    findImports (AST.EInteger _ _ :@ _) = []
    findImports (AST.ECharacter _ :@ _) = []
    findImports (AST.EIdentifier _ :@ _) = []
    findImports (AST.EType :@ _) = []
    findImports (AST.EHole _ :@ _) = []
    findImports (AST.EMultiplicativeUnit :@ _) = []
    findImports (AST.EAdditiveUnit :@ _) = []
    findImports (AST.EBoolean _ :@ _) = []
    findImports (AST.EOne :@ _) = []
    findImports (AST.ETop :@ _) = []
    findImports (AST.ELam param ex :@ _) = findImportsInParam param <> findImports ex
    findImports (AST.EApplication e1 _ e2 :@ _) = findImports e1 <> findImports e2
    findImports (AST.EPi param ex :@ _) = findImportsInParam param <> findImports ex
    findImports (AST.EMultiplicativeProduct param ex :@ _) = findImportsInParam param <> findImports ex
    findImports (AST.EAdditiveProduct param ex :@ _) = findImportsInParam param <> findImports ex
    findImports (AST.EMultiplicativePair e1 e2 :@ _) = findImports e1 <> findImports e2
    findImports (AST.EAdditivePair e1 e2 :@ _) = findImports e1 <> findImports e2
    findImports (AST.EIfThenElse c e1 e2 :@ _) = findImports c <> findImports e1 <> findImports e2
    findImports (AST.EFst e :@ _) = findImports e
    findImports (AST.ESnd e :@ _) = findImports e
    findImports (AST.EAdditiveTupleAccess e _ :@ _) = findImports e
    findImports (AST.EMultiplicativePairElim _ _ _ _ e1 e2 :@ _) = findImports e1 <> findImports e2
    findImports (AST.EMultiplicativeUnitElim _ _ e1 e2 :@ _) = findImports e1 <> findImports e2
    findImports (AST.EFieldAccess e _ :@ _) = findImports e
    findImports (AST.ELocal def e :@ _) = findImportsInDefinition def <> findImports e

    findImportsInParam (AST.Parameter _ _ _ e :@ _) = findImports e

    findImportsInDefinition (AST.Let _ _ _ ty ex :@ _) = findImports ty <> findImports ex
    findImportsInDefinition (AST.Val _ _ ty :@ _) = findImports ty
    findImportsInDefinition (AST.Import _ path x _ :@ _) = [path <> x]

    snd3 ~(_, x, _) = x

    keepIface ~(x, _, z) = (x, z)

data Resolved
  = ResolvedNamespace Interface
  | ResolvedItem (Located Text) (Located Multiplicity)

resolveNamespace :: forall m. MonadDriver m => ModName -> ParsedFiles -> [(FilePath, ModName, Interface)] -> [FilePath] -> m (Resolved, [(FilePath, ModName, Interface)])
resolveNamespace mod asts cache = solveConstraintFor mod asts cache

solveConstraintFor :: forall m. MonadDriver m => ModName -> ParsedFiles -> [(FilePath, ModName, Interface)] -> [FilePath] -> m (Resolved, [(FilePath, ModName, Interface)])
solveConstraintFor mod asts cache filteredPaths = do
  constr <- gets snd
  let Just ((mod', c), cs) = findElem ((== mod) . fst) constr

  -- - try to solve each file constraint independently
  --   however, there is a small "problem" regarding errors:
  --
  --   ideally, we'd know exactly which part of a constraint failed to be satisfied
  --   in order to report an error more useful than "name resolution failed"
  --
  --   but in order to do so, we have to store independently the value of each constraint
  --   and also return the value of the whole conjonction/disjunction
  --
  --   we needs to inspect each disjunction value anyways (to report ambiguous resolved items)
  --   and we need to throw an error if the disjunction has no @TRUE@ value inside (in such case, constraints were not satisfied)
  (c', cache') <- foldrM (\c (cs, cache) -> first (: cs) <$> solve' mod' c cache) ([], cache) c

  let trueCons =
        -- filtering here is equivalent to applying an 'or'
        -- because we only keep the values which are @TRUE@ ('or' is @TRUE@ only if there is at least one @TRUE@)
        --
        -- when there is no such value, the end list is empty, therefore equivalent to @FALSE@
        --
        -- this allows us to keep every subconstraint for error-reporting later, and also to check how many
        -- @TRUE@ subconstraints there really are
        filter snd $ second (Prelude.all snd) <$> c'

  unit <- case trueCons of
    [(u, _)] -> pure u
    -- - check whether this constraint is ambiguous (if multiple subconstraints are @TRUE@)
    cs@(_ : _) -> throwError $ AmbiguousModuleName mod' (unUnit . fst <$> cs)
    -- - check whether this constraint is actually @TRUE@ otherwise report an unresolved namespace
    [] -> throwError $ UnresolvedImport mod' ?includeDirs
  modify $ second $ const ((mod', [(unit, [TrueC])]) : cs)

  let Just cs = lookup unit c'
  (r, cache'') <- resolve mod unit cs cache'

  case r of
    Nothing -> undefined
    Just i@(Iface _ pub priv)
      | Map.null pub && Map.null priv -> pure (ResolvedItem (last mod) undefined, cache'')
      | otherwise -> pure (ResolvedNamespace i, cache'')
  where
    solve' :: forall m. MonadDriver m => ModName -> FileConstraint -> [(FilePath, ModName, Interface)] -> m ((Unit, [(Constraint, Bool)]), [(FilePath, ModName, Interface)])
    solve' mod (f, c) cache = do
      (cs, cache') <- foldrM (\c (cs, cache) -> first (: cs) <$> solve'' mod c cache) ([], cache) c
      pure ((f, cs), cache')

    solve'' :: forall m. MonadDriver m => ModName -> Constraint -> [(FilePath, ModName, Interface)] -> m ((Constraint, Bool), [(FilePath, ModName, Interface)])
    solve'' mod c cache = do
      (b, cache') <- case c of
        TrueC -> pure (True, cache)
        FalseC -> pure (False, cache)
        In id mod' -> do
          (iface, cache') <- interfaceOf mod mod' cache
          case iface of
            Nothing -> pure (False, cache')
            Just (Iface _ pub _) ->
              -- - if @id@ is not a public member, constraint cannot be solved
              case Map.lookup id pub of
                Nothing -> pure (False, cache')
                Just _ -> pure (True, cache')
      pure ((c, b), cache')

    interfaceOf base (Mod mod path) cache = do
      if path `elem` filteredPaths
        then pure (Nothing, cache)
        else case safeHead (filter (\(p, m, _) -> p == path && m == mod) cache) of
          Just (_, _, iface) -> pure (Just iface, cache)
          Nothing -> do
            let (path', mod', ast) = head (filter (\(p, m, _) -> p == path && m == mod) asts)
            interfaceOf base (Mod mod path') =<< generateInterface path' mod' ast asts cache
    interfaceOf mod (Access mod' x) cache = do
      (iface, cache') <- interfaceOf mod mod' cache
      case iface of
        Nothing -> pure (Nothing, cache')
        Just (Iface _ pub _) -> do
          -- - if @id@ is not a public member, constraint cannot be solved
          case Map.lookup x pub of
            Nothing -> pure (Nothing, cache')
            Just (_, iface) -> pure (Just iface, cache')

    resolve = goResolve Nothing

    goResolve acc _ _ [] cache = pure (acc, cache)
    goResolve acc mod unit ((c, True) : cs) cache = case c of
      TrueC -> do
        (iface, cache') <- interfaceOf mod (Mod (unit2Mod unit) (unUnit unit)) cache
        goResolve (iface <|> acc) mod unit cs cache'
      FalseC -> undefined
      In x mod' -> interfaceOf mod (Access mod' x) cache
    goResolve _ _ _ ((_, False) : _) cache = pure (Nothing, cache)

patchImports :: forall m. MonadDriver m => ParsedFiles -> [DisSystem] -> m ParsedFiles
patchImports [] _ = pure []
patchImports ((path, mod, ast) : fs) sys = do
  ast' <- patch ast sys
  fs' <- patchImports fs sys
  pure ((path, mod, ast') : fs')
  where
    patch (Right iface) _ = pure $ Right iface
    patch (Left (AST.Mod defs :@ p)) sys = do
      defs' <- traverse (flip patchToplevel sys) defs
      pure $ Left $ AST.Mod defs' :@ p

    patchToplevel (AST.TopLevel isPublic metas def :@ p) sys = do
      def' <- patchDefinition def sys
      pure $ AST.TopLevel isPublic metas def' :@ p

    patchDefinition (AST.Let isRec mult name ty ex :@ p) sys = do
      ty' <- patchExpression ty sys
      ex' <- patchExpression ex sys
      pure $ AST.Let isRec mult name ty' ex' :@ p
    patchDefinition (AST.Val mult name ty :@ p) sys = do
      ty' <- patchExpression ty sys
      pure $ AST.Val mult name ty' :@ p
    patchDefinition (AST.Import isOpen mod _ _ :@ p) sys = do
      --                                   ^^^ should be empty because desugaring gives @[]@ and @""@
      let Just [(unit, _)] = lookup mod sys
          mod' = unit2Mod unit
          path = unUnit unit
          item = drop (length mod') mod
      pure $ AST.Import isOpen mod' item path :@ p

    patchExpression (AST.EInteger i suf :@ p) _ = pure $ AST.EInteger i suf :@ p
    patchExpression (AST.ECharacter c :@ p) _ = pure $ AST.ECharacter c :@ p
    patchExpression (AST.EIdentifier id :@ p) _ = pure $ AST.EIdentifier id :@ p
    patchExpression (AST.ELam param ex :@ p) sys = do
      param' <- patchParameter param sys
      ex' <- patchExpression ex sys
      pure $ AST.ELam param' ex' :@ p
    patchExpression (AST.ELocal def ex :@ p) sys = do
      def' <- patchDefinition def sys
      ex' <- patchExpression ex sys
      pure $ AST.ELocal def' ex' :@ p
    patchExpression (AST.EApplication e1 isImp e2 :@ p) sys = do
      e1' <- patchExpression e1 sys
      e2' <- patchExpression e2 sys
      pure $ AST.EApplication e1' isImp e2' :@ p
    patchExpression (AST.EType :@ p) _ = pure $ AST.EType :@ p
    patchExpression (AST.EHole loc :@ p) _ = pure $ AST.EHole loc :@ p
    patchExpression (AST.EPi param ex :@ p) sys = do
      param' <- patchParameter param sys
      ex' <- patchExpression ex sys
      pure $ AST.EPi param' ex' :@ p
    patchExpression (AST.EMultiplicativeProduct param ex :@ p) sys = do
      param' <- patchParameter param sys
      ex' <- patchExpression ex sys
      pure $ AST.EMultiplicativeProduct param' ex' :@ p
    patchExpression (AST.EAdditiveProduct param ex :@ p) sys = do
      param' <- patchParameter param sys
      ex' <- patchExpression ex sys
      pure $ AST.EAdditiveProduct param' ex' :@ p
    patchExpression (AST.EMultiplicativePair e1 e2 :@ p) sys = do
      e1' <- patchExpression e1 sys
      e2' <- patchExpression e2 sys
      pure $ AST.EMultiplicativePair e1' e2' :@ p
    patchExpression (AST.EAdditivePair e1 e2 :@ p) sys = do
      e1' <- patchExpression e1 sys
      e2' <- patchExpression e2 sys
      pure $ AST.EAdditivePair e1' e2' :@ p
    patchExpression (AST.EMultiplicativeUnit :@ p) _ = pure $ AST.EMultiplicativeUnit :@ p
    patchExpression (AST.EAdditiveUnit :@ p) _ = pure $ AST.EAdditiveUnit :@ p
    patchExpression (AST.EBoolean b :@ p) _ = pure $ AST.EBoolean b :@ p
    patchExpression (AST.EIfThenElse c e1 e2 :@ p) sys = do
      c' <- patchExpression c sys
      e1' <- patchExpression e1 sys
      e2' <- patchExpression e2 sys
      pure $ AST.EIfThenElse c' e1' e2' :@ p
    patchExpression (AST.EOne :@ p) _ = pure $ AST.EOne :@ p
    patchExpression (AST.ETop :@ p) _ = pure $ AST.ETop :@ p
    patchExpression (AST.EFst e :@ p) sys = do
      e' <- patchExpression e sys
      pure $ AST.EFst e' :@ p
    patchExpression (AST.ESnd e :@ p) sys = do
      e' <- patchExpression e sys
      pure $ AST.ESnd e' :@ p
    patchExpression (AST.EAdditiveTupleAccess e n :@ p) sys = do
      e' <- patchExpression e sys
      pure $ AST.EAdditiveTupleAccess e' n :@ p
    patchExpression (AST.EFieldAccess e x :@ p) sys = do
      e' <- patchExpression e sys
      pure $ AST.EFieldAccess e' x :@ p
    patchExpression (AST.EMultiplicativePairElim z mult x y e1 e2 :@ p) sys = do
      e1' <- patchExpression e1 sys
      e2' <- patchExpression e2 sys
      pure $ AST.EMultiplicativePairElim z mult x y e1' e2' :@ p
    patchExpression (AST.EMultiplicativeUnitElim z mult e1 e2 :@ p) sys = do
      e1' <- patchExpression e1 sys
      e2' <- patchExpression e2 sys
      pure $ AST.EMultiplicativeUnitElim z mult e1' e2' :@ p
    patchExpression (AST.ERecordLiteral fields :@ p) sys = do
      fields' <- Map.traverseWithKey (\_ (mult, e) -> (mult,) <$> patchExpression e sys) fields
      pure $ AST.ERecordLiteral fields' :@ p
    patchExpression (AST.EComposite fields :@ p) sys = do
      fields' <- Map.traverseWithKey (\_ (mult, e) -> (mult,) <$> patchExpression e sys) fields
      pure $ AST.EComposite fields' :@ p

    patchParameter (AST.Parameter isImp mult name ty :@ p) sys = do
      ty' <- patchExpression ty sys
      pure $ AST.Parameter isImp mult name ty' :@ p

--------------------

tryParseModuleName :: forall m. MonadDriver m => Located Text -> m [Located Text]
tryParseModuleName (m :@ p) = do
  let parts = fold $ Text.splitOn "∷" <$> Text.splitOn "::" m
  traverse checkValid parts
  where
    checkValid "" = throwError $ EmptyModuleName m
    checkValid part = do
      case Text.findIndex invalidCharacters part of
        Just idx -> throwError $ InvalidModuleName part idx
        Nothing -> pure $ part :@ p

    invalidCharacters '/' = True
    invalidCharacters ':' = True
    invalidCharacters '\\' = True
    invalidCharacters '"' = True
    invalidCharacters ',' = True
    invalidCharacters ';' = True
    invalidCharacters '=' = True
    invalidCharacters _ = False

data Unit
  = -- | a @.zci@ module interface
    Interface FilePath FilePath
  | -- | a @.zc@ normal file
    File FilePath FilePath
  deriving (Eq, Ord)

instance Show Unit where
  show = unUnit

unUnit :: Unit -> FilePath
unUnit (Interface dir path) = dir </> path <.> "zci"
unUnit (File dir path) = dir </> path <.> "zc"

unit2Mod :: Unit -> ModName
unit2Mod = \case
  Interface _ path -> mkMod path
  File _ path -> mkMod path
  where
    mkMod = fmap ((:@ def) . Text.pack) . splitDirectories

isInterface :: Unit -> Bool
isInterface (Interface _ _) = True
isInterface _ = False

tryLexing :: forall m. MonadDriver m => FilePath -> Text -> m ([Located Token], Diagnostic String)
tryLexing path content = liftEither . first LexingE $ lexFile path content

tryParsing :: forall m. MonadDriver m => FilePath -> [Located Token] -> m (Located CST.Module, Diagnostic String)
tryParsing path tks = liftEither . first ParsingE $ parseTokens path tks

tryDesugaring :: forall m. MonadDriver m => Located CST.Module -> m ([[Located Text]], Located AST.Module, Diagnostic String)
tryDesugaring cst = liftEither . bimap DesugaringE swapFirstTwo $ desugarCST cst
  where
    swapFirstTwo ~(a, b, c) = (b, a, c)

---------------------------------

doOutputWarnings :: (?warnings :: WarningFlags) => FilePath -> Text -> Diagnostic String -> IO ()
doOutputWarnings path content diag = do
  let erroneous = W.areErrors ?warnings
  let diag' = if erroneous then warningsToErrors diag else diag

  printDiagnostic stderr True True 4 defaultStyle (addFile diag' path $ Text.unpack content)
  when (erroneous && hasReports diag') do
    exitFailure

-------------------------------

findElem :: (a -> Bool) -> [a] -> Maybe (a, [a])
findElem p = find' id
  where
    find' _ [] = Nothing
    find' prefix (x : xs)
      | p x = Just (x, prefix xs)
      | otherwise = find' (prefix . (x :)) xs

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x : _) = Just x
