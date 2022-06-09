{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Zilch.Typecheck.Elaborator where

import Control.Monad.Except (MonadError)
import Control.Monad.Reader (MonadReader)
import Data.IntMap (IntMap)
import Data.Located (Located)
import Error.Diagnose (Diagnostic)
import qualified Language.Zilch.Syntax.Core.AST as AST
import qualified Language.Zilch.Typecheck.Core.AST as TAST
import qualified Language.Zilch.Typecheck.Core.Eval (MetaEntry)
import Language.Zilch.Typecheck.Errors (ElabError)

type MonadElab m = (MonadError ElabError m)

elabProgram :: Located AST.Module -> Either (Diagnostic String) (Located TAST.Module)
