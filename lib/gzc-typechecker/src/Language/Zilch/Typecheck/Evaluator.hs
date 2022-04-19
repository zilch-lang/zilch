module Language.Zilch.Typecheck.Evaluator (normalize, normalize0) where

import qualified Data.HashMap as Hash
import Data.Located (Located ((:@)), Position (Position), unLoc)
import Data.Maybe (fromJust)
import Data.Text (Text)
import qualified Data.Text as Text
import Language.Zilch.Syntax.Core.AST (Definition (..), Expression (..), Parameter (..))
import Language.Zilch.Typecheck.Core.Eval
import Language.Zilch.Typecheck.Fresh (fresh)
import Prelude hiding (read)
import qualified Prelude (read)

-- | Extend the given environment by one entry.
extend :: Environment -> Name -> Value -> Environment
extend env name val = Hash.insert name val env

eval :: Environment -> Expression -> Value
eval _ (EInteger e) = VInteger (read $ unLoc e)
eval env (EIdentifier n) = fromJust $ Hash.lookup (unLoc n) env
eval env (EApplication (e1 :@ _) (e2 :@ _)) = case (eval env e1, eval env e2) of
  (VLam _ clos, u) -> clos u
  (t, u) -> VApplication t u
eval env (ELet (Let True name _ val :@ _) u) = eval (extend env (unLoc name) (eval env $ unLoc val)) (unLoc u)
eval env (ELet (Let False name _ val :@ _) u) = eval (extend env (unLoc name) (eval env $ unLoc val)) (unLoc u)
eval env (EPi (Parameter _ name ty1 :@ _) ty2) = VPi (unLoc name) (eval env $ unLoc ty1) (\u -> eval (extend env (unLoc name) u) $ unLoc ty2)
eval env (ELam (Parameter _ name _ :@ _) ex) = VLam (unLoc name) (\u -> eval (extend env (unLoc name) u) $ unLoc ex)
eval _ e = error $ "unhandled case " <> show e

p :: Position
p = Position (0, 0) (0, 0) "_"

quote :: Environment -> Value -> Located Expression
quote env = \case
  VIdentifier n -> EIdentifier (n :@ p) :@ p
  VInteger n -> EInteger (Text.pack (show n) :@ p) :@ p
  VApplication v1 v2 -> EApplication (quote env v1) (quote env v2) :@ p
  VLam x' clos ->
    let x = fresh env x'
     in ELam (Parameter False (x :@ p) (EHole :@ p) :@ p) (quote (extend env x (VIdentifier x)) $ clos (VIdentifier x)) :@ p
  VPi x' val clos ->
    let x = fresh env x'
     in EPi (Parameter False (x :@ p) (quote env val) :@ p) (quote (extend env x (VIdentifier x)) $ clos (VIdentifier x)) :@ p
  v -> error $ "not yet handled " <> show v

normalize :: Environment -> Located Expression -> Located Expression
normalize env = quote env . eval env . unLoc

normalize0 :: Located Expression -> Located Expression
normalize0 = quote mempty . eval mempty . unLoc

------------

read :: Read a => Text -> a
read = Prelude.read . Text.unpack
