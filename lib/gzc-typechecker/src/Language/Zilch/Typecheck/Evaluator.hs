module Language.Zilch.Typecheck.Evaluator (eval) where

import qualified Data.HashMap as Hash
import Data.Located (Located ((:@)), unLoc)
import Data.Maybe (fromJust)
import Data.Text (Text)
import qualified Data.Text as Text
import Language.Zilch.Syntax.Core.AST (Definition (..), Expression (..), Parameter (..))
import Language.Zilch.Typecheck.Core.Eval
import Prelude hiding (read)
import qualified Prelude (read)

-- | Extend the given environment by one entry.
extend :: Environment -> Name -> Value -> Environment
extend env name val = Hash.insert name val env

eval :: Environment -> Expression -> Value
eval _ (EInteger e) = VInteger (read $ unLoc e)
eval env (EIdentifier n) = fromJust $ Hash.lookup (unLoc n) env
eval env (EApplication (e1 :@ _) (e2 :@ _)) = case (eval env e1, eval env e2) of
  (VLam clos, u) -> clos u
  (t, u) -> VApplication t u
eval env (ELet (Let True name _ val :@ _) u) = eval (extend env (unLoc name) (eval env $ unLoc val)) (unLoc u)
eval env (ELet (Let False name _ val :@ _) u) = eval (extend env (unLoc name) (eval env $ unLoc val)) (unLoc u)
eval env (EPi (Parameter _ name ty1 :@ _) ty2) = VPi (unLoc name) (eval env $ unLoc ty1) (\u -> eval (extend env (unLoc name) u) $ unLoc ty2)
eval env (ELam (Parameter _ name _ :@ _) ex) = VLam (\u -> eval (extend env (unLoc name) u) $ unLoc ex)
eval _ e = error $ "unhandled case " <> show e

------------

read :: Read a => Text -> a
read = Prelude.read . Text.unpack
