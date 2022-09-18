module Language.Zilch.Typecheck.Imports where

import Data.Located (Located)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import Language.Zilch.Typecheck.Core.Eval (Value)
import Language.Zilch.Typecheck.Core.Multiplicity (Multiplicity)

type ImportCache = Map (FilePath, [Located Text]) ModuleInterface

insert :: (FilePath, [Located Text]) -> ModuleInterface -> ImportCache -> ImportCache
insert = Map.insert

lookup :: (FilePath, [Located Text]) -> ImportCache -> Maybe ModuleInterface
lookup = Map.lookup

data ModuleInterface
  = Iface
      (Map (Located Text) Namespace)
      -- ^ Public interface
      (Map (Located Text) Namespace)
      -- ^ Private interface
  deriving (Show)

instance Monoid ModuleInterface where
  mempty = Iface mempty mempty

instance Semigroup ModuleInterface where
  Iface pub1 priv1 <> Iface pub2 priv2 = Iface (pub1 <> pub2) (priv1 <> priv2)

data Namespace
  = SingleNS
      (Located Multiplicity)
      -- ^ The multiplicity of the element
      (Located Value)
      -- ^ The evaluated type of the element
      (Located Value)
      -- ^ The evaluated value of the element
  | MultipleNS
      (Located Multiplicity)
      -- ^ The multiplicity of the container (@ω@ for modules)
      (Located Value)
      -- ^ The evaluated type of the container
      ModuleInterface
      -- ^ All the elements within the namespace
  deriving (Show)
