{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}

module Language.Zilch.Typecheck.Internal.Mangler where

import Data.Bifunctor (first)
import Data.Char (isAlphaNum, isAscii, ord)
import Data.List (foldl')
import Data.Located (Located ((:@)), getPos, unLoc)
import Data.Text (Text)
import qualified Data.Text as Text
import GHC.Exts (IsList (..))
import Language.Zilch.Typecheck.IR (BuiltinType (..), Expression (..), Parameter (..))

-- see https://itanium-cxx-abi.github.io/cxx-abi/abi.html#mangling

type TemplateSpecialisation = [(Located Text, Located Expression)]

-- | A variant of 'mangle' which also adds the module qualification.
mangleInNS :: [Located Text] -> TemplateSpecialisation -> Located Expression -> Located Text
mangleInNS = mangledName

mangle :: Located Text -> TemplateSpecialisation -> Located Expression -> Located Text
mangle = mangledName . pure

-- |
--  > <mangled-name> ::= _Z <encoding>
--  >                  | _Z <encoding> . <vendor specific suffix>
mangledName :: [Located Text] -> TemplateSpecialisation -> Located Expression -> Located Text
mangledName n spec t = ("_Z" <> encoding (unLoc <$> n) spec t) :@ getPos (last n)

-- |
--  > <encoding> ::= <function name> <bare-function-type>
--  >              | <data name>
--  >              | <special name>
encoding :: [Text] -> TemplateSpecialisation -> Located Expression -> Text
encoding n spec t = name spec n <> functionType spec (not $ null spec) t

-- |
--  > <name> ::= <nested-name>
--  >          | <unscoped-name>
--
--  > <nested-name> ::= N <prefix> <unqualified-name> E
--
--  > <prefix> ::= <unqualified-name>                 # global namespace
--  >            | <prefix> <unqualified-name>        # nested namespace
--
--  > <unscoped-name> ::= <unqualified-name>
--
--  > <unqualified-name> ::= <operator-name> [<abi-tags>]
--  >                      | <source-name>
--  >                      | <unnamed-type-name>
--
--  > <source-name> ::= <positive length number> <source identifier>
--
--  /Note:/ encoding of @<source identifier>@ is left to us when characters used are outside the range @_A-Za-z0-9@.
--          We simply substitute any character @c@ by @U<ord c>@ where @ord c@ is simply the unicode number encoding @c@.
name :: TemplateSpecialisation -> [Text] -> Text
name spec n = case n of
  [n] -> goName [n] <> goSpec spec
  [] -> undefined
  ns -> "N" <> goName ns <> goSpec spec <> "E"
  where
    goName = \case
      [] -> undefined
      [n] -> mangleName n
      ns -> foldl' (\x y -> x <> mangleName y) "" ns

    goSpec [] = ""
    goSpec xs = "I" <> foldl' (\x (_, y) -> x <> type' spec y) "" xs <> "E"

    encodeUnicode c
      | (isAlphaNum c && isAscii c) || c == '_' = Text.singleton c
      | otherwise = "U" <> Text.pack (show $ ord c)

    mangleName :: Text -> Text
    mangleName n =
      let x = Text.concat $ encodeUnicode <$> toList n
       in Text.pack (show $ Text.length x) <> x

-- |
--  > <bare-function-type> ::= <signature type>+
--  >      # return type (void if unit) then parameters in left to right order
functionType :: TemplateSpecialisation -> Bool -> Located Expression -> Text
functionType spec withRet t@(EPi _ _ :@ _) = Text.concat ((if withRet then (type' spec ret :) else id) (type' spec <$> params))
  where
    (params, ret) = mkTelescope t

    mkTelescope :: Located Expression -> ([Located Expression], Located Expression)
    mkTelescope (EPi (Parameter _ _ pt :@ _) t :@ _) = first (pt :) (mkTelescope t)
    mkTelescope t = ([], t)

-- |
--  > <type> ::= <builtin-type>
--  >          | <qualified-type>
--  >          | <function-type>
--  >          | <array-type>
--  >          | P <type>      # pointer
--  >          | R <type>      # l-value reference
--  >          | O <type>      # r-value reference
type' :: TemplateSpecialisation -> Located Expression -> Text
type' _ (EBuiltin ty :@ _) = builtinType ty
type' _ (EOne :@ _) = "v"
type' spec (EIdentifier [x] :@ _) = case keyIndex x spec of
  Just 0 -> "T_"
  Just i -> "T" <> Text.pack (show $ i - 1) <> "_"
  Nothing -> undefined
  where
    keyIndex = go 0

    go _ _ [] = Nothing
    go n x ((y, _) : ys)
      | x == y = Just n
      | otherwise = go (n + 1) x ys
type' spec ty@(EPi _ _ :@ _) = "P" <> "F" <> functionType spec True ty <> "E"

-- box every function argument

-- |
--  > <builtin-type> ::= v     # void
--  >                  | w     # wchar_t
--  >                  | b     # bool
--  >                  | c     # char
--  >                  | a     # signed char
--  >                  | h     # unsigned char
--  >                  | s     # short
--  >                  | t     # unsigned short
--  >                  | i     # int
--  >                  | j     # unsigned int
--  >                  | l     # long
--  >                  | m     # unsigned long
--  >                  | x     # long long
--  >                  | y     # unsigned long long
--  >                  | f     # float
--  >                  | d     # double
--  >                  | z     # ellipsis
builtinType :: BuiltinType -> Text
builtinType TyU64 = "y"
builtinType TyU32 = "j"
builtinType TyU16 = "t"
builtinType TyU8 = "h"
builtinType TyS64 = "x"
builtinType TyS32 = "i"
builtinType TyS16 = "s"
builtinType TyS8 = "a"
builtinType TyBool = "b"
