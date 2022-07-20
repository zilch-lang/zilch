{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Zilch.Syntax.Internal (showToken) where

import Data.List (intercalate)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Located (Located ((:@)), Position (Position), unLoc)
import Data.Maybe (fromMaybe)
import qualified Data.Text as Text
import Language.Zilch.Syntax.Core (Token)
import qualified Language.Zilch.Syntax.Core as Core
import qualified Text.Megaparsec as MP

instance MP.VisualStream [Located Token] where
  showTokens _ = commaSeparated . fmap (showToken . unLoc) . NonEmpty.toList

instance MP.TraversableStream [Located Token] where
  reachOffsetNoLine o MP.PosState {..} =
    let (_, after) = splitAt (o - pstateOffset) pstateInput

        actualisePos pos Nothing = pos
        actualisePos _ (Just (Position (bLine, bCol) _ file)) =
          MP.SourcePos
            { MP.sourceName = file,
              MP.sourceColumn = MP.mkPos (fromIntegral bCol),
              MP.sourceLine = MP.mkPos (fromIntegral bLine)
            }

        tokenPos = case after of
          [] -> Nothing
          (_ :@ p) : _ -> Just p

        newPos =
          MP.PosState
            { MP.pstateInput = after,
              MP.pstateOffset = max pstateOffset o,
              MP.pstateSourcePos = actualisePos pstateSourcePos tokenPos,
              MP.pstateTabWidth = pstateTabWidth,
              MP.pstateLinePrefix = pstateLinePrefix
            }
     in newPos

commaSeparated :: [String] -> String
commaSeparated l = intercalate ", " $ filter (/= "") l

-- | A prettier output for 'Token's than the corresponding derived 'Show' instance.
showToken :: Token -> String
showToken Core.TkLet = "'let'"
showToken Core.TkRec = "'rec'"
showToken Core.TkVal = "'val'"
showToken Core.TkOpen = "'open'"
showToken Core.TkEnum = "'enum'"
showToken Core.TkRecord = "'record'"
showToken Core.TkPublic = "'public'"
showToken Core.TkImport = "'import'"
showToken Core.TkAs = "'as'"
showToken Core.TkLam = "'lam'"
showToken Core.TkUniLam = "'λ'"
showToken Core.TkDo = "'do'"
showToken Core.TkColon = "':'"
showToken Core.TkColonEquals = "':='"
showToken Core.TkUniColonEquals = "'≔'"
showToken Core.TkLeftParen = "'('"
showToken Core.TkRightParen = "')'"
showToken Core.TkDoubleLeftBrace = "'{{'"
showToken Core.TkUniDoubleLeftBrace = "'⦃'"
showToken Core.TkDoubleRightBrace = "'}}'"
showToken Core.TkUniDoubleRightBrace = "'⦄'"
showToken Core.TkLeftBrace = "'{'"
showToken Core.TkRightBrace = "'}'"
showToken Core.TkDoubleColon = "'::'"
showToken Core.TkUniDoubleColon = "'∷'"
showToken Core.TkRightArrow = "'->'"
showToken Core.TkUniRightArrow = "'→'"
showToken Core.TkDoubleRightArrow = "'=>'"
showToken Core.TkUniDoubleRightArrow = "'⇒'"
showToken Core.TkForall = "'forall'"
showToken Core.TkUniForall = "'∀'"
showToken Core.TkExists = "'exists'"
showToken Core.TkUniExists = "'∃'"
showToken Core.TkComma = "','"
showToken Core.TkUnderscore = "'_'"
showToken (Core.TkSymbol txt) = "'" <> Text.unpack txt <> "'"
showToken (Core.TkNumber txt suffix) = "'" <> Text.unpack txt <> Text.unpack (fromMaybe "" suffix) <> "'"
showToken (Core.TkCharacter txt) = "''" <> Text.unpack txt <> "''"
showToken (Core.TkString txt) = "'\"" <> Text.unpack txt <> "\"'"
showToken Core.TkEOF = "<eof>"
showToken (Core.TkInlineComment c) = "--" <> Text.unpack c
showToken (Core.TkMultilineComment c) = "/-" <> Text.unpack c <> "-/"
showToken Core.TkQuestionMark = "?"
showToken Core.TkType = "'type'"
showToken Core.TkAssume = "'assume'"
showToken Core.TkTrue = "'true'"
showToken Core.TkFalse = "'false'"
showToken Core.TkIf = "'if'"
showToken Core.TkThen = "'then'"
showToken Core.TkElse = "'else'"
