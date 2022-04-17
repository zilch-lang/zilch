{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Zilch.Syntax.Internal (located, showToken) where

import Data.List (intercalate)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Located (Located ((:@)), Position (Position), unLoc)
import qualified Data.Text as Text
import Language.Zilch.Syntax.Core (Token)
import qualified Language.Zilch.Syntax.Core as Core
import qualified Text.Megaparsec as MP

-- | Wraps the result of a parser with its starting and ending positions.
located :: (MP.MonadParsec e s m, MP.TraversableStream s) => m a -> m (Located a)
located p = do
  MP.SourcePos
    { MP.sourceName = file,
      MP.sourceLine = lineB,
      MP.sourceColumn = colB
    } <-
    MP.getSourcePos
  let !start = both (fromIntegral . MP.unPos) (lineB, colB)

  res <- p

  MP.SourcePos
    { MP.sourceName = _file,
      MP.sourceLine = lineE,
      MP.sourceColumn = colE
    } <-
    MP.getSourcePos
  let !end = both (fromIntegral . MP.unPos) (lineE, colE)

  pure (res :@ Position start end file)

-- | Applies a computation to both element of a tuple.
--
--   > both f = bimap @(,) f f
both :: (a -> b) -> (a, a) -> (b, b)
both f ~(x, y) = (f x, f y)

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
showToken Core.TkForall = "'forall'"
showToken Core.TkUniForall = "'∀'"
showToken Core.TkExists = "'exists'"
showToken Core.TkUniExists = "'∃'"
showToken Core.TkComma = "','"
showToken Core.TkUnderscore = "'_'"
showToken (Core.TkSymbol txt) = "'" <> Text.unpack txt <> "'"
showToken (Core.TkNumber txt) = "'" <> Text.unpack txt <> "'"
showToken (Core.TkCharacter txt) = "''" <> Text.unpack txt <> "''"
showToken (Core.TkString txt) = "'\"" <> Text.unpack txt <> "\"'"
showToken Core.TkEOF = "<eof>"
showToken (Core.TkInlineComment c) = "--" <> Text.unpack c
showToken (Core.TkMultilineComment c) = "/-" <> Text.unpack c <> "-/"
