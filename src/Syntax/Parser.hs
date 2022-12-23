{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Syntax.Parser where

import Control.Monad.Writer (MonadWriter)
import Data.List (intercalate)
import qualified Data.List.NonEmpty as NonEmpty
import Error.Diagnose (Diagnostic, Position (..))
import Located (Located (..), getPos, unLoc)
import qualified Syntax.CST as CST
import Syntax.Errors
import Syntax.Tokens (Token, showToken)
import qualified Text.Megaparsec as MP

type MonadParser m = (MonadWriter [ParsingWarning] m, MP.MonadParsec ParsingError [Located Token] m, MonadFail m)

instance MP.VisualStream [Located Token] where
  showTokens _ = commaSeparated . fmap (showToken . unLoc) . NonEmpty.toList
    where
      commaSeparated :: [String] -> String
      commaSeparated l = intercalate ", " $ filter (/= "") l

instance MP.TraversableStream [Located Token] where
  reachOffsetNoLine o MP.PosState {..} =
    let (_, after) = splitAt (o - pstateOffset) pstateInput

        actualisePos pos Nothing = pos
        actualisePos _ (Just (Position (bLine, bCol) _ file)) =
          MP.SourcePos
            { MP.sourceName = file,
              MP.sourceColumn = MP.mkPos bCol,
              MP.sourceLine = MP.mkPos bLine
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

------------------------------------------------------------------------

-- | Transforms a simple parser into a parser returning a located value.
located :: forall m a. MonadParser m => m a -> m (Located a)
located p = do
  MP.SourcePos file beginLine beginColumn <- MP.getSourcePos
  MP.State input0 offset0 _ _ <- MP.getParserState
  -- NOTE: we need to fetch the input stream before, because it is not complete
  -- (it does not necessarily contain all tokens at once).

  res <- p

  MP.State _ offset _ _ <- MP.getParserState
  let Position _ (endLine, endColumn) _ = getPos $ input0 !! (offset - 1 - offset0)

  -- NOTE: We need to fetch the last token parsed, which is located right before the
  --       currently available token.
  --       Thankfully, our tokens have their locations, so we can use the ending location
  --       of the previous token to get the ending location of the result of our parser @p@.

  let pos =
        Position
          (fromIntegral $ MP.unPos beginLine, fromIntegral $ MP.unPos beginColumn)
          (endLine, endColumn)
          file

  pure $ res :@ pos

------------------------------------------------------------------------

runParser :: FilePath -> [Located Token] -> Either (Diagnostic String) (Located CST.Module, Diagnostic String)
runParser path tokens = undefined
