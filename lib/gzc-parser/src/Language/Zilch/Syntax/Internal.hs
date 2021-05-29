{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Zilch.Syntax.Internal where

import qualified Text.Megaparsec as MP
import Text.Diagnose (Diagnostic, Report, Marker(..), Hint, Position(..), reportError, (<++>), diagnostic)
import qualified Data.Set as Set
import Data.Bifunctor (bimap, second)
import Language.Zilch.Core.Tokens (LToken)
import qualified Data.IndentLocated as IL (unwrapLocated, position)
import qualified Data.List.NonEmpty as NE
import Language.Zilch.Pretty.Tokens (pretty)

-- | Transforms a megaparsec's 'MP.ParseErrorBundle' into a well formated 'Diagnostic'.
megaparsecBundleToDiagnostic :: (MP.Stream s, MP.ShowErrorComponent e, MP.TraversableStream s, MP.VisualStream s, Hintable e)
                             => String -> MP.ParseErrorBundle s e -> Diagnostic s2 String a
megaparsecBundleToDiagnostic msg MP.ParseErrorBundle{..} =
  foldl (<++>) diagnostic (toLabeledPositions <$> bundleErrors)
 where toLabeledPositions :: (MP.Stream s, Hintable e, MP.ShowErrorComponent e, MP.TraversableStream s, MP.VisualStream s)
                          => MP.ParseError s e -> Report String
       toLabeledPositions err =
         let (_, pos) = MP.reachOffset (MP.errorOffset err) bundlePosState
             !source  = fromSourcePos (MP.pstateSourcePos pos)
             msgs     = lines (MP.parseErrorTextPretty err)
         in flip (reportError msg) (errorHints err)
            if | [m] <- msgs      -> [ (source, This m) ]
               | [m1, m2] <- msgs -> [ (source, This m1), (source, Where m2) ]
               | otherwise        -> [ (source, This "Unknown error") ]

       fromSourcePos MP.SourcePos{..} =
         let start = both (fromIntegral . MP.unPos) (sourceLine, sourceColumn)
             end   = second (+ 1) start
         in Position start end sourceName

       errorHints :: (MP.Stream s, Hintable e) => MP.ParseError s e -> [Hint String]
       errorHints MP.TrivialError{}      = []
       errorHints (MP.FancyError _ errs) = Set.toList errs >>= \case
         MP.ErrorCustom e -> hints e
         _                -> mempty

       both f = bimap f f

-- | A type class for errors supporting diagnostic hints.
class Hintable e where
  hints :: e -> [Hint String]

-------------------------------------------------------------------------------------------------

instance MP.VisualStream [LToken] where
  showTokens _ tokens = unwords . NE.toList $ show . pretty . IL.unwrapLocated <$> tokens

instance MP.TraversableStream [LToken] where
  reachOffsetNoLine o MP.PosState{..} =
    let (_, after) = splitAt (o - pstateOffset) pstateInput

        currentTokenPosition = case after of
          []  -> Nothing
          t:_ -> Just (IL.position t)

        calculateNewPosition p Nothing  = p
        calculateNewPosition _ (Just p) =
          let (Position (bLine, bCol) _ file) = p
          in MP.SourcePos
                { MP.sourceName   = file
                , MP.sourceLine   = MP.mkPos $ fromIntegral bLine
                , MP.sourceColumn = MP.mkPos $ fromIntegral bCol
                }
    in MP.PosState
        { MP.pstateInput      = after
        , MP.pstateOffset     = max o pstateOffset
        , MP.pstateSourcePos  = calculateNewPosition pstateSourcePos currentTokenPosition
        , MP.pstateTabWidth   = pstateTabWidth
        , MP.pstateLinePrefix = pstateLinePrefix
        }
