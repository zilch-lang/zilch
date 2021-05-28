{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}

module Language.Zilch.Syntax.Internal where

import qualified Text.Megaparsec as MP
import Text.Diagnose (Diagnostic, Report, Marker(..), Hint, hint, Position(..), reportError, (<++>), diagnostic)
import qualified Data.Set as Set
import Data.Bifunctor (bimap, second)

-- | Transforms a megaparsec's 'MP.ParseErrorBundle' into a well formated 'Diagnostic'.
megaparsecBundleToDiagnostic :: (MP.Stream s, Show e, MP.ShowErrorComponent e, MP.TraversableStream s, MP.VisualStream s)
                             => String -> MP.ParseErrorBundle s e -> Diagnostic s2 String a
megaparsecBundleToDiagnostic msg MP.ParseErrorBundle{..} =
  foldl (<++>) diagnostic (toLabeledPositions <$> bundleErrors)
 where toLabeledPositions :: (MP.Stream s, Show e, MP.ShowErrorComponent e, MP.TraversableStream s, MP.VisualStream s)
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

       errorHints :: (MP.Stream s, Show e) => MP.ParseError s e -> [Hint String]
       errorHints MP.TrivialError{}      = []
       errorHints (MP.FancyError _ errs) = Set.toList errs >>= \case
         MP.ErrorCustom e -> [hint $ show e]
         _                -> mempty

       both f = bimap f f
