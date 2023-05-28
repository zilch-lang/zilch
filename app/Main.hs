{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Main() where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Located_Internal;
import qualified Diagnose_Internal;
import qualified Filter;
import qualified HOL;
import qualified Typerep;

instance (Typerep.Typerep a) => Typerep.Typerep (Filter.Filter a) where {
  typerep = Filter.typerep_filter;
};

}
