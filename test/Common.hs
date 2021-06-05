module Common where

import Test.Hspec
import Text.Diagnose (Diagnostic, PrettyText, prettyText, (<~<))
import Text.PrettyPrint.ANSI.Leijen (plain)
import Data.Text (Text)
import qualified Data.Text as Text

fails :: Either (Diagnostic [] String Char) b -> Expectation
fails (Left d)    = pure ()
fails (Right res) = expectationFailure "Test was expected to fail but returned a correct value."

succeeds :: Either (Diagnostic [] String Char) b -> (String, Text) -> Expectation
succeeds (Left d)  (file, ct) = expectationFailure $ "Test was expected to succeed but failed with the error:\n"
                                                  <> show (plain $ prettyText (d <~< (file, lines $ Text.unpack ct)))
succeeds (Right r) _          = pure ()

right :: Either a b -> b
right (Right x) = x

left :: Either a b -> a
left (Left x) = x
