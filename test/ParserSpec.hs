module ParserSpec (spec) where

import Test.Hspec
import Common
import qualified Language.Zilch.Core.ConcreteSyntaxTree as CST
import Language.Zilch.Syntax.Parser (runParser)

spec :: Spec
spec = parallel do
  emptyStream

-----------------------------------------------------------------------------------

specFilename :: String
specFilename = "<test>"

emptyStream :: Spec
emptyStream = describe "on an empty stream" do
  let content = []
  let result = runParser content specFilename
  it "successfully runs" do
    succeeds result (specFilename, "")
  it "generates an empty module" do
    right result `shouldBe` CST.Module Nothing [] []
