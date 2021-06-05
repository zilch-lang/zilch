module LexerSpec (spec) where

import Test.Hspec
import Language.Zilch.Syntax.Lexer (runLexer)
import Data.Either (fromRight)
import Common

spec :: Spec
spec = parallel do
  emptyStream
  spaceStream

-------------------------------------------------------------------------

specFilename :: String
specFilename = "<test>"
{-# INLINE specFilename #-}

emptyStream :: Spec
emptyStream = describe "on an empty stream" do
  let result = runLexer "" specFilename
  it "successfully runs" do
    succeeds result (specFilename, "")
  it "generates no lexeme" do
    right result `shouldBe` []

spaceStream :: Spec
spaceStream = describe "on an invisible stream" do
  let content = "     \t\r    \v"
  let result = runLexer content specFilename
  it "successfully runs" do
    succeeds result (specFilename, content)
  it "generates no lexeme" do
    right result `shouldBe` []
