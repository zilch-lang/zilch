import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Error.Diagnose (addFile, defaultStyle, printDiagnostic, stdout)
import Located (unLoc)
import Syntax.Lexer (runLexer)
import Syntax.Parser (runParser)
import Text.Pretty.Simple (pPrint)

main :: IO ()
main = do
  input <- Text.getContents

  let go = do
        (tokens, ws1) <- runLexer "stdin" input
        (cst, ws2) <- runParser "stdin" tokens
        pure (tokens, cst, ws1 <> ws2)

  case go of
    Left diag -> printDiagnostic stdout True True 4 defaultStyle (addFile diag "stdin" (Text.unpack input))
    Right (toks, cst, warnings) -> do
      printDiagnostic stdout True True 4 defaultStyle warnings
      pPrint $ unLoc <$> toks
      pPrint cst
