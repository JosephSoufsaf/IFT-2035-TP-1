module Main where

import Data.List
import Data.Char
import Control.Monad.Trans
import System.Console.Haskeline
import Text.ParserCombinators.Parsec
import Control.Arrow

import Parseur
import Eval


mapLeft :: (a -> b) -> Either a c -> Either b c
mapLeft f (Left x) = Left $ f x
mapLeft _ (Right x) = Right x

run :: String -> Either Error (Value, Type)
run sourceCode = do
  sexp <- mapLeft show (parse pOneSexp "" sourceCode)
  exp <- sexp2Exp sexp
  t <- typeCheck tenv0 exp
  let v = eval env0 exp
  return (v, t)



runIO :: String -> IO ()
runIO line =
  case run line of
    Left err -> print err
    Right (v, t) -> do
      putStrLn (show v ++ " :: " ++ show t)
      return ()

-- Lit un fichier de Sexps
-- Chaque sexp contient deux sous exp
-- Les deux sont évaluées séparémment le résultat doit être identique
-- Lorsque la 2e Sexp a pour mot clé Erreur, alors la première doit
-- retourner une erreur
unittests :: String -> IO ()
unittests file = do
  lines <- readFile file
  case parse pManySexp "" lines of
    Left err -> print err
    Right sexps -> do
      let res = map runtest sexps
      let nbGood = foldl (\i r -> case r of {Left _ -> i; Right False -> i;
                                            Right True -> i + 1}) 0 res
      let size = length res
      let nbBad = size - nbGood

      -- Show results
      mapM_ (uncurry showResult) (zip [1..] res)
      putStrLn ("Ran " ++ show size ++ " unittests. " ++ show nbGood
                ++ " OK and "
                ++ show nbBad ++ " KO.")

  where runtest :: Sexp -> Either Error Bool
        -- Cas où l'on s'attend à une Erreur
        runtest (SList [test, SSym "Erreur"]) =
          let x = do
                exp <- sexp2Exp test
                typeCheck tenv0 exp
          in case x of
               Left _ -> Right True
               Right _ -> Right False

        -- Cas où l'on compare deux résultats
        runtest (SList [test, solution]) = do
          exp <- sexp2Exp test
          t <- typeCheck tenv0 exp
          let v = eval env0 exp

          expSol <- sexp2Exp solution
          tSol <- typeCheck tenv0 expSol
          let vSol  = eval env0 expSol

          return $ v == vSol

        runtest _ = Left "Ill formed unittest Sexp"

        showResult :: Int -> Either Error Bool -> IO ()
        showResult i (Left err) = putStrLn $ "Test " ++ show i ++ ": " ++ err
        showResult _ (Right True) = return ()
        showResult i (Right False) = putStrLn $ "Test " ++ show i ++ " failed"

-- REPL : Read Eval Print Loop
-- Vous permet d'évaluer des expressions à l'aide de GHCi,
-- l'interpréteur de Haskell qui vient avec la Haskell Platform
-- Pour quitter le mode MiniHaskell, vous devez entrer :q
repl :: IO ()
repl = runInputT defaultSettings loop
  where
  loop = do
    input <- getInputLine "MiniHaskell> "
    case input of
      Nothing -> outputStrLn "Leaving Mini Haskell"
      Just input | trim input == ":q" -> outputStrLn "Leaving Mini Haskell"
      Just input -> liftIO (runIO input) >> loop

  trim = dropWhileEnd isSpace . dropWhile isSpace
main = repl
