{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift      #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE QuasiQuotes     #-}

module Test where

import Control.Monad (unless)
import LambdaPiCombinators hiding (main)
import Language.Haskell.TH.Syntax (Lift, Exp, Q)
import Language.Haskell.TH.Quote (QuasiQuoter(..))
import Text.ParserCombinators.ReadP
import GHC.Stack (HasCallStack, withFrozenCallStack)

import qualified LambdaPi as LPi

{-
Things to test for:

* Elaboration follows abstraction

[X]e == K c where |- e <= t ~> c

* lambda-pi matches lambda-pi-with-combinators

reinterpret lambda-pi type as term, then type == |- e <= t ~> c

(\y.(x:*) -> y) : (y:*) -> y

(\x.\y.x) : (x:*) -> (y:*) -> *

(\x.\y.y) : (x:*) -> (y:*) -> *

(\A.\y.y) : (A:*) -> (y:A) -> A

(\A.\y.*) : (A:*) -> (y:A) -> *

Use QuasiQuotes to get multi-line strings/no fiddling with backslash?

-}

deriving instance Read Combinator

comb :: QuasiQuoter
comb = qq "comb" $ \str -> case parseCombinator str of
  Left err -> fail $ "comb quasi-quoter parse error: " <> err
  Right c  -> [|c|]

{-
C := (C) | C A | A
A := any combinator that is not an application
-}

parseCombinator :: String -> Either String Combinator
parseCombinator str =
  case readP_to_S (skipSpaces *> combinatorP <* eof) str of
    [(c,"")] -> Right c
    _        -> Left "Syntax error!"

combinatorP :: ReadP Combinator
combinatorP =
  chainl1
    ((symbol "(" *> combinatorP <* symbol ")") <++ atomP)
    (pure (:@:))

atomP :: ReadP Combinator
atomP = lexeme $ do
  c <- readS_to_P (readsPrec 0)
  case c of
    _ :*: _ -> pfail
    atom    -> pure atom

-- | Test that type checking succeeds
test :: HasCallStack => Term Check -> Typ -> IO ()
test term expected = withFrozenCallStack $
  case check [] term expected of
    Left err -> error err
    Right{}  -> pure ()

-- | Test that type checking fails
failure :: HasCallStack => Term Check -> Typ -> IO ()
failure term expected = withFrozenCallStack $
  case check [] term expected of
    Left err -> pure ()
    Right{}  -> error "Expected failure!"

-- | Test that inference for LPi and LPiC satisfy:
--
--   > |- t => ty ~> c and |- t' => ty and t == [x]ty
--
--   where @t' = LPi.toInfer [] t@, and x does not occur in @ty@.
lPi :: HasCallStack => Term Infer -> IO ()
lPi term = withFrozenCallStack $
  unless (c1 =<*>= c2) $ 
    error $ unlines 
      [ "Inference mismatch:"
      , "  LPiC: " ++ show c1
      , "  LPi:  " ++ show c2
      ]
  where
    x =<*>= y = Right True == liftA2 (=*=) x y
    c1 = ty <$> infer [] term
    v2 = LPi.infer 0 [] (LPi.toInfer [] term)    
    c2 = unK . abstract "0" . LPi.toTerm0 <$> v2
    ty (t :~> _) = t
    unK (K :*: x) = x
    

main :: IO ()
main = do
  test    [lpc|*|] [typ|*|]
  test    [lpc|(x:*) -> *|] [typ|*|]
  test    [lpc|\x.x|] [typ|(x:*) -> *|]
  test    [lpc|\x.x|] [typ|(x:*) -> x|]
  failure [lpc|\y.x|] [typ|(x:*) -> x|]
  test    [lpc|\f.f *|] [typ|(f:(x:*) -> *) -> *|]
  test    [lpc|((\f.f *) : (f:(x:*) -> *) -> *) (\x.x)|] [typ|*|]
  test    [lpc|((\f.f *) : (f:(x:*) -> *) -> *)|] [typ|(f:(x:*) -> *) -> *|]
  test    [lpc|(\A.\x.x) : (A:*) -> (x:A) -> A|] [typ|(A:*) -> (x:A) -> A|]
  test    [lpc|(A : (B:*) -> *) -> A *|] [typ|*|]
  failure [lpc|(C : (B : *) -> *) -> (A : (B : *) -> *) -> A C|] [typ|*|]
  test    [lpc|(\x.x) : (((\t.(x:t) -> t) : (t : *) -> *) *)|] [typ|(x:*) -> *|]
  lPi     [lpci|*|]
  lPi     [lpci|(x:*) -> *|]      
  lPi     [lpci|(\x.x) : (((\t.(x:t) -> t) : (t : *) -> *) *)|]
  lPi     [lpci|(A : (B:*) -> *) -> A *|]
