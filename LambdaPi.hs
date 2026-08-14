{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE LambdaCase   #-}
{-# LANGUAGE GADTs        #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

-- | Lambda Pi reference implementation
module LambdaPi where

import Control.Exception (try, displayException)
import Control.Monad (unless)
import qualified LambdaPiCombinators as C
import Data.List (elemIndex)

data Infer
  = Ann Check Check
  | Star
  | Pi Check Check
  | Bound Int
  | Free Name
  | Infer :@: Check
  deriving (Eq, Show)  

data Check 
  = Lam Check
  | Inf Infer
  deriving (Eq, Show)


data Name
  = Global String
  | Local Int
  | Quote Int
  deriving (Eq, Show)

data Value
  = VLam (Value -> Value)
  | VStar
  | VPi Value (Value -> Value)
  | VNeutral Neutral

data Neutral
  = NFree Name
  | NApp Neutral Value

vfree :: Name -> Value
vfree = VNeutral . NFree

type Type = Value
type Context = [(Name,Type)]
type Env = [Value]

evalI :: Infer -> Env -> Value
evalI t d = case t of
  Ann e _  -> evalC e d
  Free x   -> vfree x
  Bound i  -> d !! i
  e :@: e' -> vapp (evalI e d) (evalC e' d)
  Star     -> VStar
  Pi t t'  -> VPi (evalC t d) (\x -> evalC t' (x:d))

evalC :: Check -> Env -> Value
evalC t d = case t of
  Inf i -> evalI i d
  Lam e -> VLam (\x -> evalC e (x:d))

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

substI :: Int -> Infer -> Infer -> Infer
substI i r = \case
  Ann e t  -> Ann (substC i r e) (substC i r t)
  Bound j  -> if i == j then r else Bound j
  Free y   -> Free y
  e :@: e' -> substI i r e :@: substC i r e'
  Star     -> Star
  Pi t t'  -> Pi (substC i r t) (substC (i + 1) r t')

substC :: Int -> Infer -> Check -> Check
substC i r = \case
  Inf e -> Inf (substI i r e)
  Lam e -> Lam (substC (i + 1) r e)

quote0 :: Value -> Check
quote0 = quote 0

quote :: Int -> Value -> Check
quote i (VLam f) = Lam (quote (i + 1) (f (vfree (Quote i))))
quote i (VNeutral n) = Inf (neutralQuote i n)
quote i VStar = Inf Star
quote i (VPi v f) = Inf (Pi (quote i v) (quote (i + 1) (f (vfree (Quote i)))))

neutralQuote :: Int -> Neutral -> Infer
neutralQuote i (NFree x)  = boundfree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

boundfree :: Int -> Name -> Infer
boundfree i (Quote k) = Bound (i - k - 1)
boundfree i x         = Free x

type Result = Either String

infer :: Int -> Context -> Infer -> Result Type
infer i g = \case
  Ann e r -> do
    check i g r VStar
    let t = evalC r []
    check i g e t
    pure t
  Star -> do
    pure VStar
  Pi r r' -> do
    check i g r VStar
    let t = evalC r []
    check (i + 1) ((Local i, t):g)
          (substC 0 (Free (Local i)) r') VStar
    pure VStar
  Free x -> do
    case lookup x g of
      Just t -> pure t
      Nothing -> Left "unknown identifier"
  e :@: e' -> do
    s <- infer i g e
    case s of
      VPi t t' -> do
        check i g e' t
        pure (t' (evalC e' []))
      _ -> Left "illegal application"
  
check :: Int -> Context -> Check -> Type -> Result ()
check i g e v = case e of
  Inf e -> do
    v' <- infer i g e
    unless (quote0 v == quote0 v') (Left "type mismatch")
  Lam e | VPi t t' <- v -> 
    check (i + 1) ((Local i,t):g)
          (substC 0 (Free (Local i)) e) (t' (vfree (Local i)))
  _ -> Left "type mismatch"

toCheck :: [String] -> C.Term C.Check -> Check
toCheck env (C.Inf i)   = Inf (toInfer env i)
toCheck env (C.Lam x e) = Lam (toCheck (x:env) e)

toInfer :: [String] -> C.Term C.Infer -> Infer
toInfer env (C.Var x)
  | Just i <- elemIndex x env = Bound i
  | otherwise                 = Free (Global x)
toInfer env (C.Ann e t)  = Ann (toCheck env e) (toCheck env t)
toInfer env (C.App e e') = toInfer env e :@: toCheck env e'
toInfer env C.Typ        = Star
toInfer env (C.Fun x t t') =
  Pi (toCheck env t) (toCheck (x:env) t')

toTerm0 :: Value -> C.Term C.Check
toTerm0 = toTerm 0

toTerm :: Int -> Value -> C.Term C.Check
toTerm i (VLam f) =
  C.Lam ("x" ++ show i) (toTerm (i + 1) (f (vfree (Quote i))))
toTerm i (VNeutral n) = C.Inf (neutralToTerm i n)
toTerm i VStar = C.Inf C.Typ
toTerm i (VPi v f) =
  C.Inf $
    C.Fun
      ("x" ++ show i)
      (toTerm i v)
      (toTerm (i + 1) (f (vfree (Quote i))))

neutralToTerm :: Int -> Neutral -> C.Term C.Infer
neutralToTerm i (NFree x) = freeToTerm x
neutralToTerm i (NApp n v) = C.App (neutralToTerm i n) (toTerm i v)

freeToTerm :: Name -> C.Term C.Infer
freeToTerm (Quote k) = C.Var $ "x" ++ show k
freeToTerm (Global x) = C.Var x
freeToTerm Local{} = error "Unexpected Local variable!"

parse :: String -> Either String Check
parse str = toCheck [] <$> C.parse str

showValue :: Value -> String
showValue = show . toTerm 0

main :: IO ()
main =
  let
    eval str = either id id $ do
      t <- parse str
      case t of
        Lam{} -> Left "The top-level term must be inferrable!"
        Inf e -> do
          let v = evalI e []
          t <- infer 0 [] e
          Right $
            show (toTerm0 v) <> "\n : " <> show (toTerm0 t)
    go = do
      putStr "> "
      getLine >>= \str -> do
        case str of
          ":h" -> do
            putStrLn $ "Usage: <expression> | :l <file> | :h | :q"
            go
          ":q" -> pure ()
          (words -> [":l", file]) -> do
            try (readFile file) >>=
               putStrLn . either (displayException @IOError) eval
            go
          _ -> do
            putStrLn $ eval str
            go
  in go
