
-- S = λxyz.(x z)(y z)
-- K = λxy.x
-- I = λx.x

import Prelude hiding (foldr)
import Control.Applicative
import Data.Foldable

data Expr a = App (Expr a) (Expr a) | Data a

data CompSKI = S | K | I
type SKI = Expr CompSKI

data LamExpr a = Lam a (LamExpr a) | 
                 LamExpr (Expr (LamExpr a)) | LamValue a
type Lambda = LamExpr Int

instance Functor Expr where
  fmap f (App x y) = App (fmap f x) (fmap f y)
  fmap f (Data x) = Data (f x)

instance Monad Expr where
  Data x >>= f = f x
  App x y >>= f = App (x >>= f) (y >>= f)
  return x = Data x
 
instance Functor LamExpr where
  fmap f (Lam x xs) = Lam (f x) (fmap f xs)
  fmap f (LamValue x) = LamValue (f x)
  fmap f (LamExpr x) = LamExpr (x >>= return . fmap f)

instance Foldable Expr where
  foldr f z (App x y) = foldr f (foldr f z y) x
  foldr f z (Data x) = f x z

expr :: (a -> String) -> Expr a -> String
expr showA (App x y) = "(" ++ expr showA x ++ 
                       " " ++ expr showA y ++ ")" 
expr showA (Data a) = showA a

lambda :: Lambda -> String
lambda (Lam x y) = "λx" ++ show x ++ "." ++ lambda y
lambda (LamExpr e) = expr lambda e
lambda (LamValue n) = "x" ++ show n

ski :: SKI -> String
ski (App x y) = "(" ++ ski x ++ ski y ++ ")"
ski (Data S) = "S"
ski (Data K) = "K"
ski (Data I) = "I"

ski2lambda :: SKI -> Lambda
ski2lambda = apply . replace

replace :: SKI -> Expr Lambda
replace x = x >>= skiReplace
  where
    skiReplace :: CompSKI -> Expr Lambda
    skiReplace S = Data (
      Lam 1 (Lam 2 (Lam 3 (LamExpr (App
                                    (App (Data $ LamValue 1) (Data $ LamValue 3))
                                    (App (Data $ LamValue 2) (Data $ LamValue 3)))))))
    skiReplace K = Data (Lam 1 (Lam 2 (LamExpr (Data $ LamValue 1))))
    skiReplace I = Data (Lam 1 (LamExpr (Data $ LamValue 1)))

apply :: Expr Lambda -> Lambda
apply = concatExpr . alphaSimple . beta . alphaNumber

alphaNumber :: Expr Lambda -> Expr Lambda
alphaNumber = fst . alphaNum 1 1

alphaNum :: Int -> Int -> Expr Lambda -> (Expr Lambda, Int)
alphaNum n s (App x y) = (App x' y', n'')
  where
    (x', n') = alphaNum n 1 x
    (y', n'') = alphaNum n' n' y
alphaNum n s (Data x) = (Data dat, n')
  where
    (dat, n') = number s [n-1..] x
    
    number :: Int -> [Int] -> Lambda -> (Lambda, Int)
    number m dic (Lam l ls) = (Lam (dic !! l) lam, m')
      where
        (lam, m') = number (m+1) dic ls
    number m dic (LamExpr e) = (LamExpr exp, m)
      where
        (exp, m') = numberExpr (m+1) dic e
    
    numberExpr :: Int -> [Int] -> Expr Lambda -> (Expr Lambda, Int)
    numberExpr n dic (App x y) = (App x' y', n'')
      where
        (x', n') = numberExpr n dic x
        (y', n'') = numberExpr n' dic y
    numberExpr n dic (Data (LamValue x)) = (Data $ LamValue (dic !! x), n)
    numberExpr n dic (Data x) = (Data $ x', n')
      where
        (x', n') = number n dic x

alphaSimple :: Expr Lambda -> Expr Lambda
alphaSimple = fst . alphaNum' 1 1

alphaNum' :: Int -> Int -> Expr Lambda -> (Expr Lambda, Int)
alphaNum' n s (App x y) = (App x' y', n'')
  where
    (x', n') = alphaNum' n 1 x
    (y', n'') = alphaNum' n' n' y
alphaNum' n s (Data x) = (Data dat, n')
  where
    (dat, n') = number s [n-1..] x
    
    number :: Int -> [Int] -> Lambda -> (Lambda, Int)
    number m dic (Lam l ls) = (Lam (dic !! m) lam, m')
      where
        (lam, m') = number (m+1) dic ls
    number m dic (LamExpr e) = (LamExpr exp, m)
      where
        (exp, m') = numberExpr 1 dic e
    
    numberExpr :: Int -> [Int] -> Expr Lambda -> (Expr Lambda, Int)
    numberExpr n dic (App x y) = (App x' y', n'')
      where
        (x', n') = numberExpr n dic x
        (y', n'') = numberExpr n' dic y
    numberExpr n dic (Data (LamValue x)) = (Data $ LamValue (dic !! n), n)
    numberExpr n dic (Data x) = (Data $ x', n')
      where
        (x', n') = number n dic x

concatExpr :: Expr Lambda -> Lambda
concatExpr (Data x) = x
concatExpr _ = undefined

beta :: Expr Lambda -> Expr Lambda
beta (App (Data x) (Data y)) = Data (y `subst` x)
  where
    subst :: Lambda -> Lambda -> Lambda
    subst x (Lam n ns) = x `substExpr` ns $ n
    subst x _ = undefined
    
    substExpr :: Lambda -> Lambda -> Int -> Lambda
    substExpr x (LamExpr e) n = LamExpr $ update x n e
    substExpr x (Lam m ms) n = Lam m (substExpr x ms n)
    substExpr x _ n = undefined
    
    update :: Lambda -> Int -> Expr Lambda -> Expr Lambda
    update lam n (App x y) = beta $ App (update lam n x) (update lam n y)
    update lam n (Data (LamValue x)) = Data $ if n == x then lam
                                              else LamValue x
    update lam n (Data x) = Data $ lam `substExpr` x $ n
beta (App x y) = beta $ App (beta x) (beta y)
beta x = x

aSKI :: SKI
aSKI = App (App (Data S) (Data K)) (Data K)

aLambda :: Lambda
aLambda = Lam 1 (Lam 2 (LamExpr (App (Data $ LamValue 1) (Data $ LamValue 2))))

main = putStrLn $ lambda . ski2lambda $ aSKI
-- ((SK)K)
-- ((λx1.λx2.λx3.((x1 x3) (x2 x3)) λx4.λx5.x4) λx6.λx7.x6)
-- λx1.x1
