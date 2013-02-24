import Prelude hiding (foldr)
import Control.Applicative
import Control.Arrow
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
  
class Recursive r where
  recur :: (a -> b) -> (b -> b -> b) -> r a -> b

instance Recursive Expr where
  recur f g (App x y) = g (recur f g x) (recur f g y)
  recur f _ (Data a) = f a

expr :: (a -> String) -> Expr a -> String
expr showA = recur showA (\x y -> "(" ++ x ++ " " ++ y ++ ")")

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
ski2lambda = apply . fmap replace

replace :: CompSKI -> Lambda
replace S = 
  Lam 1 (Lam 2 (Lam 3 (LamExpr (App
                                (App (Data $ LamValue 1) (Data $ LamValue 3))
                                (App (Data $ LamValue 2) (Data $ LamValue 3))))))
replace K = Lam 1 (Lam 2 (LamExpr (Data $ LamValue 1)))
replace I = Lam 1 (LamExpr (Data $ LamValue 1))

apply :: Expr Lambda -> Lambda
apply = concatExpr . alphaSimple . beta . alphaNumber

alphaNumber :: Expr Lambda -> Expr Lambda
alphaNumber = fst . alpha True 1 1

alphaSimple :: Expr Lambda -> Expr Lambda
alphaSimple = fst . alpha False 1 1

alpha :: Bool -> Int -> Int -> Expr Lambda -> (Expr Lambda, Int)
alpha isN n _ (App x y) = (App x' y', n'')
  where
    (x', n') = alpha isN n 1 x
    (y', n'') = alpha isN n' n' y
alpha isN n s (Data x) = (Data dat, n')
  where
    (dat, n') = number s [n-1..] x
    
    pick :: a -> a -> a
    pick a b = if isN then a else b
    
    number :: Int -> [Int] -> Lambda -> (Lambda, Int)
    number m dic (Lam l ls) = first (Lam (dic !! pick l m)) $ number (m+1) dic ls
    number m dic (LamExpr e) = first LamExpr $ numberExpr (pick (m+1) 1) dic e
    number _ _ _ = undefined
    
    numberExpr :: Int -> [Int] -> Expr Lambda -> (Expr Lambda, Int)
    numberExpr n dic (App x y) = (App x' y', n'')
      where
        (x', n') = numberExpr n dic x
        (y', n'') = numberExpr n' dic y
    numberExpr n dic (Data (LamValue x)) = (Data $ LamValue (dic !! pick x n), n)
    numberExpr n dic (Data x) = first Data $ number n dic x

concatExpr :: Expr Lambda -> Lambda
concatExpr (Data x) = x
concatExpr _ = undefined

beta :: Expr Lambda -> Expr Lambda
beta (App (Data x) (Data y)) = Data (y `subst` x)
  where
    subst :: Lambda -> Lambda -> Lambda
    subst x (Lam n ns) = x `substExpr` ns $ n
    subst _ _ = undefined
    
    substExpr :: Lambda -> Lambda -> Int -> Lambda
    substExpr x (LamExpr e) n = LamExpr $ update x n e
    substExpr x (Lam m ms) n = Lam m (substExpr x ms n)
    substExpr _ _ _ = undefined
    
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
aLambda = Lam 1 (Lam 2 (Lam 3 (LamExpr (App
                                (App (Data $ LamValue 1) (Data $ LamValue 3))
                                (App (Data $ LamValue 2) (Data $ LamValue 3))))))

main = putStrLn $ lambda $ ski2lambda aSKI
