{- Three ideas for safe low-level programming in Idris -}

{- 1. safe vector lookup -}

import Data.Nat

data Vec : Type -> Nat -> Type where
  Nil : Vec a 0
  Cons : a -> Vec a n -> Vec a (S n)

data Lt : Nat -> Nat -> Type where
  LtZero : Lt 0 (S r)
  LtSucc : Lt l r -> Lt (S l) (S r)

nth : (n : Nat) -> {p : Lt n m} -> Vec a m    -> a
nth   0            {p=LtZero}      (Cons x _)  = x
nth   (S n)        {p=LtSucc lt}   (Cons _ xs) = nth n {p=lt} xs


{- 2. quantitative types for resources -}

data Mem : Type

alloc : Nat -> (1 mem :  Mem -> IO ()) -> IO ()
alloc n k = ?

read : (1 mem : Mem) -> Nat -> ((1 mem : Mem) -> Nat -> IO ()) -> IO ()
read mem n k = ?

write : (1 mem : Mem) -> Nat -> Nat -> ((1 mem : Mem) -> IO ()) -> IO ()
write mem n m k = ?

free : (1 mem : Mem) -> IO ()
free mem = ?

{- 3. codes for structs -}

data Code : Type where
  CInt : Code
  CBool : Code
  CPair : Code -> Code -> Code

code2type : Code -> Type
code2type CInt = Int
code2type CBool = Bool 
code2type (CPair x y) = (code2type x, code2type y)
