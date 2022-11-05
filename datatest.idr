

MyPtr = Int

data Vec : (Nat) -> Type where
    Arr : (size : Nat) -> MyPtr -> Vec size


data Pair2 : Type where
    P2 : (1 _ : Nat) -> (Int) -> Pair2

--OK interestingly!
f2 : Pair2 -> (Nat, Nat)
f2 (P2 i i2) = (i, i)

--NotOK
f3 : (1 _ : Pair2) -> (Nat, Nat)
f3 (P2 i i2) = (i, i)


--OK
f : (1 _ : Pair2) -> (Int, Int)
f (P2 Z i2) = (i2, i2)
f (P2 (S z) i2) = (i2, i2)

main : IO ()
main = print 5