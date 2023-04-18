import LinearLibPoly9
import Control.Linear.LIO
import Prelude.Num
import Data.Fin
import Data.Nat

import Data.Vect


finish : (1 mem : IntArray size isParent self) -> Bool -> L IO {use=1} (SemiLinPair Bool (IntArray size isParent self))
finish arr b = pure1 $ b *? arr

export
div2 : Nat -> Nat
div2 0 = 0
div2 (S 0) = 0
div2 (S (S k)) = S (div2 k)


%transform "div2" div2 j = integerToNat (div (natToInteger j)  2)

data PPair : (a : Type) -> (P : a -> Type) -> Type where
   MakePPair : {P : a -> Type} -> (x : a) -> (0 _ : P x) -> PPair a P

data ErasedProof : Type -> Type where
    MkProof : (0 _ : a) -> ErasedProof a

addBasic : (lp : Nat) -> (rp : Nat) -> LT (lp) rp -> LT ((lp + rp)) (plus rp rp)
addBasic lp rp x = plusLteMonotoneRight rp (S lp) rp x

addDub : {size : Nat} -> {rp : Nat} -> (LTE (rp) (S size)) -> LTE (rp + rp) ((S size) + (S size))
addDub x = let x2 = plusLteMonotoneRight (S size) (rp) (S size) x in
           let x3 = plusLteMonotoneLeft (rp) (rp) (S size) x in
           transitive x3 x2

plus1 : (size : Nat) -> (lp : Nat) -> (rp : Nat) -> (0 _ : LTE (S lp) rp) -> (0 _ : LTE (rp) (S size)) -> PPair Nat (\m1 => LTE (S m1) ((S size) + (S size)))
plus1 size lp rp x y = let (MkProof x4) : (ErasedProof (LTE (S (lp + rp)) ((S size) + (S size)))) = MkProof 
                                (let x2 : (LTE (S (lp + rp)) (rp + rp)) = addBasic lp rp x in 
                                let x3 : (LTE (rp + rp) ((S size) + (S size))) = addDub y in 
                                transitive x2 x3) in
                      (MakePPair (plus lp rp) x4)

divFinal : {a : Nat} -> {b : Nat} -> (LT ((a + a)) (b + b)) -> (LT a b)
divFinal {a = 0} {b = 0} x = x
divFinal {a = 0} {b = (S k)} x = LTESucc LTEZero
divFinal {a = (S k)} {b = 0} x impossible
divFinal {a = (S k)} {b = (S j)} x = let x2 = fromLteSucc x in
                                     let x3 = replace {p=(\x => LTE (S (plus k (S k))) x)} (sym (plusSuccRightSucc j j)) x2 in
                                     let x4 = fromLteSucc x3 in 
                                     let x5 = replace {p=(\x => LTE x (plus j j))} (sym (plusSuccRightSucc k k)) x4 in 
                                     let x5 = divFinal x5 in LTESucc x5

rtp : (a : Nat) -> (LTE (2 * (div2 a)) a)
rtp (0) = LTEZero
rtp ((S 0)) = LTEZero
rtp ((S (S k))) = let rec = rtp {a=k} in 
                    rewrite sym (plusSuccRightSucc (div2 k) (plus (div2 k) 0)) in 
                        LTESucc (LTESucc rec)

divoddeven : (a : Nat) -> (b : Nat) -> (0 _ : LT a (b + b)) -> ErasedProof (LT (div2 a) b)
divoddeven a b x = MkProof $ let x1 = LTESucc (rtp {a=a}) in
                    let x2 = (transitive x1 x) in
                    let x4 = replace {p=(\x => LTE (S (plus (div2 a) x)) (plus b b))} (plusZeroRightNeutral (div2 a)) x2 in
                    divFinal x4

div2WithPrf' : (size : Nat) -> (m1 : Nat) -> (0 _ : LTE (S m1) (size + size)) -> PPair Nat (\mid => LTE (S mid) (size))
div2WithPrf' size m1 x = let (MkProof prf) = divoddeven m1 size x in MakePPair (div2 m1) (prf)


div2WithPrf : (size : Nat) -> (m1 : Nat) -> (0 _ : LTE (S m1) ((S size) + (S size))) -> PPair Nat (\mid => LTE (S mid) (S size))
div2WithPrf size m1 x = div2WithPrf' (S size) m1 x


succRem : (0 _ : LTE (S mid) (S size)) -> ErasedProof (LTE (mid) (size))
succRem (LTESucc x) = MkProof x

lteSuccLeft' : (0 _ : LTE (S mid) (S size)) -> ErasedProof (LTE (mid) (S size))
lteSuccLeft' x = MkProof $ lteSuccLeft x

succBoth : (0 _ : LTE (S mid) (S size)) -> ErasedProof (LTE mid size)
succBoth (LTESucc x) = MkProof x

binSearch'' : {size : Nat} -> (lp : Nat) -> (rp : Nat) -> (item : Int) ->
                     (1 mem : IntArray (S size) isParent self ) -> 
                     {auto 0 p2 : LTE (rp) (S size)} -> 
                     {auto 0 p3 : LTE (S lp) rp} -> 
                     L IO {use=1} (SemiLinPair Bool (IntArray (S size) isParent self ))
binSearch'' {size} lp rp item arr = 
                                let (MakePPair m1 prf1) = plus1 size lp rp p3 p2 in
                                let (MakePPair mid prf2) = div2WithPrf size m1 prf1 in 
                                let (MkProof prf'') = succBoth prf2 in
                                let (MkProof x) = lteSuccLeft' prf2 in do
                                val *? arr <- readIntArrayPrf mid arr
                                case compare item val of 
                                    LT => case choose (lp < mid) of
                                        Left x => let _ = ltOpReflectsLT lp mid x in  binSearch'' lp mid item (arr)
                                        Right _ => finish arr False
                                    EQ => finish arr True
                                    GT => case choose ((S mid) < rp) of 
                                        Left x => let y = ltOpReflectsLT (S mid) rp x in 
                                                        binSearch'' (S mid) rp item (arr)
                                        Right _ => finish arr False


lteRefl : (size : Nat) -> (LTE size size)
lteRefl Z = LTEZero
lteRefl (S n) = LTESucc (lteRefl n)

binSearch : {size : Nat} -> (item : Int) -> (1 _ : IntArray (S size) isParent self) -> L IO {use=1} (SemiLinPair Bool (IntArray (S size) isParent self))
binSearch item arr = let prf = lteRefl (S size) in 
                                    binSearch'' 0 (S size) item arr
                                    

{-
main : IO ()
main = runLin $ do
        x <- vecToArr _ ([1, 6, 17, 19, 20, 25,100])
        val <- binSearch (100) x
        print val
-}

{-mutual
    divSmaller : (x : Nat) -> {auto _ : (NonZero x)} -> LTE (S (div2 x)) x
    divSmaller 0 impossible
    divSmaller (S 0) = LTESucc LTEZero
    divSmaller (S (S k)) = let rec = fromLteSucc (divSmaller (S k)) in      
                            let rec2 = removeSucc k rec in LTESucc (LTESucc rec2)

    removeSucc : (k : Nat) -> LTE (div2 (S k)) k -> LTE (div2 k) k
    removeSucc 0 x = x
    removeSucc (S 0) x = LTEZero 
    removeSucc (S (S k)) x = let rec = fromLteSucc (divSmaller (S k)) in
                                let rec2 = removeSucc k rec in
                                    let rec3 = (LTESucc rec2) in lteSuccRight rec3-}