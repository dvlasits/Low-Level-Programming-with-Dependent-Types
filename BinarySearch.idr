import LinearLib
import HelpfulLinear
import Control.Linear.LIO
import Prelude.Num
import Data.Fin
import Data.Nat

import Data.Vect


finish : (1 mem : MyVect size) -> Bool -> L IO Bool
finish arr b = do
            freeArr arr
            pure b

export
div2 : Nat -> Nat
div2 0 = 0
div2 (S 0) = 0
div2 (S (S k)) = S (div2 k)


divLinear : (LTE x y) -> (LTE (div2 x) (div2 y))
divLinear LTEZero = LTEZero
divLinear (LTESucc LTEZero) = LTEZero
divLinear (LTESucc (LTESucc z)) = LTESucc (divLinear z)



divhalves : (size : Nat) -> div2 (plus size size) = size
divhalves 0 = Refl
divhalves (S 0) = Refl
divhalves (S (S k)) = rewrite sym (plusSuccRightSucc k (S k)) in 
                        rewrite sym (plusSuccRightSucc k k) in 
                            rewrite divhalves k in Refl


sub : Nat -> Nat -> Nat
sub Z x = x
sub (S k) (S x) = sub k x
sub (S k) Z = Z 


addBasic : {lp : Nat} -> {rp : Nat} -> LT (lp) rp -> LT ((lp + rp)) (plus rp rp)
addBasic {lp} {rp} x = plusLteMonotoneRight rp (S lp) rp x

addDub : {size : Nat} -> {rp : Nat} -> (LTE (rp) (S size)) -> LTE (rp + rp) ((S size) + (S size))
addDub x = let x2 = plusLteMonotoneRight (S size) (rp) (S size) x in
           let x3 = plusLteMonotoneLeft (rp) (rp) (S size) x in
           transitive x3 x2



plus1 : {lp : Nat} -> {rp : Nat} -> {size : Nat} -> LTE (S lp) rp -> LTE (rp) (S size) -> (m1 : Nat ** LTE (S m1) ((S size) + (S size)))
plus1 {lp} {rp} x y = let x2 : (LTE (S (lp + rp)) (rp + rp)) = addBasic x in 
                      let x3 : (LTE (rp + rp) ((S size) + (S size))) = addDub y in 
                      let x4 : (LTE (S (lp + rp)) ((S size) + (S size))) = transitive x2 x3  in
                      ((lp + rp) ** x4)



rtp :{a : Nat} -> LTE (2 * (div2 a)) a
rtp {a = 0} = LTEZero
rtp {a = (S 0)} = LTEZero
rtp {a = (S (S k))} = let rec = rtp {a=k} in 
                    rewrite sym (plusSuccRightSucc (div2 k) (plus (div2 k) 0)) in 
                        LTESucc (LTESucc rec)



divFinal : {a : Nat} -> {b : Nat} -> (LT ((a + a)) (b + b)) -> (LT a b)
divFinal {a = 0} {b = 0} x = x
divFinal {a = 0} {b = (S k)} x = LTESucc LTEZero
divFinal {a = (S k)} {b = 0} x impossible
divFinal {a = (S k)} {b = (S j)} x = let x2 = fromLteSucc x in
                                     let x3 = replace {p=(\x => LTE (S (plus k (S k))) x)} (sym (plusSuccRightSucc j j)) x2 in
                                     let x4 = fromLteSucc x3 in 
                                     let x5 = replace {p=(\x => LTE x (plus j j))} (sym (plusSuccRightSucc k k)) x4 in 
                                     let x5 = divFinal x5 in LTESucc x5

divoddeven : {a : Nat} -> {b : Nat} -> (LT a (b + b)) -> LT (div2 a) b
divoddeven {a} x = let x1 = LTESucc (rtp {a=a}) in
                    let x2 = (transitive x1 x) in
                    let x4 = replace {p=(\x => LTE (S (plus (div2 a) x)) (plus b b))} (plusZeroRightNeutral (div2 a)) x2 in
                    divFinal x4


div2WithPrf' : {m1 : Nat} -> {sizeB : Nat} -> LTE (S m1) (sizeB + sizeB) -> (mid : Nat ** LTE (S mid) (sizeB))
div2WithPrf' x = (div2 m1 ** divoddeven x)


div2WithPrf : {m1 : Nat} -> {size : Nat} -> LTE (S m1) ((S size) + (S size)) -> (mid : Nat ** LTE (S mid) (S size))
div2WithPrf {m1} {size} x = div2WithPrf' x
                            

binSearch'' : {size : Nat} -> (lp : Nat) -> (rp : Nat) -> (item : Int) ->
                     (1 mem : MyVect (S size)) -> 
                     {auto p2 : LTE (rp) (S size)} -> 
                     {auto p3 : LTE (S lp) rp} -> 
                     L IO Bool
binSearch'' {size} lp rp item arr = 
                                let (m1 ** prf1) = plus1 p3 p2 in
                                let (mid ** prf2) = div2WithPrf prf1 in
                                let x3 = lteSuccLeft prf2 in do
                                val # arr <- getIndex (natToFinLT mid) arr
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

binSearch : {size : Nat} -> (item : Int) -> (1 _ : MyVect (S size)) -> L IO Bool
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