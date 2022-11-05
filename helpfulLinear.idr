import LinearLib

import Control.Linear.LIO
import Prelude.Num
import Data.Fin
import Data.Nat
import Data.Vect
import Data.List

{-getIndexLTE : (toWrite : Int) -> (index : Nat) -> 
                {auto prf : LTE (S index) size} -> 
                (1 mem : (MyVect size)) -> 
                L IO {use=1} (MyVect size)
getIndexLTE toWrite index arr  = writeArr toWrite (natToFinLT index) arr-}


doList : (l : List ((MyVect size) -> L IO (MyVect size))) -> (MyVect size) -> L IO {use=1} (MyVect size)
doList [] x = pure1 x
doList (f :: fs) x = (f x) >>= (doList fs)



update : (Int -> Int) -> (Fin size) -> (1 _ : MyVect size) -> L IO {use=1} (MyVect size)
update f index arr = do
                val # arr <- getIndex index arr
                writeArr (f val) index arr

vec' : (Int -> Int) -> (Fin size) -> (1 _ : MyVect size) -> L IO {use=1} (MyVect size)
vec' f FZ arr = update f FZ arr
vec' f (FS x) arr = do
                arr <- update f (FS x) arr
                vec' f (weaken x) arr

vecMap : {size : Nat} -> (Int -> Int) -> (1 _ : MyVect (S size)) -> L IO {use=1} (MyVect (S size))
vecMap f a = vec' f last a


vecToArr' : (Fin size) -> (Vect size Int) -> (1 _ : MyVect size) -> L IO {use=1} (MyVect size)
vecToArr' FZ vec arr = writeArr (index FZ vec) (FZ) arr
vecToArr' (FS x) vec arr = do
                        arr <- writeArr (index (FS x) vec) (FS x) arr
                        vecToArr' (weaken x) vec arr

vecToArr : (size : Nat) -> (Vect (S size) Int) -> L IO {use=1} (MyVect (S size))
vecToArr k vect = do
                x <- createArr k
                vecToArr' (last) vect x

                

lengthNonZero : (l : List Int) -> (NonEmpty l) -> (NonZero (length l))
lengthNonZero [] x impossible
lengthNonZero (y :: xs) x = SIsNonZero
 

arrToList' : (Fin size) -> (1 _ : MyVect size) -> L IO (List Int)
arrToList' FZ arr = do
                (val # arr) <- getIndex FZ arr
                freeArr arr
                pure [val]
arrToList' (FS x) arr = do
                (head # arr) <- getIndex (FS x) arr
                tail <- arrToList' (weaken x) arr
                pure (head :: tail)

 

arrToList : {size : Nat} -> (1 _ : MyVect (S size)) -> L IO (List Int)
arrToList arr = do
                x <- (arrToList' last arr)
                pure (reverse x)

{-
main : IO ()
main = runLin $ do
        x <- vecToArr 2 [142,3,4]
        val <- arrToList x
        print val-}