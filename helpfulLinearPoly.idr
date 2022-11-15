import LinearLibPoly2

import Control.Linear.LIO
import Prelude.Num
import Data.Fin
import Data.Nat
import Data.Vect
import Data.List

data LTup : Type -> Type -> Type where
        (!!) : (1 _ : a) -> (1 _ : b) -> LTup a b

infixr 4 !!

doList : (l : List ((MyVect size a) -> L IO (MyVect size a))) -> (MyVect size a) -> L IO {use=1} (MyVect size a)
doList [] x = pure1 x
doList (f :: fs) x = (f x) >>= (doList fs)


update : (CType a, CType b) => (a -> b) -> (Fin size) -> (1 _ : MyVect size a) -> 
        (1 _ : MyVect size b) -> L IO {use=1} (LTup (MyVect size a) (MyVect size b))
update f index arr new = do
                val # old <- getIndex index arr
                new <- writeArr (f val) index new
                pure1 (old !! new)


vec' : (CType a, CType b) => (a -> b) -> (Fin size) -> (1 _ : MyVect size a) -> (1 _ : MyVect size b) -> 
                        L IO {use=1} (LTup (MyVect size a) (MyVect size b))
vec' f FZ arr new = update f FZ arr new
vec' f (FS x) arr new = do
                (old !! new) <- update f (FS x) arr new
                vec' f (weaken x) old new

vecMap : (CType a, CType b) => {size : Nat} -> (a -> b) -> (1 _ : MyVect (S size) a) -> L IO {use=1} (MyVect (S size) b)
vecMap f a = do
        new <- createArr size
        (old !! new) <- vec' f last a new
        freeArr old
        pure1 new

(<$$>) : (CType a, CType b) => {size : Nat} -> (a -> b) -> (1 _ : MyVect (S size) a) -> L IO {use=1} (MyVect (S size) b)
(<$$>) = vecMap
infixr 4 <$$>


intToChar : Int -> Char
intToChar 0 = 'c'
intToChar _ = 'a'

const0 : Int -> Int
const0 = const 0

{-
main : IO ()
main = runLin $ do
        x <- createArr 9
        x <- const0 <$$> x
        x <- intToChar <$$> x
        (val # x) <- getIndex 5 x
        print val
        freeArr x-}


vecToArr' : (CType a) => (Fin size) -> (Vect size a) -> (1 _ : MyVect size a) -> L IO {use=1} (MyVect size a)
vecToArr' FZ vec arr = writeArr (index FZ vec) (FZ) arr
vecToArr' (FS x) vec arr = do
                        arr <- writeArr (index (FS x) vec) (FS x) arr
                        vecToArr' (weaken x) vec arr

vecToArr : (CType a) => (size : Nat) -> (Vect (S size) a) -> L IO {use=1} (MyVect (S size) a)
vecToArr k vect = do
                x <- createArr k
                vecToArr' (last) vect x


foldrArr' : (CType a) => (Fin size) -> (a -> b -> b) -> b -> (1 _ : MyVect size a) -> L IO b
foldrArr' FZ func acc arr = do
                        (val # arr) <- getIndex FZ arr
                        freeArr arr
                        pure (func val acc)     
foldrArr' (FS x) func acc arr = do
                       (val # arr) <- getIndex (FS x) arr
                       foldrArr' (weaken x) func (func val acc) arr


foldrArr : (CType a) => {size : Nat} -> (a -> b -> b) -> b -> (1 _ : MyVect (S size) a) -> L IO b
foldrArr func acc arr = foldrArr' last func acc arr

arrToList : (CType a) => {size : Nat} -> (1 _ : MyVect (S size) a) -> L IO (List a)
arrToList arr = foldrArr (::) [] arr
                

lengthNonZero : (l : List Int) -> (NonEmpty l) -> (NonZero (length l))
lengthNonZero [] x impossible
lengthNonZero (y :: xs) x = SIsNonZero
 


main : IO ()
main = runLin $ do
        x <- vecToArr 2 [the Int 142,3,4]
        val <- arrToList x
        print val

