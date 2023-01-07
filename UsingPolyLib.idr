import LinearLibPoly6
import Control.Linear.LIO
import Data.Vect
import Data.Nat
import Data.Fin
import BinarySearch







addList : Nat -> (Vect (S m) Type2) -> (Vect (S m) Type2)
addList n v = map (TArr n) v


swapsies : {size : Nat} -> {t : (Vect (S m) Type2)} -> (1 _ : MyVectL (S size) (TStruct t) parent myptr) -> L IO {use=1} (DPair2 AnyPtr (\ptr => MyStructL (addList (S size) t) Nothing ptr))
swapsies {size} {t} v = do
            (newPtr *? newStruct) <- createStructL $ addList (S size) t
            --- Here we have v is a list of structs
            -- We have newStruct which is a struct of lists
            (_ *? firstStruct) *?? v <- readArrL 0 v
            ?something

data MinHeap : Nat -> Type where
        MinHeapL : (1 _ : MyVectL (S s) TInt parent myptr) -> (containing : Fin (S s)) -> MinHeap (S s)

createMinHeap : (size : Nat) -> L IO {use=1} (MinHeap (S size))
createMinHeap size = do
                (_ *? arr) <- createArrL TInt size 
                pure1 $ MinHeapL arr 0

freeMinHeap : (1 _ : MinHeap (S size)) -> L IO ()
freeMinHeap (MinHeapL v _) = freeArrL v


bubbleUp : (pos : Nat) -> {size : Nat} -> {auto prf : LTE (S pos) (S size)} -> (1 _ : MyVectL (S size) TInt p m) -> L IO {use=1} (MyVectL (S size) TInt p m)
bubbleUp Z arr = pure1 arr
bubbleUp (S x) {prf} arr = let newPos = div2 x in do
                                            currEle # arr <- readArrL (natToFinLT x) arr
                                            val # arr <- readArrL (natToFinLT newPos) arr 
                                            ?onuthuooe


push : {size : Nat} -> (element : Int) -> (1 _ : MinHeap (S size)) -> L IO {use=1} (MinHeap (S size))
push {size} ele (MinHeapL arr containing) = case strengthen containing of
                                                Nothing => (pure1 $ MinHeapL arr containing)
                                                Just x => let pos = shift 1 x in do
                                                                                arr <- writeArrL pos ele arr
                                                                                pure1 (MinHeapL arr pos)




main : IO ()
main = runLin $ do
            myheap <- createMinHeap 10
            freeMinHeap myheap