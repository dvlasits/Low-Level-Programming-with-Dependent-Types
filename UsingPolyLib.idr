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



divSmallerWithProof : (x : Nat) -> (y : Nat) -> {auto prf : LT x y} -> (x2 : Nat ** LT x2 y)
divSmallerWithProof x y {prf} = (div2 x ** divSmaller {x=x} {y=y} prf)



bubbleUp : (pos : Nat) -> {size : Nat} -> {auto prf : LTE (S pos) (S size)} -> (1 _ : MyVectL (S size) TInt p m) -> L IO {use=1} (MyVectL (S size) TInt p m)
bubbleUp Z arr = pure1 arr
bubbleUp (S x) {size} {prf} arr = let (newPos ** _) = divSmallerWithProof (S  x) (S size) {prf=prf} in do
                                            currEle # arr <- readArrL (natToFinLT (S x)) arr
                                            parent # arr <- readArrL (natToFinLT newPos) arr 
                                            if currEle < parent then do
                                                        arr <- writeArrL (natToFinLT newPos) currEle arr 
                                                        arr <- writeArrL (natToFinLT (S x)) parent arr
                                                        bubbleUp newPos arr
                                                else do
                                                        pure1 arr


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