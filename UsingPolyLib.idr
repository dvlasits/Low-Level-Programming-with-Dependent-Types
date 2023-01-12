import LinearLibPoly7
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
        MinHeapL : (1 _ : MyVectL (S s) TInt Nothing myptr) -> (containing : Fin (S s)) -> MinHeap (S s)

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
                                                        arr <- writeArrL (natToFinLT newPos) arr currEle
                                                        arr <- writeArrL (natToFinLT (S x)) arr parent
                                                        bubbleUp newPos arr
                                                else do
                                                        pure1 arr


push : {size : Nat} -> (element : Int) -> (1 _ : MinHeap (S size)) -> L IO {use=1} (MinHeap (S size))
push {size} ele (MinHeapL arr containing) = case strengthen containing of
                                                Nothing => (pure1 $ MinHeapL arr containing)
                                                Just x => let pos = shift 1 x in do
                                                                                arr <- writeArrL pos arr ele
                                                                                pure1 (MinHeapL arr pos)
{-
vec' : (Int -> Int) -> (Fin size) -> (1 _ : MyVect size) -> L IO {use=1} (MyVect size)
vec' f FZ arr = update f FZ arr
vec' f (FS x) arr = do
                arr <- update f (FS x) arr
                vec' f (weaken x) arr-}




data ConvertIt : (t : Type2) -> Type -> Type where
        [search t]
        TIntCIF : ConvertIt TInt (Int -> Int)
        TCharCIF : ConvertIt TChar (Char -> Char)
        TStructCIF : ConvertIt (TStruct l) ({m : Maybe AnyPtr} -> {p : AnyPtr} -> (1 _ : MyStructL l m p) -> L IO {use=1} (MyStructL l m p))
        TArrCIF : ConvertIt (TArr s t) ({p : Maybe AnyPtr} -> {m : AnyPtr} -> (1 _ : MyVectL (S s) t p m) -> L IO {use=1} (MyVectL (S s) t p m))


update : {t : Type2} -> {s : Nat} -> (Fin (S s)) -> {auto 0 ci : ConvertIt t func} -> func
                                                        -> {parent : Maybe AnyPtr} -> (1 _ : MyVectL (S s) t parent my)
                                                        -> L IO {use=1} (MyVectL (S s) t parent my)
update pos {ci=TIntCIF} f vec = do
                        val # vec <- readArrL pos vec
                        writeArrL pos vec (f val)
update pos {ci=TCharCIF} f vec = do
                        val # vec <- readArrL pos vec
                        writeArrL pos vec (f val)
update pos {ci=TStructCIF} f vec = do
                        (_ *? oneStruct)  *?? vec <- readArrL pos vec
                        oneStruct <- f oneStruct
                        oneStruct *?? vec <- writeArrL pos vec oneStruct
                        freeKid vec oneStruct
update pos {ci=TArrCIF} f vec = do
                        (lolol *? oneStruct)  *?? vec <- readArrL pos vec
                        oneStruct <- f oneStruct
                        oneStruct *?? vec <- writeArrL pos vec oneStruct
                        freeKid vec oneStruct





genericMap' : {t : Type2} -> {s : Nat} -> {parent : Maybe AnyPtr} ->  (1 _ : MyVectL (S s) t parent my) -> (Fin (S s)) -> {auto 0 ci : ConvertIt t func} -> func
                                                                                -> L IO {use=1} (MyVectL (S s) t parent my)
genericMap' vec FZ f = pure1 vec
genericMap' vec (FS x) f = do
                        arr <- update (FS x) f vec
                        genericMap' arr (weaken x) f



intMap :{s : Nat} -> {parent : Maybe AnyPtr} ->  (1 _ : MyVectL (S s) TInt parent my) -> {auto 0 ci : ConvertIt TInt func} -> func
                                                                                -> L IO {use=1} (MyVectL (S s) TInt parent my)
intMap v f = genericMap' v last f                                                                                

genericMap : {t : Type2} -> {s : Nat} -> {parent : Maybe AnyPtr} ->  (1 _ : MyVectL (S s) t parent my) -> {auto 0 ci : ConvertIt t func} -> func
                                                                                -> L IO {use=1} (MyVectL (S s) t parent my)
genericMap v f = genericMap' v last f


{-

recursePrintInt : {t : Type2} -> {s : Nat} -> (1 _ : MyVectL (S s) TInt parent my) -> (Fin (S s)) -> L IO {use=1} (Res String (\_ => MyVectL (S s) TInt parent my))
recursePrintInt vec FZ = pure1 $ "" # vec
recursePrintInt vec (FS x) = do
                                int # vec <- readArrL (FS x) vec
                                recursePrintInt vec (weaken x)



genericPrintArr : {t : Type2} -> {s : Nat} -> (1 _ : MyVectL (S s) t parent my) -> L IO {use=1} (Res String (\_ => MyVectL (S s) t parent my))
genericPrintArr {t} with (t) proof g
        genericPrintArr | TInt = ?onuthnth
        genericPrintArr | TChar = ?onetuhoenuth
        genericPrintArr | TStruct l = ?on
        genericPrintArr | TArr s2 l = ?onetuh
                
-}


main : IO ()
main = runLin $ do
                (_ *? arr) <- createArrL TInt 10
                arr <- intMap arr (the (Int -> Int) $ const 5)
                free arr



