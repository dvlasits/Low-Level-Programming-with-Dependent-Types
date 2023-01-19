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




div2Fin : (Fin s) -> (Fin s)
div2Fin FZ = FZ
div2Fin (FS FZ) = FZ
div2Fin (FS (FS x)) = FS (weaken (div2Fin x))


bubbleUp : {size : Nat} -> (pos : Fin (S size)) -> (1 _ : MyVectL (S size) TInt p m) -> L IO {use=1} (MyVectL (S size) TInt p m)
bubbleUp FZ arr = pure1 arr
bubbleUp {size} (FS x) arr = let newPos = div2Fin (weaken x) in do
                                            currEle # arr <- readArrL (FS x) arr
                                            parent # arr <- readArrL (newPos) arr 
                                            if currEle < parent then do
                                                        arr <- writeArrL (newPos) arr currEle
                                                        arr <- writeArrL (FS x) arr parent
                                                        bubbleUp newPos arr
                                                else do
                                                        pure1 arr


push : {size : Nat} -> (element : Int) -> (1 _ : MinHeap (S size)) -> L IO {use=1} (MinHeap (S size))
push {size} ele (MinHeapL arr containing) = case strengthen containing of
                                                Nothing => (pure1 $ MinHeapL arr containing)
                                                Just x => let pos = shift 1 x in do
                                                                                arr <- writeArrL containing arr ele
                                                                                arr <- bubbleUp containing arr
                                                                                pure1 (MinHeapL arr (shift 1 x))


printIntArr' : {size : Nat} -> (pos : Fin (S size)) -> (1 _ : MyVectL (S size) TInt p m) -> L IO {use=1} (Res String (\_ => MyVectL (S size) TInt p m))
printIntArr' FZ arr = do
                        ele # arr <- readArrL FZ arr
                        pure1 $ (show ele) # arr
printIntArr' (FS x) arr = do
                        ele # arr <- readArrL (FS x) arr
                        s # arr <- printIntArr' (weaken x) arr
                        pure1 $ (s ++ "," ++ show ele) # arr


printIntArr : {size : Nat} -> (1 _ : MyVectL (S size) TInt p m) -> L IO {use=1} (Res String (\_ => MyVectL (S size) TInt p m))
printIntArr arr = printIntArr' last arr

swapGreater : {size : Nat} -> (pos1 : Fin (S size)) -> (pos2 : Fin (S size)) -> (1 _ : MinHeap (S size)) -> L IO {use=1} (Res Bool (\_ => MinHeap (S size)))
swapGreater pos1 pos2 (MinHeapL arr (FZ)) = pure1 $ False # (MinHeapL arr (FZ))
swapGreater pos1 pos2 (MinHeapL arr (FS x)) = do
                                        item1 # arr <- readArrL pos1 arr
                                        item2 # arr <- readArrL pos2 arr
                                        case compare item2 item1 of 
                                                LT => do 
                                                        arr <- writeArrL pos1 arr item2
                                                        arr <- writeArrL pos2 arr item1
                                                        pure1 $ True # (MinHeapL arr (FS x))
                                                EQ => pure1 $ False # (MinHeapL arr (FS x))
                                                GT => pure1 $ False # (MinHeapL arr (FS x))





bubbleDown : {size : Nat} -> (start : (Fin (S size))) -> (1 _ : MinHeap (S size)) -> L IO {use=1} (MinHeap (S size))
bubbleDown start (MinHeapL arr FZ) = pure1 (MinHeapL arr FZ)       
bubbleDown {size} start (MinHeapL arr containing) = let heap = (MinHeapL arr containing) in let c1 = (2* (finToInteger start) + 1) in 
                                                        let c2 = c1 + 1 in 
                                                                case integerToFin c1 (S size) of 
                                                                        Nothing => pure1 heap
                                                                        Just c1 => do   
                                                                                        if c1 < containing then do
                                                                                                b # heap <- swapGreater start c1 heap
                                                                                                case b of 
                                                                                                        True => bubbleDown c1 heap
                                                                                                        False => case integerToFin c2 (S size) of 
                                                                                                                        Nothing => pure1 heap
                                                                                                                        Just c2 => 
                                                                                                                                   if c2 < containing then do     
                                                                                                                                        b # heap <- swapGreater start c2 heap
                                                                                                                                        case b of 
                                                                                                                                                True => bubbleDown c2 heap
                                                                                                                                                False => pure1 heap
                                                                                                                                        else pure1 heap
                                                                                                else
                                                                                                        pure1 heap
                                                                                        



pop : {size : Nat} -> (1 _ : MinHeap (S size)) -> L IO {use=1} (Res (Maybe Int) (\_ => MinHeap (S size)))
pop (MinHeapL arr FZ) =  pure1 $ Nothing # (MinHeapL arr FZ)
pop (MinHeapL arr (FS x)) = do
                        toReturn # arr <- readArrL 0 arr
                        lastEle # arr <- readArrL (weaken x) arr
                        arr <- writeArrL (weaken x) arr 0
                        arr <- writeArrL 0 arr lastEle
                        s # arr <- printIntArr arr
                        heap <- bubbleDown 0 (MinHeapL arr (weaken x))
                        pure1 $ (Just toReturn) # heap




printHeap : {size : Nat} -> (1 _ : MinHeap (S size)) -> L IO {use=1} (MinHeap (S size))
printHeap (MinHeapL arr containing) = do
                                s # arr <- printIntArr arr
                                pure1 (MinHeapL arr containing)

main : IO ()
main = runLin $ do
                h <- createMinHeap 10

                h <- push 10 h
                h <- printHeap h
                h <- push 9 h
                h <- printHeap h
                h <- push 8 h
                h <- printHeap h
                h <- push 7 h
                h <- printHeap h
                h <- push 3 h
                h <- printHeap h
                ele # h <- pop h
                h <- printHeap h
                putStrLn $ (show ele)
                ele # h <- pop h
                h <- printHeap h
                putStrLn $ (show ele)
                ele # h <- pop h
                h <- printHeap h
                putStrLn $ (show ele)
                ele # h <- pop h
                h <- printHeap h
                putStrLn $ (show ele)
                ele # h <- pop h
                h <- printHeap h
                putStrLn $ (show ele)
                ele # h <- pop h
                h <- printHeap h
                putStrLn $ (show ele)
                
                freeMinHeap h
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

update : {t : Type2} -> {auto 0 ci : ConvertIt t func}-> {s : Nat} -> (Fin (S s))  -> func
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

genericMap' : {t : Type2} -> {auto 0 ci : ConvertIt t func} -> {parent : Maybe AnyPtr} ->{s : Nat} ->   (1 _ : MyVectL (S s) t parent my) -> (Fin (S s))  -> func
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




