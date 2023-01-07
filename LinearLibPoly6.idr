import System.FFI
import PrimIO
import Prelude
import Control.Linear.LIO
import Control.App
import Control.App.Console
import System.FFI
import PrimIO
import Prelude
import Control.Linear.LIO
import Control.Monad.State.State
import Control.Monad.State
import Data.Fin
import Data.Nat
import Data.Vect
import Debug.Trace

--Create Arrays
%foreign "C:getArray, libsmall"
getArray : Int -> PrimIO (Ptr Int)

%foreign "C:getArray, libsmall"
getArrayChar : Int -> PrimIO (AnyPtr)

--Read Arrays
%foreign "C:readPointerOffset, libsmall"
readPointerOffset : Int -> (1 mem : AnyPtr) -> PrimIO Int

%foreign "C:readPointerOffsetChar, libsmall"
readPointerOffsetChar : Int -> (1 mem : AnyPtr) -> PrimIO Char

--Write Arrays
%foreign "C:writeOffset, libsmall"
writeOffset : Int -> (1 mem : AnyPtr) -> Int -> PrimIO ()

%foreign "C:writeOffsetChar, libsmall"
writeOffsetChar : Int -> (1 mem : AnyPtr) -> Char -> PrimIO ()

--Free Pointer
%foreign "C:freePointer, libsmall"
freePointer : (1 mem : AnyPtr) -> PrimIO ()

%foreign "C:freePointerChar, libsmall"
freePointerChar : (1 mem : Ptr Char) -> PrimIO ()

--Creating any Sized Struct
%foreign "C:createStruct, libsmall"
createStruct : Int -> PrimIO AnyPtr

--Getting data from structs
%foreign "C:getIntStruct, libsmall"
getIntStruct : AnyPtr -> Int -> PrimIO Int

%foreign "C:getCharStruct, libsmall"
getCharStruct : AnyPtr -> Int -> PrimIO Char

%foreign "C:getStructStruct, libsmall"
getStructStruct : AnyPtr -> Int -> PrimIO AnyPtr

--Writing to Structs
%foreign "C:writeIntStruct, libsmall"
writeIntStruct : AnyPtr -> (offset : Int) -> Int -> PrimIO ()

%foreign "C:writeCharStruct, libsmall"
writeCharStruct : AnyPtr -> (offset : Int) -> Char -> PrimIO ()

%foreign "C:writeStructStruct, libsmall"
writeStructStruct : AnyPtr -> (offset : Int) -> AnyPtr -> Int -> PrimIO ()

--Need write struct thing



x : IO AnyPtr
x = fromPrim (createStruct 10)

data MyPtr2 : (parent : AnyPtr) -> Type where
        Ptr2 : {a : AnyPtr} -> AnyPtr -> MyPtr2 a


freePoint : (a : AnyPtr) -> MyPtr2 a -> IO ()
freePoint a b = pure ()

x2 : (a : AnyPtr) -> IO (MyPtr2 a)
x2 a = pure (Ptr2 a)




data MyPtr : Type -> Type where
        NPtr : AnyPtr -> MyPtr a

data Type2 : Type where
        TInt : Type2
        TChar : Type2
        TStruct : (Vect (S m) Type2) -> Type2
        TArr : (m : Nat) -> Type2 -> Type2


sizeOfT2 : Type2 -> Int
sizeOfT2 (TInt) = 4
sizeOfT2 (TChar) = 1
sizeOfT2 (TStruct x) = sum (map sizeOfT2 x)
sizeOfT2 (TArr s t) = (cast (S s)) * (sizeOfT2 t)

sizeofStruct :  (Vect m Type2) -> Int
sizeofStruct [] = 0
sizeofStruct a@(x::xs) = sizeOfT2 (TStruct a)



data MyStruct : Vect m Type2 -> Type where
        StructCreate : (0 a : Vect (S k) Type2) -> (sizeOfStruct : Int) -> AnyPtr -> MyStruct a

export
data MyVect : Nat -> Type2 -> Type where
        Arr : (size : Nat) -> (AnyPtr) -> MyVect (S size) a

%name MyVect arr, arr1, arr2


makeStruct : (t : Vect (S m) Type2) -> IO (MyStruct t)
makeStruct a = let size = sizeOfT2 (TStruct a) in 
                 (StructCreate a size) <$> (fromPrim (createStruct size))

conv : (Fin m) -> Int
conv = cast . finToInteger 


convType2 : Type2 -> Type
convType2 TInt = Int
convType2 TChar = Char
convType2 (TStruct a) = MyStruct a
convType2 (TArr (m) t) = MyVect (S m) t



vecTake : (x : Fin m) -> Vect m a -> Vect (finToNat x) a
vecTake FZ _ = []
vecTake (FS y) (x::xs) = x :: (vecTake y xs)


doArr : (k : Nat) -> (t2 : Type2) -> (AnyPtr -> MyVect (S k) t2)
doArr n t2 = (Arr n)



readStruct' : (loc : Fin (S m)) -> {t : Vect (S m) Type2} -> MyStruct t -> (loc' : Int) -> IO (convType2 (index loc t))
readStruct' loc struct'' loc' with (index loc t) proof p
                readStruct' loc (StructCreate _ s ptr) loc' | TInt =  (fromPrim (getIntStruct ptr loc'))
                readStruct' loc (StructCreate _ s ptr) loc' | TChar = (fromPrim (getCharStruct ptr loc'))
                readStruct' loc (StructCreate _ s ptr) loc' | TStruct l = (StructCreate l (sizeOfT2 (TStruct l)))  <$> (fromPrim (getStructStruct ptr loc'))
                readStruct' loc (StructCreate _ s ptr) loc' | TArr s2 l = ((doArr s2 l) <$> (fromPrim (getStructStruct ptr loc')))

readStruct : (loc : Fin (S m)) -> {t : Vect (S m) Type2} -> MyStruct t -> IO (convType2 (index loc t))
readStruct loc struct'' = readStruct' loc struct'' (sizeofStruct (vecTake (loc) t))



writeStruct' : (loc : Fin (S m)) -> {t : Vect (S m) Type2} -> (convType2 (index loc t)) -> MyStruct t -> (loc' : Int) -> PrimIO ()
writeStruct' loc val struct'' loc' with (index loc t) proof p
                                        writeStruct' loc val (StructCreate _ s ptr) loc' | TInt = writeIntStruct ptr loc' (val)
                                        writeStruct' loc val (StructCreate _ s ptr) loc' | TChar = writeCharStruct ptr loc' (val)
                                        writeStruct' loc val (StructCreate _ s ptr) loc' | TStruct l = let s : MyStruct l = val in
                                                                                                            let (StructCreate _ size ptrVal)  = s in
                                                                                                                (writeStructStruct ptr loc' ptrVal (sizeofStruct l))
                                        writeStruct' loc val (StructCreate _ s ptr) loc' | TArr s2 l = let s : MyVect (S s2) l = val in
                                                                                                        let (Arr s ptrVal) = s in 
                                                                                                        (writeStructStruct ptr loc' ptrVal (cast (S s2) * (sizeOfT2 l)))


writeStruct : (loc : Fin (S m)) -> {t : Vect (S m) Type2} -> (convType2 (index loc t)) -> MyStruct t -> IO ()
writeStruct loc val (StructCreate l s ptr) = fromPrim (writeStruct' loc val (StructCreate l s ptr) (sizeofStruct (vecTake (loc) t)))


createArr : (a : Type2) -> (size : Nat) -> IO (MyVect (S size) a) 
createArr a (size) = let s1 = sizeOfT2 a in do
                x <- (fromPrim (getArrayChar (s1 * (cast (S size)))))
                pure (Arr size x)

writeArr : {a : Type2} -> (index : Fin m) -> (convType2 a) -> (MyVect m a) -> IO ()
writeArr {a=TInt} index int (Arr s ptr)  = let int' : Int =  int in
                                                        (fromPrim (writeOffset (conv index) ptr int'))
writeArr {a=TChar} index char (Arr s ptr)  = let int' : Char = char in
                                        (fromPrim (writeOffsetChar (conv index) ptr int'))
writeArr {a=TStruct t} index struct (Arr s ptr2)  = let x : MyStruct t = struct in
                                                let (StructCreate _ size ptr) = x in 
                                                        (fromPrim (writeStructStruct ptr2 ((sizeofStruct t) * (conv index)) ptr (size)))
writeArr {a=TArr s t2} index tarr (Arr s1 ptr2)  = let x : MyVect (S s) t2 = tarr in 
                                                let (Arr s2 ptr) = x in 
                                                        (fromPrim (writeStructStruct ptr2 ((sizeOfT2 t2)* (conv index)) ptr (cast s2)))

readArr : {a : Type2} -> (index : Fin m) -> (MyVect m a) -> IO (convType2 a)
readArr {a=TInt} index (Arr s ptr) = (fromPrim (readPointerOffset (conv index) ptr))
readArr {a=TChar} index (Arr s ptr) = (fromPrim (readPointerOffsetChar (conv index) ptr))
readArr {a=TStruct t} index (Arr s ptr) = (StructCreate t (sizeofStruct t)) <$> (fromPrim (getStructStruct ptr (conv index * (sizeofStruct t))))
readArr {a=TArr s t2} index (Arr s1 ptr) = let x : (AnyPtr -> MyVect (S s) t2) = (Arr s) in 
                                                 x <$> (fromPrim (getStructStruct ptr (conv index * (sizeOfT2 t2))))



export
data MyVectL : Nat -> Type2 -> (parent : (Maybe AnyPtr)) -> (myptr : AnyPtr) -> Type where
        ArrL : {x : Maybe (AnyPtr)} ->  (size : Nat) -> (1 myptr : AnyPtr) -> MyVectL (S size) a x myptr

export
getSize : {size : Nat} -> (1 _ : MyVectL (S size) t parent myptr) -> L IO {use=1} (Res (Res Nat (\x=> x=size )) (\_=> MyVectL (S size) t parent myptr))
getSize {size} v = pure1 $ (size # Refl) # v

export
data MyStructL : Vect m Type2 -> (parent : (Maybe AnyPtr)) -> (myptr : AnyPtr) -> Type where
        StructCreateL : {x : Maybe (AnyPtr)} -> (a : Vect (S k) Type2) -> (sizeOfStruct : Int) -> (1 myptr : AnyPtr) -> MyStructL a x myptr


export
data DPair2 : (a : Type) -> (P : a -> Type) -> Type where
   (*?) : {P : a -> Type} -> (x : a) -> (1 _ : P x) -> DPair2 a P
infixr 4 *?





toStruct : MyStructL t a myptr -> MyStruct t
toStruct (StructCreateL x y z) = (StructCreate x y z)



export
createArrL : (a : Type2) -> (size : Nat) -> L IO {use=1} (DPair2 AnyPtr (\myptr => MyVectL (S size) a Nothing myptr))
createArrL a (size) = let s1 = sizeOfT2 a in do
                x <- liftIO1 (fromPrim (getArrayChar (s1 * (cast (S size)))))
                pure1 ((x) *? (ArrL size x))

export
createStructL : (t : Vect (S m) Type2) -> L IO {use=1} (DPair2 AnyPtr (\myptr => MyStructL t Nothing myptr))
createStructL x = let struct' = (makeStruct x) in do
                        (StructCreate x y z) <- liftIO1 {io = L IO} (struct')
                        pure1 ((z) *? (StructCreateL x y z))



writeArrL' : {a : Type2} -> (index : Fin m) -> (convType2 a) -> (MyVectL m a parent myptr) -> L IO {use=1} (MyVectL m a parent myptr)
writeArrL' {a=TInt} index int (ArrL s ptr)  = let int' : Int =  int in
                                                        do 
                                                            liftIO1 (fromPrim (writeOffset (conv index) ptr int'))
                                                            pure1 (ArrL s ptr)
writeArrL' {a=TChar} index char (ArrL s ptr)  = let int' : Char = char in do
                                                        liftIO1 (fromPrim (writeOffsetChar (conv index) ptr int'))
                                                        pure1 (ArrL s ptr)
writeArrL' {a=TStruct t} index struct (ArrL s ptr2)  = let x : MyStruct t = struct in
                                                let (StructCreate _ size ptr) = x in do
                                                        liftIO1 (fromPrim (writeStructStruct ptr2 ((sizeofStruct t) * (conv index)) ptr (size)))
                                                        pure1 (ArrL s ptr2)
writeArrL' {a=TArr s t2} index tarr (ArrL s1 ptr2)  = let x : MyVect (S s) t2 = tarr in 
                                                let (Arr s2 ptr) = x in do
                                                        liftIO1 (fromPrim (writeStructStruct ptr2 ((sizeOfT2 t2)* (conv index)) ptr (cast s2)))
                                                        pure1 (ArrL s1 ptr2)

export
writeArrL : {a : Type2} -> (index : Fin m) -> (convType2 a) -> (1 _ : MyVectL m a parent myptr) -> L IO {use=1} (MyVectL m a parent myptr)
writeArrL index item = assert_linear (writeArrL' index item)



writeStructL' : (loc : Fin (S m)) -> {t : Vect (S m) Type2} -> (convType2 (index loc t)) -> (MyStructL t a myptr) -> L IO {use=1} (MyStructL t a myptr)
writeStructL' index item struct' = let struct = toStruct struct' in do
                                liftIO1 {io=L IO} ((writeStruct index item) struct)
                                pure1 (struct')


export
writeStructL : (loc : Fin (S m)) -> {t : Vect (S m) Type2} -> (convType2 (index loc t)) -> (1 _ : MyStructL t a myptr) -> L IO {use=1} (MyStructL t a myptr)
writeStructL index item = assert_linear (writeStructL' index item)


export
data SpecialPair : Type -> Type -> Type where
        (*??) : (1 _ : a) -> (1 _ : b) -> SpecialPair a b
infixr 4 *??

getData : (MyStructL t a myptr) -> ((MyStruct t), MyStructL t a myptr)
getData (StructCreateL x y z) = ((StructCreate x y z),(StructCreateL x y z))




createKid : {myptr2 : AnyPtr} -> (parent : MyStructL v a myptr2) -> (kidpointer : AnyPtr) -> {t : Vect (S m) Type2} -> IO (MyStructL t (Just myptr2) kidpointer)
createKid (StructCreateL _ _ ptr) newPtr = do
                pure (StructCreateL t (sizeofStruct t) newPtr)


createKidArrStruct : {myptr2 : AnyPtr} -> (MyVectL (S size) t parent myptr2) -> (kidpointer : AnyPtr) -> {t1 : Vect (S m) Type2} -> IO (MyStructL t1 (Just myptr2) kidpointer)
createKidArrStruct (ArrL size ptr) newPtr = do
                pure (StructCreateL t1 (sizeofStruct t1) newPtr)



toLIO1 : IO a -> L IO {use=1} a
toLIO1 x = do
        y <- liftIO1 {io = L IO} x
        pure1 y


readArrL' : {t : Type2} -> (index : Fin m) -> (MyVectL m t parent myptr) -> L IO {use=1} (case t of
                                                                                TInt => Res Int (\_ => MyVectL m t parent myptr)
                                                                                TChar => Res Char (\_ =>MyVectL m t parent myptr)
                                                                                TStruct l => SpecialPair (DPair2 AnyPtr (\kidpointer => MyStructL l (Just (myptr)) kidpointer)) (MyVectL m t parent myptr)
                                                                                TArr s2 l => SpecialPair (DPair2 AnyPtr (\kidpointer => MyVectL (S s2) l (Just myptr) kidpointer)) (MyVectL m t parent myptr)
                                                                                )
readArrL' {t=TInt} index (ArrL s ptr) = toLIO1 $ ((# (ArrL s ptr)) <$> (fromPrim (readPointerOffset (conv index) ptr)))
readArrL' {t=TChar} index (ArrL s ptr) = toLIO1 $ ((# (ArrL s ptr)) <$> (fromPrim (readPointerOffsetChar (conv index) ptr)))
readArrL' {t=TStruct l} index (ArrL s ptr) = toLIO1 (do
                                            x <- (fromPrim (getStructStruct ptr (conv index * (sizeofStruct l))))
                                            pure ((x *? (StructCreateL l (sizeofStruct l) x)) *?? (ArrL s ptr)))
readArrL' {t=TArr s t2} index (ArrL s1 ptr) =  toLIO1 (do
                                                    ptr1 <- (fromPrim (getStructStruct ptr (conv index * (sizeOfT2 t2))))
                                                    pure ((ptr1 *? (ArrL s ptr1)) *?? (ArrL s1 ptr))
                                                    )


copyPlace' : a -> L IO {use=1} (Res a (\_ => a))
copyPlace' x = pure1 $ x # x

copyPlace : (1 _ : a) -> L IO {use=1} (Res a (\_ => a))
copyPlace = assert_linear copyPlace'

consume' : a -> L IO ()
consume' a = pure ()

consume : (1 _ : a) -> L IO ()
consume = assert_linear consume'

export
readArrL : {t : Type2} -> (index : Fin m) -> (1 _ : MyVectL m t parent myptr) -> L IO {use=1} (case t of
                                                                                TInt => Res Int (\_ => MyVectL m t parent myptr)
                                                                                TChar => Res Char (\_ =>MyVectL m t parent myptr)
                                                                                TStruct l => SpecialPair (DPair2 AnyPtr (\kidpointer => MyStructL l (Just (myptr)) kidpointer)) (MyVectL m t parent myptr)
                                                                                TArr s2 l => SpecialPair (DPair2 AnyPtr (\kidpointer => MyVectL (S s2) l (Just myptr) kidpointer)) (MyVectL m t parent myptr)
                                                                                )
readArrL {t=t} index arr =  do
                        (x1 # x2) <- copyPlace arr
                        consume x2
                        x <-  (readArrL' {t=t} index x1)
                        y <- assert_linear pure x
                        pure1 (believe_me y)


readStructL' : (loc' : Int)  -> (structPointer : AnyPtr)-> (loc : Fin (S m)) -> {myptr : AnyPtr } -> {t : Vect (S m) Type2} -> (parent : MyStructL t a myptr) -> L IO {use=1} (case (index loc t) of
                                                                                TInt => Res Int (\_ => MyStructL t a myptr)
                                                                                TChar => Res Char (\_ => MyStructL t a myptr)
                                                                                TStruct l => SpecialPair (DPair2 AnyPtr (\kidpointer => MyStructL l (Just (myptr)) kidpointer)) (MyStructL t a myptr)
                                                                                TArr s2 l => SpecialPair (DPair2 AnyPtr (\kidpointer => MyVectL (S s2) l (Just myptr) kidpointer)) (MyStructL t a myptr) 
                                                                                )
readStructL' loc' ptr loc ssL with (index loc t) proof p
        readStructL' loc' ptr loc ssL | TInt = toLIO1 $ ((# ssL) <$> (fromPrim (getIntStruct ptr loc')))
        readStructL' loc' ptr loc ssL | TChar = toLIO1 $ (# ssL) <$> (fromPrim (getCharStruct ptr loc'))
        readStructL' loc' ptr loc ssL | TStruct l = toLIO1 (do
                                                x <- (fromPrim (getStructStruct ptr loc'))
                                                newStruct <- createKid ssL {t=l} x
                                                pure ((x *? newStruct) *?? ssL))
        readStructL' loc' ptr loc ssL | TArr s2 l = do
                                        x <- liftIO {io = L IO} (fromPrim (getStructStruct ptr loc'))
                                        pure1 ((x *? (ArrL s2 x)) *?? ssL)



export
readStructL : (loc : Fin (S m)) -> {t : Vect (S m) Type2} -> {myptr : AnyPtr} ->(1 parent : MyStructL t a myptr) -> L IO {use=1} (case (index loc t) of
                                                                                TInt => Res Int (\_ => MyStructL t a myptr)
                                                                                TChar => Res Char (\_ => MyStructL t a myptr)
                                                                                TStruct l => SpecialPair (DPair2 AnyPtr (\kidpointer => MyStructL l (Just (myptr)) kidpointer)) (MyStructL t a myptr)
                                                                                TArr s2 l => SpecialPair (MyVect (S s2) l) (MyStructL t a myptr) 
                                                                                )
readStructL loc struct' = let ((StructCreate t s ptr), ssL) =  assert_linear getData struct' in 
                                                        let loc' = sizeofStruct (vecTake (loc) t) in 
                                                                believe_me (readStructL' loc' ptr loc ssL)


freeStructStructLKid' : (1 parent : MyStructL t a myptr) -> (MyStructL t2 (Just (myptr)) kidpointer) -> L IO {use=1} (MyStructL t a myptr)
freeStructStructLKid' struct' (StructCreateL _ _ ptr) = pure1 struct'

freeArrArrLKid' : (1 p1 : MyVectL (S size) t parent myptr) -> (MyVectL (S size2) t2 (Just (myptr)) kidpointer) -> L IO {use=1} (MyVectL (S size) t parent myptr)
freeArrArrLKid' v1 (ArrL _ ptr) = pure1 v1

export
freeArrArrLKid : (1 p1 : MyVectL (S size) t parent myptr) -> (1 _ : MyVectL (S size2) t2 (Just (myptr)) kidpointer) -> L IO {use=1} (MyVectL (S size) t parent myptr)
freeArrArrLKid v1 = assert_linear (freeArrArrLKid' v1)

export
freeStructStructLKid : (1 parent : MyStructL t a myptr) -> (1 _ : MyStructL t2 (Just (myptr)) _) -> L IO {use=1} (MyStructL t a myptr)
freeStructStructLKid struct' = assert_linear (freeStructStructLKid' struct')

freeArrStructLKid' : (1 p1 : MyVectL (S size) t parent myptr) -> (MyStructL t2 (Just (myptr)) _) -> L IO {use=1} (MyVectL (S size) t parent myptr)

freeArrStructLKid' arr1 (StructCreateL _ _ ptr) = pure1 arr1
export
freeArrStructLKid : (1 p1 : MyVectL (S size) t parent myptr) -> (1 _ : MyStructL t2 (Just (myptr)) _) -> L IO {use=1} (MyVectL (S size) t parent myptr)
freeArrStructLKid arr1 = assert_linear (freeArrStructLKid' arr1)

freeStructArrLKid' : (1 parent : MyStructL t a myptr) -> (MyVectL (S size2) t2 (Just (myptr)) kidpointer) -> L IO {use=1} (MyStructL t a myptr)
freeStructArrLKid' struct (ArrL _ ptr) = pure1 struct

export
freeStructArrLKid : (1 parent : MyStructL t a myptr) -> (1 _ : MyVectL (S size2) t2 (Just (myptr)) kidpointer) -> L IO {use=1} (MyStructL t a myptr)
freeStructArrLKid struct = assert_linear (freeStructArrLKid' struct)

export
freeArrL : (1 _ : MyVectL (S size) t parent myptr) -> L IO ()
freeArrL (ArrL _ ptr) = do
                x <- liftIO1 (fromPrim (freePointer ptr))
                pure ()

export
freeStructL : (1 _ : MyStructL t Nothing myptr) -> L IO ()
freeStructL (StructCreateL _ _ ptr) = do
        x <- liftIO1 {io= L IO} (fromPrim (freePointer ptr))
        pure ()


export
runLin : (Applicative io, LinearBind io) => (1 _ : L io a) -> io a
runLin = Control.Linear.LIO.run


{-
main : IO ()
main = runLin $ do

    (_ *? arr) <- createArrL (TStruct [TInt, TChar]) 100

    (_ *? oneStruct) *?? arr <- readArrL 10 arr

    oneStruct <- writeStructL 0 20 oneStruct

    arr <- freeArrStructLKid arr oneStruct --Need a type class for generic frees

    (_ *? oneStruct2) *?? arr <- readArrL 10 arr

    val # oneStruct2 <- readStructL 0 oneStruct2

    print val 

    arr <- freeArrStructLKid arr oneStruct2


    freeArrL arr


-}
