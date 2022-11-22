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






readStruct : (loc : Fin (S m)) -> {t : Vect (S m) Type2} -> MyStruct t -> IO (convType2 (index loc t))
readStruct loc (StructCreate t s ptr) = let t2 = index loc t in 
                                        let loc' = sizeofStruct (vecTake (loc) t) in 
                                        case (index loc t) of 
                                                TInt => believe_me <$> (fromPrim (getIntStruct ptr loc'))
                                                TChar => believe_me <$> (fromPrim (getCharStruct ptr loc'))
                                                TStruct l => (believe_me . (StructCreate l (sizeOfT2 (TStruct l)))  <$> (fromPrim (getStructStruct ptr loc')))
                                                TArr (s2) l => (believe_me .  (doArr s2 l)) <$> (fromPrim (getStructStruct ptr loc'))



writeStruct : (loc : Fin (S m)) -> {t : Vect (S m) Type2} -> (convType2 (index loc t)) -> MyStruct t -> IO ()
writeStruct loc val (StructCreate l s ptr) = let loc' = sizeofStruct (vecTake (loc) t) in 
                                                fromPrim $ case (index loc l) of
                                                        TInt => let val2 : Int = believe_me val in writeIntStruct ptr loc' (val2)
                                                        TChar => let val2 : Char = believe_me val in writeCharStruct ptr loc' (val2)
                                                        TStruct l => let s : MyStruct l = believe_me val in
                                                                        let (StructCreate _ size ptrVal)  = s in
                                                                                (writeStructStruct ptr loc' ptrVal (sizeofStruct l))
                                                        TArr s2 l => let s : MyVect (S s2) l = believe_me val in
                                                                        let (Arr s ptrVal) = s in 
                                                                                trace "written array" (writeStructStruct ptr loc' ptrVal (cast (S s2) * (sizeOfT2 l)))



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


{-

main : IO ()
main = do                                                                                                                                            
        arr1 <- createArr (TStruct [TInt, TChar]) 9
        s1 <- readArr 4 arr1
        writeStruct 1 'c' s1
        writeArr 0 s1 arr1
        s2 <- readArr 0 arr1
        c1 <- readStruct 1 s2
        print c1
-}


{-
main : IO ()
main = do
        struct1 <- makeStruct [TStruct [TInt, TChar, TArr 3 (TArr 2 TInt)], TChar, TArr 2 TInt, TStruct [TChar]]
        arr1 <- createArr TInt 2
        writeArr 0 100 arr1
        writeArr 1 200 arr1
        writeArr 2 300 arr1
        writeStruct 2 arr1 struct1
        arr2 <- readStruct 2 struct1
        val <- readArr 1 arr2
        print val
        s2 <- readStruct 3 struct1
        writeStruct 0 'd' s2
        val <- readStruct 0 s2
        print val
-}
{-
main : IO ()
main = do
        x <- makeStruct [TInt, TStruct [TInt]]
        writeStruct 0 100 x
        s2 <- readStruct 1 x
        writeStruct 0 500 s2
        val <- readStruct 0 x
        x4 <- readStruct 1 x
        val2 <- readStruct 0 x4
        print val2
-}

--------------------------------------------- Linear Part

export
data MyVectL : Nat -> Type2 -> Type where
        ArrL : (size : Nat) -> (1 _ : AnyPtr) -> MyVectL (S size) a

data MyStructL : Vect m Type2 -> Type where
        StructCreateL : (0 a : Vect (S k) Type2) -> (sizeOfStruct : Int) -> (1 _ : AnyPtr) -> MyStructL a


toLinStruct : MyStruct t -> MyStructL t
toLinStruct (StructCreate x y z) = (StructCreateL x y z)

toStruct : MyStructL t -> MyStruct t
toStruct (StructCreateL x y z) = (StructCreate x y z)

getStructToLin : IO (MyStruct t) -> L IO {use=1} (MyStructL t)
getStructToLin x = do
                x1 <- toLinStruct <$> (liftIO1 {io=L IO} x)
                pure1 x1

createStructL : (t : Vect (S m) Type2) -> L IO {use=1} (MyStructL t)
createStructL x = (getStructToLin (makeStruct x))

writeStructL' : (loc : Fin (S m)) -> {t : Vect (S m) Type2} -> (convType2 (index loc t)) -> (MyStruct t) -> L IO {use=1} (MyStructL t)
writeStructL' index item struct = do
                                liftIO1 {io=L IO} ((writeStruct index item) struct)
                                pure1 (toLinStruct struct)

writeStructL : (loc : Fin (S m)) -> {t : Vect (S m) Type2} -> (convType2 (index loc t)) -> (1 _ : MyStruct t) -> L IO {use=1} (MyStructL t)
writeStructL index item = assert_linear (writeStructL' index item)

data SpecialPair : Type -> Type -> Type where
        SPair : (1 _ : a) -> b -> SpecialPair a b



readStructL' : (loc : Fin (S m)) -> {t : Vect (S m) Type2} -> MyStructL t -> L IO {use=1} (case (index loc t) of
                                                                                TInt => Res Int (\_ => MyStructL t)
                                                                                TChar => Res Char (\_ => MyStructL t)
                                                                                TStruct l => SpecialPair (MyStructL t) (MyStructL l)
                                                                                TArr s2 l => SpecialPair (MyStructL t) (MyVect (S s2) l)
                                                                                )
readStructL' loc struct' = let  ss@(StructCreate t s ptr) = toStruct struct' in 
                                        let ssL = toLinStruct ss in let t2 = index loc t in 
                                        let loc' = sizeofStruct (vecTake (loc) t) in do
                                                xxx <- liftIO {io=L IO} (case (index loc t) of 
                                                        TInt => ((believe_me . (# ssL)) <$> (fromPrim (getIntStruct ptr loc')))
                                                        TChar =>((believe_me . (# ssL)) <$> (fromPrim (getCharStruct ptr loc')))
                                                        TStruct l =>((believe_me . (SPair ssL) .  (toLinStruct . (StructCreate l (sizeOfT2 (TStruct l))))  <$> (fromPrim (getStructStruct ptr loc'))))
                                                        TArr (s2) l => ((believe_me . ((SPair ssL) . (doArr s2 l))) <$> (fromPrim (getStructStruct ptr loc'))))
                                                pure1 xxx

freeStructL : (MyStructL t) -> L IO {use=1} ()
freeStructL (StructCreateL _ _ ptr) = do
        x <- liftIO1 {io= L IO} (fromPrim (freePointer ptr))
        pure1 x
        



export
runLin : (Applicative io, LinearBind io) => (1 _ : L io a) -> io a
runLin = Control.Linear.LIO.run

