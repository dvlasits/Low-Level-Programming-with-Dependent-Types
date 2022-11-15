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

--Create Arrays
%foreign "C:getArray, libsmall"
getArray : Int -> PrimIO (Ptr Int)

%foreign "C:getArray, libsmall"
getArrayChar : Int -> PrimIO (Ptr Char)

--Read Arrays
%foreign "C:readPointerOffset, libsmall"
readPointerOffset : Int -> (1 mem : Ptr Int) -> PrimIO Int

%foreign "C:readPointerOffsetChar, libsmall"
readPointerOffsetChar : Int -> (1 mem : Ptr Char) -> PrimIO Char

--Write Arrays
%foreign "C:writeOffset, libsmall"
writeOffset : Int -> (1 mem : Ptr Int) -> Int -> PrimIO ()

%foreign "C:writeOffsetChar, libsmall"
writeOffsetChar : Int -> (1 mem : Ptr Char) -> Char -> PrimIO ()

--Free Pointer
%foreign "C:freePointer, libsmall"
freePointer : (1 mem : Ptr Int) -> PrimIO ()

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



data Type2 = TInt | TChar | TStruct (Vect (S m) Type2) --Add arrays in here somehow?????


sizeofStruct :  (Vect m Type2) -> Int
sizeofStruct [] = 0
sizeofStruct (TInt::xs) = 4 + sizeofStruct xs
sizeofStruct (TChar::xs) = 1 + sizeofStruct xs
sizeofStruct (TStruct l::xs) = (sizeofStruct l) + (sizeofStruct xs)

data MyStruct : Vect m Type2 -> Type where
        StructCreate : (0 a : Vect (S k) Type2) -> (Int : sizeOfStruct) -> AnyPtr -> MyStruct a



makeStruct : (t : Vect (S m) Type2) -> IO (MyStruct t)
makeStruct a = (StructCreate a (sizeofStruct a)) <$> (fromPrim (createStruct (sizeofStruct a)))

conv : (Fin m) -> Int
conv = cast . finToInteger 


convType2 : Type2 -> Type
convType2 TInt = Int
convType2 TChar = Char
convType2 (TStruct a) = MyStruct a

{-
interface CanRead a where
        getSomethingStruct : AnyPtr -> Int -> IO a

CanRead Int where
        getSomethingStruct ptr loc' = (fromPrim (getIntStruct ptr loc'))
-}


readStruct : (loc : Fin (S m)) -> {t : Vect (S m) Type2} -> MyStruct t -> IO (convType2 (index loc t))
readStruct loc (StructCreate t s ptr) = let t2 = index loc t in 
                                        let loc' = conv loc in
                                        case t2 of 
                                                TInt => believe_me <$> (fromPrim (getIntStruct ptr loc'))
                                                TChar => believe_me <$> (fromPrim (getCharStruct ptr loc'))
                                                TStruct l => (believe_me . (StructCreate l (sizeofStruct l)))  <$> (fromPrim (getStructStruct ptr loc'))



writeStruct : (loc : Fin (S m)) -> {t : Vect (S m) Type2} -> (convType2 (index loc t)) -> MyStruct t -> IO ()
writeStruct loc val (StructCreate l s ptr) = 
                                        let loc' = conv loc in 
                                         fromPrim $ case (index loc l) of 
                                                TInt => writeIntStruct ptr loc' (believe_me val)
                                                TChar => writeCharStruct ptr loc' (believe_me val)
                                                TStruct l => let s : MyStruct l = believe_me val in
                                                                let (StructCreate _ size ptrVal)  = s in
                                                                        (writeStructStruct ptr loc' ptrVal (sizeofStruct l))




main : IO ()
main = do
        x <- makeStruct [TStruct [TInt, TInt]]
        x2 <- makeStruct [TInt, TInt]
        writeStruct 0 10 x2
        writeStruct 1 200 x2
        writeStruct 0 x2 x
        x4 <- readStruct 0 x
        val <- readStruct 1 x4
        print val





-- Need to make Arr constructor private
export
data MyVect : Nat -> Type -> Type where
        Arr : (size : Nat) -> (1 _ : Ptr a) -> MyVect (S size) a

%name MyVect arr, arr1, arr2


writeArrGen' : (Int -> (1 mem : Ptr t) -> t -> PrimIO ()) ->
                        (t -> (index : Fin m) -> (MyVect m t) -> L IO {use=1} (MyVect m t))
writeArrGen' write toWrite index (Arr size ptr) = do
                        liftIO1 {io = L IO} (fromPrim (write (conv index) ptr toWrite))
                        pure1 (Arr size ptr)

writeArrGen : (Int -> (1 mem : Ptr t) -> t -> PrimIO ()) ->
                        (t -> (index : Fin m) -> (1 mem : MyVect m t) -> L IO {use=1} (MyVect m t))
writeArrGen f toWrite index = assert_linear (writeArrGen' f toWrite index)

getIndexGen' :  (Int -> (1 mem : Ptr t) -> PrimIO t) ->
                (index : Fin m) -> (MyVect m t) -> L IO {use=1} (Res t (\_ => MyVect m t))
getIndexGen' read index (Arr size ptr) = do
                x <- liftIO1 {io=L IO} (fromPrim $ read (conv index) ptr)
                pure1 (x # (Arr size ptr))

getIndexGen : (Int -> (1 mem : Ptr t) -> PrimIO t) ->
                (index : Fin m) -> (1 mem : MyVect m t) -> L IO {use=1} (Res t (\_ => MyVect m t))
getIndexGen read index = assert_linear (getIndexGen' read index)

createArrGen : (Int -> PrimIO (Ptr t)) -> (size : Nat) -> L IO {use=1} (MyVect (S size) t)
createArrGen create (size) = do
                        x <- liftIO1 {io=L IO} (fromPrim (create (cast (S size))))
                        pure1 (Arr size x)

{-
createArrGen : (Int -> PrimIO (Ptr t)) -> (size : Nat) -> {auto prf : NonZero size} -> L IO {use=1} (MyVect (S size) t)
createArrGen create (size) =  do
                        x <- liftIO1 {io=L IO} (fromPrim (create (cast (size))))
                        pure1 (Arr (size) x)
-}

freeArrGen : ((1 mem : Ptr t) -> PrimIO ()) -> (1 mem : MyVect m t) -> L IO ()
freeArrGen free (Arr s ptr) = liftIO1 {io = L IO} (fromPrim $ free ptr)

interface CType a where
        createArr : (size : Nat) -> L IO {use=1} (MyVect (S size) a)
        getIndex : (index : Fin m) -> (1 mem : (MyVect m a)) -> L IO {use=1} (Res a (\_ => MyVect m a))
        writeArr : a -> (index : Fin m) -> (1 mem : MyVect m a) -> L IO {use=1} (MyVect m a)
        freeArr : (1 mem : MyVect m a) -> L IO ()

--export
CType Int where
        createArr = createArrGen getArray
        getIndex = getIndexGen readPointerOffset
        writeArr = writeArrGen writeOffset
        freeArr = freeArrGen freePointer

CType Char where
        createArr = createArrGen getArrayChar
        getIndex = getIndexGen readPointerOffsetChar
        writeArr = writeArrGen writeOffsetChar
        freeArr = freeArrGen freePointerChar



        

        



export
runLin : (Applicative io, LinearBind io) => (1 _ : L io a) -> io a
runLin = Control.Linear.LIO.run

{-


main : IO ()
main = runLin $ do
        x <- createArr 10
        x <- writeArr (the Char 'c') 5 x
        val # x <- getIndex 5 x
        print val
        freeArr x

x : IO ()
x = runLin $ do
        x <- createArr 10
        x <- writeArr (the Int 100) 5 x
        freeArr x

