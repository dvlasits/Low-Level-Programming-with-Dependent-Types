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


MyPtr = L IO {use=1} (Ptr Int)





-- Need to make Arr constructor private
export
data MyVect : Nat -> Type -> Type where
        Arr : (size : Nat) -> (1 _ : Ptr a) -> MyVect (S size) a

%name MyVect arr, arr1, arr2


interface CType a where
        createArr : (size : Nat) -> L IO {use=1} (MyVect (S size) a)
        getIndex : (index : Fin m) -> (1 mem : (MyVect m a)) -> L IO {use=1} (Res a (\_ => MyVect m a))
        writeArr : a -> (index : Fin m) -> (1 mem : MyVect m a) -> L IO {use=1} (MyVect m a)
        freeArr : (1 mem : MyVect m a) -> L IO ()

conv : (Fin m) -> Int
conv = cast . finToInteger 

getIndex' : (index : Fin m) -> (MyVect m Int) -> L IO {use=1} (Res Int (\_ => MyVect m Int))
getIndex' index (Arr size ptr) = do
                x <- liftIO1 {io=L IO} (fromPrim $ readPointerOffset (conv index) ptr)
                pure1 (x # (Arr size ptr))

writeArr' : Int -> (index : Fin m) -> (MyVect m Int) -> L IO {use=1} (MyVect m Int)
writeArr' toWrite index (Arr size ptr) = do
                        liftIO1 {io = L IO} (fromPrim (writeOffset (conv index) ptr toWrite))
                        pure1 (Arr size ptr)

export
CType Int where
        createArr (size) = do
                        x <- liftIO1 {io=L IO} (fromPrim (getArray (cast (S size))))
                        pure1 (Arr size x)
        
        getIndex index = assert_linear (getIndex' index)

        writeArr toWrite index = assert_linear (writeArr' toWrite index)

        freeArr (Arr s ptr) = liftIO1 {io = L IO} (fromPrim $ freePointer ptr)


getIndexChar' : (index : Fin m) -> (MyVect m Char) -> L IO {use=1} (Res Char (\_ => MyVect m Char))
getIndexChar' index (Arr size ptr) = do
                x <- liftIO1 {io=L IO} (fromPrim $ readPointerOffsetChar (conv index) ptr)
                pure1 (x # (Arr size ptr))

writeArrChar' : Char -> (index : Fin m) -> (MyVect m Char) -> L IO {use=1} (MyVect m Char)
writeArrChar' toWrite index (Arr size ptr) = do
                        liftIO1 {io = L IO} (fromPrim (writeOffsetChar (conv index) ptr toWrite))
                        pure1 (Arr size ptr)

export
CType Char where
        createArr (size) = do
                        x <- liftIO1 {io=L IO} (fromPrim (getArrayChar (cast (S size))))
                        pure1 (Arr size x)
        
        getIndex index = assert_linear (getIndexChar' index)

        writeArr toWrite index = assert_linear (writeArrChar' toWrite index)

        freeArr (Arr s ptr) = liftIO1 {io = L IO} (fromPrim $ freePointerChar ptr)


export
runLin : (Applicative io, LinearBind io) => (1 _ : L io a) -> io a
runLin = Control.Linear.LIO.run



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