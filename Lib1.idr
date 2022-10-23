module Lib1

import System.FFI
import PrimIO
import Prelude
import Control.Linear.LIO
import Control.Monad.State.State
import Control.Monad.State
import Data.Fin

%foreign "C:getPointer, libsmall"
getPointer : PrimIO (Ptr Int)

%foreign "C:getArray, libsmall"
getArray : Int -> PrimIO (Ptr Int)

%foreign "C:freePointer, libsmall"
freePointer : (1 mem : Ptr Int) -> PrimIO ()

%foreign "C:readNumber, libsmall"
readPointer : (1 mem : Ptr Int) -> PrimIO Int

%foreign "C:readPointerOffset, libsmall"
readPointerOffset : Int -> (1 mem : Ptr Int) -> PrimIO Int

%foreign "C:writePointer, libsmall"
writePointer : (1 mem : Ptr Int) -> Int -> PrimIO (Ptr Int)

%foreign "C:writeOffset, libsmall"
writeOffset : Int -> (1 mem : Ptr Int) -> Int -> PrimIO ()

data MyPtr = W (Ptr Int)

alloc : ((1 mem : MyPtr) -> IO a) -> IO a
alloc f = let (>>=) = io_bind in do
            x <- W <$> (fromPrim getPointer)
            f x

write :  Int -> ((1 mem : MyPtr) -> IO a) -> (1 mem : MyPtr) -> IO a
write int f (W ptr) = let (>>=) = io_bind in do
                x <- fromPrim $ writePointer ptr int
                f (W x)


read' : (Int -> (1 mem : MyPtr) -> IO a) -> MyPtr -> IO a
read' f (W ptr) = do
            x <- fromPrim (readPointer ptr)
            f x (W ptr)

read : (Int -> (1 mem : MyPtr) -> IO a) -> (1 _ : MyPtr) -> IO a
read f = assert_linear (read' f)


free : (1 mem : MyPtr) -> IO ()
free (W ptr) = fromPrim (freePointer ptr)

freeze' : MyPtr -> IO Int
freeze' (W ptr) = do
                x <- fromPrim (readPointer ptr)
                free (W ptr)
                pure x

freeze : (1 mem : MyPtr) -> IO Int
freeze = assert_linear freeze'


data MyVect : (len : Nat) -> Type where
    Arr : (Ptr Int) -> MyVect len



createArr : (size : Nat) -> ((1 _ : MyVect size) -> IO a) -> IO a
createArr size f = do
                    x <- fromPrim (getArray (cast size))
                    f (Arr x)


conv : (Fin m) -> Int
conv = cast . finToInteger 

getIndex' : (index : Fin m) -> (Int -> (1 _ : MyVect m) -> IO a) -> MyVect m -> IO a
getIndex' index f a@(Arr ptr) = do
                    x <- fromPrim $ readPointerOffset (conv index) ptr
                    f x a



getIndex : (index : Fin m) -> (Int -> (1 _ : MyVect m) -> IO a) -> (1 _ : MyVect m) -> IO a
getIndex index f = assert_linear (getIndex' index f)

writeArr' : (index : Fin m) -> Int -> ((1 mem : MyVect m) -> IO a) -> (MyVect m) -> IO a
writeArr' index toWrite f a@(Arr ptr) = do
                    x <- fromPrim $ writeOffset (conv index) ptr toWrite
                    f a

writeArr : (index : Fin m) -> Int -> ((1 mem : MyVect m) -> IO a) -> (1 _ : MyVect m) -> IO a
writeArr index toWrite f = assert_linear (writeArr' index toWrite f)


freeArr : (1 mem : MyVect m) -> IO ()
freeArr (Arr ptr) = fromPrim $ freePointer ptr


x : IO ()
x = createArr 10 (writeArr 9 200 (freeArr))



main : IO ()
main = do
        print 5