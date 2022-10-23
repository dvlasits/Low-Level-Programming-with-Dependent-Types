module Lib1

import System.FFI
import PrimIO
import Prelude
import Control.Linear.LIO
import Control.Monad.State.State
import Control.Monad.State

%foreign "C:getPointer, libsmall"
getPointer : PrimIO (Ptr Int)

%foreign "C:freePointer, libsmall"
freePointer : (1 mem : Ptr Int) -> PrimIO ()

%foreign "C:readNumber, libsmall"
readPointer : (1 mem : Ptr Int) -> PrimIO Int

%foreign "C:writePointer, libsmall"
writePointer : (1 mem : Ptr Int) -> Int -> PrimIO (Ptr Int)

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



--r2 : Int -> (1 mem : Ptr Int) -> IO Int
--r2 i ptr = if i < 50 then freeze ptr else write 20 freeze ptr


--test : IO Int
--test = alloc (write 10 (write 50 (read (r2))))

main : IO ()
main = do
        print 5