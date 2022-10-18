import System.FFI
import PrimIO
import Prelude
import Control.Linear.LIO

%foreign "C:getPointer, libsmall"
getPointer : Ptr Int

%foreign "C:freePointer, libsmall"
freePointer : (1 mem : Ptr Int) -> PrimIO ()

%foreign "C:readNumber, libsmall"
readNumber : (1 mem : Ptr Int) -> Int

%foreign "C:writePointer, libsmall"
writePointer : (1 mem : Ptr Int) -> Int -> Ptr Int

%foreign "C:testFunc, libsmall"
testFunc : (Int -> Int) -> Int

%foreign "C:readGlobal, libsmall"
readGlobal : Int

%foreign "C:savePtr, libsmall"
savePtr : (1 mem : Ptr Int) -> Ptr Int

export
alloc : ((1 mem : Ptr Int) -> IO ()) -> IO ()
alloc f = f getPointer

export
write :  Int -> ((1 mem : Ptr Int) -> IO ()) -> (1 mem : Ptr Int) -> IO ()
write int f ptr = let x = writePointer ptr int in f x

export
read : ((1 mem : Ptr Int) -> Int -> IO ()) -> (1 mem : Ptr Int) -> IO ()
read f ptr = let ptr2 = savePtr ptr in f ptr2 readGlobal

export
freeProperPrint : (1 mem : Ptr Int) -> Int -> IO ()
freeProperPrint mem item = fromPrim (freePointer mem)

f2 : () -> IO ()
f2 x = case x of
        () => print 10


finalPart : (1 mem : Ptr Int) -> Int -> IO ()
finalPart ptr int = let (>>=) = io_bind in
    do
        (freeProperPrint ptr int) 
        print 11

readInter : (1 mem : Ptr Int) -> Int -> IO ()
readInter ptr int = write (int+2) (read finalPart) ptr

z : (1 mem : Ptr Int) -> IO ()
z = (write 5 (write 10 (read (readInter))))

main : IO ()
main = alloc z