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
--import Control.Linear.LIO.HasLinearIO
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
writePointer : (1 _ : Ptr Int) -> Int -> PrimIO (Ptr Int)

%foreign "C:writeOffset, libsmall"
writeOffset : Int -> (1 mem : Ptr Int) -> Int -> PrimIO ()


MyPtr = L IO {use=1} (Ptr Int)



alloc : L {use=1} IO (Ptr Int)
alloc = do
        x <- (liftIO1 {io=L IO} (fromPrim getPointer))
        pure1 x

write : Int -> (1 _ : Ptr Int) -> MyPtr
write int ptr = do
                x <- liftIO1 {io=L IO} (fromPrim (writePointer ptr int))
                pure1 x

read : (1 _ : Ptr Int) -> (Int, MyPtr)
read ptr = assert_linear (\ptr => (
        unsafePerformIO (fromPrim (readPointer ptr)), 
        pure1 ptr
        )) ptr


free : (1 _ : Ptr Int) -> L IO {use=Unrestricted} ()
free ptr = do
        x <- (liftIO1 {io=L IO} (fromPrim (freePointer ptr)))
        case x of 
                () => pure ()



main : IO ()
main = Control.Linear.LIO.run $ do
        x <- alloc
        y <- alloc
        free y
        x <- write 10 x
        print 10
        x <- write 20 x
        print 20
        free x
        x3 <- alloc 
        x3 <- write 20 x3
        free x3