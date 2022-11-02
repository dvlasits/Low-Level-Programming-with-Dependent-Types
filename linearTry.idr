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


export
alloc : L {use=1} IO (Ptr Int)
alloc = do
        x <- (liftIO1 {io=L IO} (fromPrim getPointer))
        pure1 x

export
write : Int -> (1 _ : Ptr Int) -> MyPtr
write int ptr = do
                x <- liftIO1 {io=L IO} (fromPrim (writePointer ptr int))
                pure1 x



read' : (Ptr Int) -> L IO {use=1} (Res Int (\_ => Ptr Int))
read' ptr = do
        x <- (liftIO1 {io=L IO} (fromPrim (readPointer ptr)))
        pure1 (x # ptr)


export
read : (1 mem : Ptr Int) -> L IO {use=1} (Res Int (\_ => Ptr Int))
read = assert_linear read'

export
readNum : (1 _ : Ptr Int) -> L IO Int
readNum ptr = liftIO1 {io=L IO} (fromPrim (readPointer ptr))

export
free : (1 _ : Ptr Int) -> L IO {use=Unrestricted} ()
free ptr = do
        x <- (liftIO1 {io=L IO} (fromPrim (freePointer ptr)))
        case x of 
                () => pure ()

-- Need to make Arr constructor private
export
data MyVect : (Nat) -> Type where
        Arr : (size : Nat) -> (NonZero size) -> (1 _ : Ptr Int) -> MyVect size--(S len)

%name MyVect arr, arr1, arr2


export
createArr : (size : Nat) -> {auto prf : NonZero size} -> L IO {use=1} (MyVect size)--{auto 0 prf : NonZero size} -> L IO {use=1} (MyVect size)
createArr (size) = do--(S size) = do
                x <- liftIO1 {io=L IO} (fromPrim (getArray (cast (size))))
                pure1 (Arr size prf x)




conv : (Fin m) -> Int
conv = cast . finToInteger 

getIndex' : (index : Fin m) -> (MyVect m) -> L IO {use=1} (Res Int (\_ => MyVect m))
getIndex' index (Arr s sp ptr) = do
                x <- liftIO1 {io=L IO} (fromPrim $ readPointerOffset (conv index) ptr)
                pure1 (x # (Arr s sp ptr))

export
getIndex : (index : Fin m) -> (1 mem : (MyVect m)) -> L IO {use=1} (Res Int (\_ => MyVect m))
getIndex index = assert_linear (getIndex' index)



writeArr' : Int -> (index : Fin m) -> (MyVect m) -> L IO {use=1} (MyVect m)
writeArr' toWrite index (Arr s sp ptr) = do
                        liftIO1 {io = L IO} (fromPrim (writeOffset (conv index) ptr toWrite))
                        pure1 (Arr s sp ptr)

export
writeArr : Int -> (index : Fin m) -> (1 mem : MyVect m) -> L IO {use=1} (MyVect m)
writeArr toWrite index = assert_linear (writeArr' toWrite index)

export
freeArr : (1 mem : MyVect m) -> L IO ()
freeArr (Arr s sp ptr) = liftIO1 {io = L IO} (fromPrim $ freePointer ptr)


export
runLin : (Applicative io, LinearBind io) => (1 _ : L io a) -> io a
runLin = Control.Linear.LIO.run