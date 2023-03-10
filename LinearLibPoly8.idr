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

--Pointer Operations in C


%foreign "C:alloc_pointer, pointer_functions"
alloc_C : PrimIO AnyPtr

%foreign "C:write_int_pointer, pointer_functions"
writeInt_C : Int -> (1 _ : AnyPtr) -> PrimIO ()

%foreign "C:read_int_pointer, pointer_functions"
readInt_C : (1 _ : AnyPtr) -> PrimIO Int

%foreign "C:free_pointer, pointer_functions"
free_C : (1 _ : AnyPtr) -> PrimIO ()

--Section 3.1 Basic Operations

allocUnsafe : IO AnyPtr
allocUnsafe = fromPrim alloc_C

writeUnsafe : Int -> AnyPtr -> IO ()
writeUnsafe to_write ptr = fromPrim $ writeInt_C to_write ptr

readUnsafe : AnyPtr -> IO Int
readUnsafe ptr = fromPrim (readInt_C ptr)

freeUnsafe : AnyPtr -> IO ()
freeUnsafe ptr = fromPrim (free_C ptr)

example1 : IO ()
example1 = do
        myPointer <- allocUnsafe
        freeUnsafe myPointer
        freeUnsafe myPointer

-- Moving onto safety with CPS style 

alloc : ((1 _ : AnyPtr) -> IO Int) -> IO Int
alloc cc = do
            ptr <- allocUnsafe
            cc ptr


free : (1 _ : AnyPtr) -> IO Int
free = assert_linear free'
    where
        free' : AnyPtr -> IO Int
        free' ptr = do
                x <- readUnsafe ptr
                freeUnsafe ptr
                pure x

write : ((1 _ : AnyPtr) -> IO Int) -> Int -> (1 _ : AnyPtr) -> IO Int
write cc to_write = assert_linear write'
    where
        write' : AnyPtr -> IO Int
        write' ptr = do
                writeUnsafe to_write ptr
                cc ptr

read : (Int -> (1 _ : AnyPtr) -> IO Int) -> (1 _ : AnyPtr) -> IO Int
read cc = assert_linear read'
    where
        read' : AnyPtr -> IO Int
        read' ptr = do
                    x <- readUnsafe ptr
                    cc x ptr


example2 : IO Int
example2 = alloc . flip write 10 . read . (\cont, x => cont (x*2)) . write $ free

example3 : IO Int
example3 = alloc (flip write 10 (read ((\cont, x => cont (x*2)) (write free))))

-- Using the SafePointer construction
private
data SafePointer = ConstructSafePointer AnyPtr

allocSP : ((1 _ : SafePointer) -> IO Int) -> IO Int
allocSP cc = do
            ptr <- ConstructSafePointer <$> allocUnsafe
            cc ptr


freeSP : (1 _ : SafePointer) -> IO Int
freeSP (ConstructSafePointer ptr) = free ptr

writeSP : ((1 _ : SafePointer) -> IO Int) -> Int -> (1 _ : SafePointer) -> IO Int
writeSP cc to_write (ConstructSafePointer ptr) = do
                                            writeUnsafe to_write ptr
                                            cc (ConstructSafePointer ptr)

readSP : (Int -> (1 _ : SafePointer) -> IO Int) -> (1 _ : SafePointer) -> IO Int
readSP cc (ConstructSafePointer ptr)= do
                                x <- readUnsafe ptr
                                cc x (ConstructSafePointer ptr)

-- Section 3.2 Linear Monad


allocLin : L IO {use=Linear} SafePointer
allocLin = do
            ptr <- liftIO1 allocUnsafe
            pure1 $ ConstructSafePointer ptr

writeLin : Int -> (1 _ : SafePointer) -> L IO {use=Linear} SafePointer
writeLin to_write (ConstructSafePointer ptr) = do
                                        liftIO1 $ writeUnsafe to_write ptr
                                        pure1 $ ConstructSafePointer ptr


freeLin : (1 _ : SafePointer) -> L IO {use=Unrestricted} ()
freeLin (ConstructSafePointer ptr) = liftIO1 $ freeUnsafe ptr


runLin : (Applicative io, LinearBind io) => (1 _ : L io a) -> io a
runLin = Control.Linear.LIO.run

example4 : IO ()
example4 = runLin $ do
        myPointer <- allocLin
        myPointer' <- writeLin 10 myPointer
        myPointer'' <- writeLin 20 myPointer'
        freeLin myPointer''

example5 : IO ()
example5 = runLin $ do
                myPointer <- allocLin
                myPointer <- writeLin 10 myPointer
                myPointer <- writeLin 20 myPointer
                freeLin myPointer

data LinPair : Type -> Type -> Type where
    (*?) : a -> (1 _ : b) -> LinPair a b
infixr 4 *?

readLin : (1 _ : SafePointer) -> L IO {use=Linear} (LinPair Int SafePointer)
readLin (ConstructSafePointer ptr) = do
                                x <- liftIO1 $ readUnsafe ptr
                                pure1 $ x *? (ConstructSafePointer ptr)

example6 : IO ()
example6 = runLin $ do
            myPointer <- allocLin
            myPointer <- writeLin 10 myPointer
            doubled *? myPointer <- readLin myPointer
            myPointer <- writeLin (doubled * 2) myPointer
            freeLin myPointer


-- Section 3.3 Duplicate Pointer Handling
private
data SafePointer' = ConstructSafePointer' SafePointer

private
data TrackedPointer : Maybe SafePointer' -> SafePointer' -> Type where
        CreateTrackedPointer : (self : SafePointer) -> TrackedPointer parent (ConstructSafePointer' self)

freeTP : (1 _ : TrackedPointer Nothing self) -> L IO {use=Unrestricted} ()
freeTP (CreateTrackedPointer ptr) = freeLin ptr


freeKidTP : (1 _ : TrackedPointer grandparent parent) -> (1 _ : TrackedPointer (Just parent) self) -> L IO {use=Linear} (TrackedPointer grandparent parent)
freeKidTP parent child = do
                assert_linear consume child
                pure1 parent
            where
                consume : (TrackedPointer _ _) -> L IO ()
                consume _ = pure ()

allocTP : L IO {use=Linear} (Res SafePointer' (\self => TrackedPointer Nothing self))
allocTP = do
        ptr <- liftIO1 $ ConstructSafePointer <$> allocUnsafe
        pure1 $ (ConstructSafePointer' ptr) # (CreateTrackedPointer ptr)

private 
forceUnrestricted : L IO {use=1} a -> L IO a
forceUnrestricted act = do
                        x <- act
                        assert_linear pure x


readTP : (1 _ : TrackedPointer parent self) -> L IO {use=1} (LinPair Int (TrackedPointer parent self))
readTP = assert_linear readTP'
    where
        readTP' : (TrackedPointer parent self) -> L IO {use=1} (LinPair Int (TrackedPointer parent self))
        readTP' trackedPointer = do 
                        let (CreateTrackedPointer ptr) = trackedPointer
                        int *? _ <- forceUnrestricted $ readLin ptr
                        pure1 $ int *? trackedPointer

writeTP : Int -> (1 _ : TrackedPointer parent self) -> L IO {use=1} (TrackedPointer parent self)
writeTP int = assert_linear writeTP'
    where
        writeTP' : (TrackedPointer parent self) -> L IO {use=1} (TrackedPointer parent self)
        writeTP' trackedPointer = do
                            let (CreateTrackedPointer ptr) = trackedPointer
                            _ <- forceUnrestricted $ writeLin int ptr
                            pure1 trackedPointer

-- Section 3.4 Arrays -- PICK UP FROM HERE


{-  
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


-}


main : IO ()
main = print 20