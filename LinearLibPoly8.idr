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

data SemiLinPair : Type -> Type -> Type where
    (*?) : a -> (1 _ : b) -> SemiLinPair a b
infixr 4 *?

readLin : (1 _ : SafePointer) -> L IO {use=Linear} (SemiLinPair Int SafePointer)
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


readTP : (1 _ : TrackedPointer parent self) -> L IO {use=1} (SemiLinPair Int (TrackedPointer parent self))
readTP = assert_linear readTP'
    where
        readTP' : (TrackedPointer parent self) -> L IO {use=1} (SemiLinPair Int (TrackedPointer parent self))
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

data LinPair : Type -> Type -> Type where
    (??) : (1 _ : a) -> (1 _ : b) -> LinPair a b
infixr 4 ??

copyTP : (1 _ : TrackedPointer grandparent parent) -> L IO {use=1} (LinPair (TrackedPointer (Just parent) parent) (TrackedPointer grandparent parent))
copyTP = assert_linear copyTP'
    where
        copyTP' : (TrackedPointer grandparent parent) -> L IO {use=1} (LinPair (TrackedPointer (Just parent) parent) (TrackedPointer grandparent parent))
        copyTP' tp = pure1 $ believe_me tp ?? tp

{-
main : IO ()
main = runLin $ do
            _ # ptr <- allocTP
            kid ?? ptr <- copyTP ptr
            kid <- writeTP 50 kid
            int *? ptr <- readTP ptr
            print int
            ptr <- freeKidTP ptr kid
            freeTP ptr
-}

-- Section 3.4 Arrays -- PICK UP FROM HERE

--Array Int primitives

%foreign "C:create_int_array, pointer_functions"
allocIntArray_C : Int -> PrimIO AnyPtr

%foreign "C:write_int_array, pointer_functions"
writeIntArray_C : (loc : Int) -> (to_write : Int) -> (1 _ : AnyPtr) -> PrimIO ()

%foreign "C:read_int_array, pointer_functions"
readIntArray_C : (loc : Int) -> (1 _ : AnyPtr) -> PrimIO Int



private 
data IntArray : Nat -> Maybe SafePointer' -> SafePointer' -> Type where
    CreateIntArray : (len : Nat) -> TrackedPointer parent self -> IntArray (S len) parent self


createIntArray : (size : Nat) -> L IO {use=Linear} (Res SafePointer' (\self => IntArray (S size) Nothing self))
createIntArray size = do
                    ptr <- ConstructSafePointer <$> liftIO1 (fromPrim (allocIntArray_C . cast $ (S size)))
                    pure1 $ (ConstructSafePointer' ptr) # (CreateIntArray size (CreateTrackedPointer ptr))

--Fin is kinda shit
conv : (Fin m) -> Int
conv = cast . finToInteger 

private
getPointerFromIntArray : IntArray _ _ _ -> AnyPtr
getPointerFromIntArray (CreateIntArray _ (CreateTrackedPointer (ConstructSafePointer ptr))) = ptr

writeIntArray : (Fin (S size)) -> Int -> (1 _ : IntArray (S size) parent self) -> L IO {use=Linear} (IntArray (S size) parent self)
writeIntArray loc to_write = assert_linear writeIntArray'
    where
        writeIntArray' : IntArray (S size) parent self -> L IO {use=Linear} (IntArray (S size) parent self)
        writeIntArray' intArray = do
                                let ptr = getPointerFromIntArray intArray
                                liftIO1 (fromPrim (writeIntArray_C (conv loc) to_write ptr))
                                pure1 intArray

readIntArray : (Fin (S size)) -> (1 _ : IntArray (S size) parent self) -> L IO {use=Linear} (SemiLinPair Int (IntArray (S size) parent self))
readIntArray loc = assert_linear readIntArray'
    where
        readIntArray' : IntArray (S size) parent self -> L IO {use=Linear} (SemiLinPair Int (IntArray (S size) parent self))
        readIntArray' intArray = do
                            let ptr = getPointerFromIntArray intArray
                            val <- liftIO1 (fromPrim (readIntArray_C (conv loc) ptr))
                            pure1 $ val *? intArray

freeIntArray : (1 _ : IntArray size Nothing self) -> L IO ()
freeIntArray = assert_linear freeIntArray'
    where
        freeIntArray' : IntArray _ _ _ -> L IO ()
        freeIntArray' intArray = do
                                let ptr = getPointerFromIntArray intArray
                                liftIO1 $ freeUnsafe ptr

freeIntArrayKid : (1 _ : IntArray size grandparent parent) -> (1 _ : IntArray _ (Just parent) _) -> L IO {use=1} (IntArray size grandparent parent)
freeIntArrayKid parent child = do
                            assert_linear consume child
                            pure1 parent
                        where
                            consume : (IntArray _ _ _) -> L IO ()
                            consume _ = pure ()

duplicateIntArray : (1 _ : IntArray size grandparent parent) -> L IO {use=1} (LinPair (IntArray size (Just parent) parent) (IntArray size grandparent parent))
duplicateIntArray = assert_linear duplicateIntArray'
    where
        duplicateIntArray' : IntArray size grandparent parent -> L IO {use=1} (LinPair (IntArray size (Just parent) parent) (IntArray size grandparent parent))
        duplicateIntArray' intArray = pure1 $ believe_me intArray ?? intArray

-- We now get onto polymorphism with typeclasses

private
data SimplePolyArray : Nat -> (elem : Type) -> Maybe SafePointer' -> SafePointer' -> Type where
    CreateSimplePolyArray : (len : Nat) -> (TrackedPointer parent self) -> SimplePolyArray (S len) a parent self

interface CType a where
    createArraySimplePoly : (size : Nat) -> L IO {use=Linear} (Res SafePointer' (\self => SimplePolyArray (S size) a Nothing self))
    readArraySimplePoly : (loc : Fin (S size)) -> (1 _ : SimplePolyArray (S size) a parent self) -> L IO {use=Linear} (SemiLinPair a (SimplePolyArray (S size) a parent self))
    writeArraySimplePoly : (loc : Fin (S size)) -> a -> (1 _ : SimplePolyArray (S size) a parent self) -> L IO {use=Linear} (SimplePolyArray (S size) a parent self)

-- Functions which are equivalent independnt of type of element withn

freeArraySimplePoly : (1 _ : SimplePolyArray _ _ Nothing _) -> L IO {use=Unrestricted} ()
freeArraySimplePoly = assert_linear freeArraySimplePoly'
    where
        freeArraySimplePoly' : (SimplePolyArray _ _ _ _) -> L IO ()
        freeArraySimplePoly' _ = pure ()

duplicateSimplePolyArray : (1 _ : SimplePolyArray size a grandparent parent) -> L IO {use=1} (LinPair (SimplePolyArray size a (Just parent) parent) (SimplePolyArray size a grandparent parent))
duplicateSimplePolyArray = assert_linear duplicateSimplePolyArray'
    where
        duplicateSimplePolyArray' : SimplePolyArray size a grandparent parent -> L IO {use=1} (LinPair (SimplePolyArray size a (Just parent) parent) (SimplePolyArray size a grandparent parent))
        duplicateSimplePolyArray' polyArr = pure1 $ believe_me polyArr ?? polyArr

freeKidSimplePolyArray : (1 _ : SimplePolyArray size a grandparent parent) -> (1 _ : SimplePolyArray _ a (Just parent) _) -> L IO {use=1} (SimplePolyArray size a grandparent parent)
freeKidSimplePolyArray parent child = do
                                assert_linear consume child
                                pure1 parent
                        where
                            consume : (SimplePolyArray _ _ _ _) -> L IO ()
                            consume _ = pure ()

-- Here we create functions to create the above functions when passed the correct C primitive

private
createArraySimplePolyGeneric : (Int -> PrimIO AnyPtr) -> (size : Nat) -> L IO {use=1} (Res SafePointer' (\self => SimplePolyArray (S size) a Nothing self))
createArraySimplePolyGeneric allocArr size = do
                                    ptr <- ConstructSafePointer <$> liftIO1 (fromPrim (allocArr (cast (S size))))
                                    pure1 $ (ConstructSafePointer' ptr) # (CreateSimplePolyArray size (CreateTrackedPointer ptr))

private
getPointerFromSimplePolyArray : (SimplePolyArray _ _ _ _) -> AnyPtr
getPointerFromSimplePolyArray (CreateSimplePolyArray _ (CreateTrackedPointer (ConstructSafePointer ptr))) = ptr

private 
writeArraySimplePolyGeneric : (Int -> a -> (1 _ : AnyPtr) -> PrimIO ()) -> (Fin (S size)) -> a -> (1 _ : SimplePolyArray (S size) a parent self) -> L IO {use=Linear} (SimplePolyArray (S size) a parent self)
writeArraySimplePolyGeneric writeArr loc to_write = assert_linear writeArraySimplePolyGeneric'
    where
        writeArraySimplePolyGeneric' : SimplePolyArray (S size) a parent self -> L IO {use=Linear} (SimplePolyArray (S size) a parent self)
        writeArraySimplePolyGeneric' polyArr = do
                                            let ptr = getPointerFromSimplePolyArray polyArr
                                            liftIO1 (fromPrim (writeArr (conv loc) to_write ptr))
                                            pure1 polyArr

private 
readArraySimplePolyGeneric : (Int -> (1 _ : AnyPtr) -> PrimIO.PrimIO a) -> (Fin (S size)) -> (1 _ : SimplePolyArray (S size) a parent self) -> L IO {use=Linear} (SemiLinPair a (SimplePolyArray (S size) a parent self))
readArraySimplePolyGeneric readArr loc = assert_linear readArraySimplePolyGeneric'
    where
        readArraySimplePolyGeneric' : SimplePolyArray (S size) a parent self -> L IO {use=Linear} (SemiLinPair a (SimplePolyArray (S size) a parent self))
        readArraySimplePolyGeneric' polyArr = do
                                            let ptr = getPointerFromSimplePolyArray polyArr
                                            val <- liftIO1 (fromPrim (readArr (conv loc) ptr))
                                            pure1 $ val *? polyArr

CType Int where
    createArraySimplePoly = createArraySimplePolyGeneric allocIntArray_C
    readArraySimplePoly = readArraySimplePolyGeneric readIntArray_C
    writeArraySimplePoly = writeArraySimplePolyGeneric writeIntArray_C

-- Adding Chars

%foreign "C:create_char_array, pointer_functions"
allocCharArray_C : Int -> PrimIO AnyPtr

%foreign "C:write_char_array, pointer_functions"
writeCharArray_C : (loc : Int) -> (to_write : Char) -> (1 _ : AnyPtr) -> PrimIO ()

%foreign "C:read_char_array, pointer_functions"
readCharArray_C : (loc : Int) -> (1 _ : AnyPtr) -> PrimIO Char

CType Char where
    createArraySimplePoly = createArraySimplePolyGeneric allocCharArray_C
    readArraySimplePoly = readArraySimplePolyGeneric readCharArray_C
    writeArraySimplePoly = writeArraySimplePolyGeneric writeCharArray_C


main : IO ()
main = runLin $ do
            _ # ptr <- createArraySimplePoly 9
            ptr <- writeArraySimplePoly 5 'k' ptr
            ptr2 ?? ptr <- duplicateSimplePolyArray ptr
            val *? ptr2 <- readArraySimplePoly 5 ptr2
            print val
            ptr <- freeKidSimplePolyArray ptr ptr2
            freeArraySimplePoly ptr
            
-- Move onto section 3.6 full polymorphism

-- TODO simple polymorphism with ValidInt + ValidChar
-- This is purely for explanation purposes so does not include code necessary for pointer duplaction

data ValidType' = ValidInt' | ValidChar'

validTypeToType' : ValidType' -> Type
validTypeToType' ValidInt' = Int
validTypeToType' ValidChar' = Char

data PolyArr' : Nat -> ValidType' -> Type where
    CreatePolyArr' : (len : Nat) -> SafePointer -> PolyArr' (S len) validType'

private
createArrayPolyGeneric' : (Int -> PrimIO AnyPtr) -> (size : Nat) -> L IO {use=1} (PolyArr' (S size) a)
createArrayPolyGeneric' allocArr size = do
                                    ptr <- ConstructSafePointer <$> liftIO1 (fromPrim (allocArr (cast (S size))))
                                    pure1 $ (CreatePolyArr' size  ptr)


createPolyArr' : (size : Nat) -> (validType' : ValidType') -> L IO {use=1} (PolyArr' (S size) validType')
createPolyArr' size ValidInt' = createArrayPolyGeneric' allocIntArray_C size
createPolyArr' size ValidChar' = createArrayPolyGeneric' allocCharArray_C size




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

