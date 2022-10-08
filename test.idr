import Data.Vect
import System.FFI


PointNum : Type
PointNum = Struct "pointnum" [("ptr", Ptr Int), ("num", Int)]

%foreign "C:getPointer, libsmall"
getPointer : Ptr Int

%foreign "C:freePointer, libsmall"
freePointer : (1 mem : Ptr Int) -> ()

%foreign "C:readNumber, libsmall"
readNumber : (1 mem : Ptr Int) -> Int

%foreign "C:writePointer, libsmall"
writePointer : (1 mem : Ptr Int) -> Int -> Ptr Int

%foreign "C:testFunc, libsmall"
testFunc : (Int -> Int) -> Int

%foreign "C:dumbread, libsmall"
dumbread : Int

%foreign "C:doDumb, libsmall"
doDumb : (1 mem : Ptr Int) -> Ptr Int


ab : ((1 mem : Ptr Int) -> IO ()) -> IO ()
ab f = f getPointer

write :  Int -> ((1 mem : Ptr Int) -> IO ()) -> (1 mem : Ptr Int) -> IO ()
write int f ptr = let x = writePointer ptr int in f x

read : ((1 mem : Ptr Int) -> Int -> IO ()) -> (1 mem : Ptr Int) -> IO ()
read f ptr = let ptr2 = doDumb ptr in f ptr2 dumbread

freeProper : (1 mem : Ptr Int) -> IO ()
freeProper mem = case freePointer mem of
                    () => print ""


finalPart : (1 mem : Ptr Int) -> Int -> IO ()
finalPart ptr int = case freePointer ptr of 
                    () => print int

z : (1 mem : Ptr Int) -> IO ()
z = (write 5 (write 10 (read (finalPart))))

main : IO ()
main = ab z