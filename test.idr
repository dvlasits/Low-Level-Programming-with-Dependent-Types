import Data.Vect
import System.FFI


PointNum : Type
PointNum = Struct "pointnum" [("ptr", Ptr Int), ("num", Int)]

%foreign "C:getPointer, libsmall"
getPointer : Ptr Int

%foreign "C:freePointer, libsmall"
freePointer : Ptr Int -> ()

%foreign "C:readNumber, libsmall"
readNumber : (1 mem : Ptr Int) -> Int

%foreign "C:writePointer, libsmall"
writePointer : (1 mem : Ptr Int) -> Int -> Ptr Int

%foreign "C:testFunc, libsmall"
testFunc : (Int -> Int) -> Int

ab : (1 mem : Ptr Int -> IO ()) -> IO ()
ab f = f getPointer

write : (1 mem : Ptr Int) -> Int -> ((1 mem : Ptr Int) -> IO ()) -> IO ()
write ptr int f = let x = writePointer ptr int in f x

read : (1 mem : Ptr Int) -> ((1 mem : Ptr Int) -> Int -> IO ()) -> IO ()
read ptr f = let z = readNumber ptr  in f (getField z "ptr") (getField z "num")

double : Int -> Int
double x = x + x


main : IO ()
main = print $ testFunc double
