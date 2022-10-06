import Data.Vect
import System.FFI
Number : Type
Number = Struct "number" [("x", Int)]



%foreign "C:getPointer, libsmall"
getPointer : Number

%foreign "C:freePointer, libsmall"
freePointer : Number -> Int

%foreign "C:readNumber, libsmall"
readNumber : Number -> Int

main : IO ()
main = (printLn . freePointer) getPointer


