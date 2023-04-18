import LinearLibPoly9
import HelpfulLinear
import Control.Linear.LIO
import Prelude.Num
import Data.Fin
import Data.Nat
import System
import System.Clock

import Data.Vect
import BinarySearchFinal




%foreign "C:writeNums, arrayWrite"
writeNums : AnyPtr -> Int -> PrimIO (AnyPtr)



doUpdate' : (IntArray (S size) isParent self) -> L IO {use=1} (IntArray (S size) isParent self)
doUpdate' arr = let (s, ptr) = getPointerUnsafe arr in do
                    _ <- liftIO1 {io=L IO} $ fromPrim $ writeNums ptr (cast s)
                    pure1 arr

doUpdate : (1 _ : IntArray (S size) isParent self) -> L IO {use=1} (IntArray (S size) isParent self)
doUpdate = assert_linear doUpdate'

nano : Integer
nano = 1000000000

f : Nat -> Nat
f x = x
{-
main : IO ()
main = do
    myList <- getArgs
    case myList of 
                [_, a] => (runLin $ do
                                let y = f (cast a)

                                


                                clock <- liftIO1 {io = L IO} $ clockTime Process
                                let t = seconds clock * nano + nanoseconds clock


                                clock <- liftIO1 {io = L IO} (clockTime Process)
                                let t' = seconds clock * nano + nanoseconds clock
                                let time = t' - t
                                print time
                            )
                _ => print "not right arguments"
-}

-- Need to try integers to give it a chance I think, god knows

main : IO ()
main = do
        myList <- getArgs
        case myList of 
                [_, a] => (runLin $ do
                                let y = S (cast a)
                                _ # arr <- createIntArray y
                                arr <- doUpdate arr
                                clock <- liftIO1 {io = L IO} $ clockTime Process
                                val *? arr <- binSearch 0 arr
                                clock' <- liftIO1 {io = L IO} (clockTime Process)
                                let t = seconds clock * nano + nanoseconds clock
                                let t' = seconds clock' * nano + nanoseconds clock'
                                let time = t' - t
                                freeIntArray arr
                                print time
                            )
                _ => print "not right arguments"
