import LinearTry

import Control.Linear.LIO
import Prelude.Num
import Data.Fin
import Data.Nat

{-
e1 : IO ()
e1 = runLin $ do
    x <- createArr 1000
    print 10

e2 : IO ()
e2 = runLin $ do
    x <- createArr 100
    freeArr x 
    freeArr x

e3 : IO ()
e3 = runLin $ do
    x <- createArr 10
    y <- createArr 10
    y <- writeArr 10 100 y
    freeArr y

e4 : IO ()
e4 = runLin $ do
        x <- createArr 10
        x <- createArr 10
        freeArr x-}

main : IO ()
main = runLin $ do
    x <- createArr 100
    x <- writeArr 10 50 x
    val # x <- getIndex 50 x
    print val
    print val 
    print val
    freeArr x