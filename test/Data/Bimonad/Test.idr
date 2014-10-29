module Data.Bimonad.Test

import Data.Bimonad

testPair0 : (Int, String)
testPair0 = (42, "hello world")

testPair1 : (Int, String)
testPair1 = (43, "goodbye world")

testPair2 : (Int, String)
testPair2 = (44, "hello again world")

testPair3 : (Int, String)
testPair3 = (45, "goodbye again world")

intFunct : Int -> (Int, String)
intFunct x = (x, "hi")

stringFunct : String -> (Int, String)
stringFunct x = (46, x)

test0 : biunit 42 "hello world" =
        (testPair0, testPair0)
test0 = Refl

test1 : bijoin ((testPair0, testPair1), (testPair2, testPair3)) =
        ((42, "hello world"), (45, "goodbye again world"))
test1 = Refl

test2 : (testPair0, testPair1) >>== (intFunct, stringFunct) =
        ((42, "hi"), (46, "goodbye world"))
test2 = Refl
