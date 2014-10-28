module Data.Biapplicative.Test

import Data.Biapplicative

testPair0 : (Int, String)
testPair0 = (42, "hello world")

testPair1 : (Int, String)
testPair1 = (43, "goodbye world")

intFunct : Int -> Int
intFunct i = (*) 3 i

stringFunct : String -> String
stringFunct a = (++) a " from jp"

test0 : bipure 42 "hello world" =
        (42, "hello world")
test0 = Refl

test1 : ((intFunct, stringFunct) <<*>> testPair0) =
        ((42 * 3), "hello world from jp")
test1 = Refl

test2 : (testPair0 <<* testPair1) =
        testPair0
test2 = Refl

test3 : (testPair0 *>> testPair1) =
         testPair1
test3 = Refl

test4 : testPair0 <<**>> (intFunct, stringFunct) =
        ((42 * 3), "hello world from jp")
test4 = Refl
