module Main

import Data.Bifunctor.Apply

testPair0 : (Int, String)
testPair0 = (42, "hello world")

testPair1 : (Int, String)
testPair1 = (43, "goodbye world")

testPair2 : (Int, String)
testPair2 = (44, "hello again world")

intFunct : Int -> Int
intFunct i = (*) 3 i

stringFunct : String -> String
stringFunct a = (++) a " from jp"

test0 : ((intFunct, stringFunct) <<.>> testPair0) =
        ((42 * 3), "hello world from jp")
test0 = Refl

test1 : (testPair0 <<. testPair1) =
        testPair0
test1 = Refl

test2 : (testPair0 .>> testPair1) =
         testPair1
test2 = Refl

test3 : (bilift2 (+) (++) testPair0 testPair1) =
        ((42 + 43), "hello worldgoodbye world")
test3 = Refl

test4 : (bilift3 (\x,y,z => x + y + z) (\x,y,z => x ++ y ++ z)
                 testPair0 testPair1 testPair2)            =
        ((42 + 43 + 44), "hello worldgoodbye worldhello again world")
test4 = Refl

test5 : testPair0 <<..>> (intFunct, stringFunct) =
        ((42 * 3), "hello world from jp")
test5 = Refl
