module Data.Bitraversable.Test

import Data.Bitraversable

testPair0 : (Int, String)
testPair0 = (42, "hello world")

intFunct : Int -> Maybe String
intFunct = Just . show

stringFunct : String -> Maybe String
stringFunct = Just . id

test0 : bitraverse intFunct stringFunct testPair0 =
        Just ("42", "hello world")
test0 = Refl

test1 : bisequence (bimap intFunct stringFunct testPair0) =
        Just ("42", "hello world")
test1 = Refl

test2 : bimapAccumL (\x,y => (x, 1)) (\x,y => (x, "two")) True testPair0 =
        (True, (1, "two"))
test2 = Refl

test3 : bimapAccumR (\x,y => (x, 1)) (\x,y => (x, "two")) True testPair0 =
        (True, (1, "two"))
test3 = Refl
