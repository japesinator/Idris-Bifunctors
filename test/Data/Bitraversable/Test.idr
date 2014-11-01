module Data.Bitraversable.Test

import Data.Bitraversable

testPair0 : (Int, String)
testPair0 = (42, "hello world")

testEither0 : Either Int String
testEither0 = Left 43

testEither1 : Either Int String
testEither1 = Right "goodbye world"

intFunct : Int -> Maybe String
intFunct = Just . show

stringFunct : String -> Maybe String
stringFunct = Just . id

test0 : bitraverse intFunct stringFunct testEither0 =
        Just (Left "43")
test0 = Refl

test1 : bisequence (bimap intFunct stringFunct testEither1) =
        Just (Right "goodbye world")
test1 = Refl

test2 : bimapAccumL (\x,y => (x, 1)) (\x,y => (x, "two")) True testPair0 =
        (True, (1, "two"))
test2 = Refl

test3 : bimapAccumR (\x,y => (x, 1)) (\x,y => (x, "two")) True testPair0 =
        (True, (1, "two"))
test3 = Refl
