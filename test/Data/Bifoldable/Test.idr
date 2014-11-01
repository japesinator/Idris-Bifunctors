module Main

import Data.Bifoldable

testPair0 : (Int, String)
testPair0 = (42, "hello world")

testEither0 : Either Int String
testEither0 = Left 43

testEither1 : Either Int String
testEither1 = Right "goodbye world"

intFunct : Int -> String
intFunct = show

stringFunct : String -> String
stringFunct = id

test0 : bifoldMap show id testEither0 =
        "43"
test0 = Refl

test1 : bifoldr (\x,y => (show x) ++ y) (++) "" testEither1 =
        "goodbye world"
test1 = Refl

test2 : bifoldl (\x,y => x ++ (show y)) (++) "" testPair0 =
        "hello world42"
test2 = Refl

test3 : bifold ("one", "two") =
        "onetwo"
test3 = Refl

test4 : bifoldrM (\x,y => Just ((show x) ++ y))
                 (\x,y => Just (x ++ y)) "" testPair0 =
        Just "hello world42"
test4 = Refl

test5 : bifoldlM (\x,y => Just (x ++ (show y)))
                 (\x,y => Just (x ++ y)) "" testPair0 =
        Just "hello world42"
test5 = Refl

test6 : bitraverse_ Just Just testPair0 =
        Just ()
test6 = Refl

test7 : bimapM_ Just Just testPair0 =
        Just ()
test7 = Refl

test8 : bisequence_ (Just 1, Just "two") =
        Just ()
test8 = Refl

test9 : biList (1, 2) =
        [2,1]
test9 = Refl

test10 : biconcat ([1], [2]) =
         [1,2]
test10 = Refl

test11 : biany ((==) 42) ((==) "goodbye world") testPair0 =
         True
test11 = Refl

test12 : biall ((==) 42) ((==) "goodbye world") testPair0 =
         False
test12 = Refl
