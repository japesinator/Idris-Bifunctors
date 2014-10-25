module Main

import Data.Bifunctor

testEither0 : Either Int String
testEither0 = Left 42

testEither1 : Either Int String
testEither1 = Right "hello world"

intFunct : Int -> Int
intFunct i = (*) 3 i

stringFunct : String -> String
stringFunct a = (++) a " from jp"

test0 :  ((first intFunct) . (second stringFunct) $ testEither0) =
         (bimap intFunct stringFunct testEither0)
test0 = refl

test1 :  (first intFunct testEither0) =
         (Left (42 * 3))
test1 = refl

test2 :  (first intFunct testEither1) =
         (Right "hello world")
test2 = refl

test3 :  (second stringFunct testEither0) =
         (Left (42))
test3 = refl

test4 :  (second stringFunct testEither1) =
         (Right "hello world from jp")
test4 = refl
