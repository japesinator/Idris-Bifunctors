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

main : IO ()
main = do
  putStrLn $ show $ (==) ((first intFunct) . (second stringFunct) $ testEither0)
                        (bimap intFunct stringFunct testEither0)
  putStrLn $ show $ (==) (first intFunct testEither0)
                        (Left (42 * 3))
  putStrLn $ show $ (==) (first intFunct testEither1)
                        (Right "hello world")
  putStrLn $ show $ (==) (second stringFunct testEither0)
                        (Left (42))
  putStrLn $ show $ (==) (second stringFunct testEither1)
                        (Right "hello world from jp")
