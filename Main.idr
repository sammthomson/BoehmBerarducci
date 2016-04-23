module Main

import Data.BoehmBerarducci.BList
import Data.BoehmBerarducci.BMaybe
import Data.BoehmBerarducci.BPair
import Data.BoehmBerarducci.BEither

%default total
%access public export


exampleList : BList Int
exampleList = cons 1 (cons 2 (cons 3 nil))

exampleNil : BList Int
exampleNil = nil


exampleNothing : BMaybe Int
exampleNothing = nothing

exampleJust : BMaybe Int
exampleJust = just 1


examplePr : BPair Int String
examplePr = pair 1 "asdf"


exampleLeft : BEither Int String
exampleLeft = left 1

exampleRight : BEither Int String
exampleRight = right "asdf"


main : IO ()
main = do
  putStrLn $ show exampleList
  putStrLn $ show exampleNil
  putStrLn $ show exampleJust
  putStrLn $ show exampleNothing
  putStrLn $ show examplePr
  putStrLn $ show exampleLeft
  putStrLn $ show exampleRight
  putStrLn ""
