module Main

import Data.BoehmBerarducci.BList
import Data.BoehmBerarducci.BMaybe
import Data.BoehmBerarducci.BPair
import Data.BoehmBerarducci.BEither
import Data.BoehmBerarducci.BNat

%default total
%access public export


exampleNil : BList Int
exampleNil = nil

exampleCons : BList Int
exampleCons = cons 1 (cons 2 (cons 3 nil))


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

example2 : BNat
example2 = (s (s z))

example4 : BNat
example4 = plus example2 example2


main : IO ()
main = do
  putStrLn (show exampleNil)
  putStrLn (show exampleCons)
  putStrLn (show (zip exampleCons (drop (s z) exampleCons)))
  putStrLn (show (zip (take example2 exampleCons) exampleCons))
  putStrLn (show exampleNothing)
  putStrLn (show exampleJust)
  putStrLn (show examplePr)
  putStrLn (show exampleLeft)
  putStrLn (show exampleRight)
  putStrLn (show example4)
  putStrLn (show (mult example4 example4))
  putStrLn ""
