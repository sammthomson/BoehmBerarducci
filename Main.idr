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
  printLn exampleNil
  printLn exampleCons
  printLn (zip exampleCons (drop (s z) exampleCons))
  printLn (zip (take example2 exampleCons) (reverse exampleCons))
  printLn exampleNothing
  printLn exampleJust
  printLn examplePr
  printLn exampleLeft
  printLn exampleRight
  printLn example4
  printLn (mult example4 example4)
  putStrLn ""
