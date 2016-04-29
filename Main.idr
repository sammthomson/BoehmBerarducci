module Main

import Data.BoehmBerarducci.BList
import Data.BoehmBerarducci.BMaybe
import Data.BoehmBerarducci.BPair
import Data.BoehmBerarducci.BEither
import Data.BoehmBerarducci.BNat
import Data.BoehmBerarducci.BInt
import Data.BoehmBerarducci.BBTree
import Data.BoehmBerarducci.BTuple3

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

exampleTr : BTuple3 Int String (BMaybe BNat)
exampleTr = tuple3 8 "ink" (just 44)

exampleLeft : BEither Int String
exampleLeft = left 1

exampleRight : BEither Int String
exampleRight = right "asdf"

example2 : BNat
example2 = s (s z)

example4 : BNat
example4 = plus example2 example2

exampleNode : BBTree Int String
exampleNode = node 2 (leaf "a") (leaf "b")


main : IO ()
main = do
  printLn exampleNil
  printLn exampleCons
  printLn (zip exampleCons (drop 1 exampleCons))
  printLn (zip (take 2 exampleCons) (reverse exampleCons))
  printLn exampleNothing
  printLn exampleJust
  printLn examplePr
  printLn exampleTr
  printLn exampleLeft
  printLn exampleRight
  printLn example4
  printLn (mult example4 example4)
  printLn (the BInt (pred z))
  printLn (succ (mult (neg example4) (pos example4)))
  printLn exampleNode
  putStrLn ""
