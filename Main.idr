module Main

import Data.BoehmBerarducci.BList
import Data.BoehmBerarducci.BMaybe
import Data.BoehmBerarducci.BPair
import Data.BoehmBerarducci.BEither

%default total
%access public export

main : IO ()
main = do
  putStrLn $ show exampleList
  putStrLn $ show exampleNil
  putStrLn $ show exampleJust
  putStrLn $ show exampleNothing
  putStrLn $ show examplePr
  putStrLn $ show exampleL
  putStrLn $ show exampleR
