module Data.BoehmBerarducci.BPair

%default total
%access public export


data BPair : Type -> Type -> Type where
  BP : ({pr: Type} -> (f: a -> b -> pr) -> pr) -> BPair a b

fold : (a -> b -> r) -> BPair a b -> r
fold f (BP x) = x f

pair : a -> b -> BPair a b
pair a b = BP (\f => f a b)


Functor (BPair a) where
  map f = fold (\a, b => pair a (f b))

(Eq a, Eq b) => Eq (BPair a b) where
  (==) = fold (\xa, xb => fold (\ya, yb => xa == ya && xb == yb))

(Show a, Show b) => Show (BPair a b) where
  show = fold (\a, b => "(" ++ show a ++ ", " ++ show b ++ ")")


examplePr : BPair Int String
examplePr = pair 1 "asdf"
