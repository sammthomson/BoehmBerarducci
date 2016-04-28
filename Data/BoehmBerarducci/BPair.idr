module Data.BoehmBerarducci.BPair

%default total
%access public export


data BPair a b = MkBPair ({r: Type} -> (pair: a -> b -> r) -> r)

foldInto : BPair a b -> (pair: a -> b -> r) -> r
foldInto (MkBPair x) = x

||| aka uncurry
fold : (a -> b -> r) -> BPair a b -> r
fold f x = foldInto x f

uncurry : (a -> b -> r) -> (BPair a b -> r)
uncurry = fold

pair : a -> b -> BPair a b
pair a b = MkBPair (\f => f a b)

curry : (BPair a b -> r) -> a -> b -> r
curry f a b = f (pair a b)

fst : BPair a b -> a
fst = fold (\a, b => a)

snd : BPair a b -> b
snd = fold (\a, b => b)

swap : BPair a b -> BPair b a
swap = fold (flip pair)


Functor (BPair a) where
  map f = fold (\a, b => pair a (f b))

(Eq a, Eq b) => Eq (BPair a b) where
  (==) = fold (\xa, xb => fold (\ya, yb => xa == ya && xb == yb))

(Show a, Show b) => Show (BPair a b) where
  show = fold (\a, b => "BPair (" ++ show a ++ ", " ++ show b ++ ")")
