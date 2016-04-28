module Data.BoehmBerarducci.BTuple3

%default total
%access public export


data BTuple3 a b c = MkBTuple3 ({r : Type} -> (a -> b -> c -> r) -> r)

foldInto : BTuple3 a b c -> (tuple: a -> b -> c -> r) -> r
foldInto (MkBTuple3 x) = x

||| aka uncurry
fold : (a -> b -> c -> r) -> BTuple3 a b c -> r
fold f x = foldInto x f

uncurry3 : (a -> b -> c -> r) -> (BTuple3 a b c -> r)
uncurry3 = fold

tuple3 : a -> b -> c -> BTuple3 a b c
tuple3 a b c = MkBTuple3 (\f => f a b c)

curry : (BTuple3 a b c -> r) -> a -> b -> c -> r
curry f a b c = f (tuple3 a b c)

fst : BTuple3 a b c -> a
fst = fold (\a, b, c => a)

snd : BTuple3 a b c -> b
snd = fold (\a, b, c => b)

third : BTuple3 a b c -> c
third = fold (\a, b, c => c)


Functor (BTuple3 a b) where
  map f = fold (\a, b, c => tuple3 a b (f c))

(Eq a, Eq b, Eq c) => Eq (BTuple3 a b c) where
  (==) = fold (\xa, xb, xc =>
           fold (\ya, yb, yc =>
             xa == ya &&
             xb == yb &&
             xc == yc
           )
         )

(Show a, Show b, Show c) => Show (BTuple3 a b c) where
  show = fold (\a, b, c =>
    "BTuple3 (" ++
      show a ++ ", " ++
      show b ++ ", " ++
      show c ++
    ")"
  )
