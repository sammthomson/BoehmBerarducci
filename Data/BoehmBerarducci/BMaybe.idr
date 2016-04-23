module Data.BoehmBerarducci.BMaybe

%default total
%access public export


data BMaybe a = BM ({m: Type} -> (nothing: m) -> (just: a -> m) -> m)

fold : m -> (a -> m) -> BMaybe a -> m
fold n j (BM x) = x n j

nothing : {a : Type} -> BMaybe a
nothing = BM (\n, j => n)

just : a -> BMaybe a
just a = BM (\n, j => j a)

Functor BMaybe where
  map f = fold nothing (just . f)

Semigroup a => Semigroup (BMaybe a) where
  (<+>) = fold (const nothing) (\a => fold nothing (just . (<+>) a))

Semigroup a => Monoid (BMaybe a) where
  neutral = nothing

Eq a => Eq (BMaybe a) where
  (==) = fold (fold True (const False)) (\a => fold False ((==) a))

Show a => Show (BMaybe a) where
  showPrec d = fold "Nothing" (\a => showCon d "Just" (showArg a))


exampleNothing : BMaybe Int
exampleNothing = nothing

exampleJust : BMaybe Int
exampleJust = just 1
