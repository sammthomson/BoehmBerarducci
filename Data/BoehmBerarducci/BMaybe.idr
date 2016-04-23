module Data.BoehmBerarducci.BMaybe

%default total
%access public export


data BMaybe a = MkBMaybe ({r: Type} -> (nothing: r) -> (just: a -> r) -> r)

fold : r -> (a -> r) -> BMaybe a -> r
fold n j (MkBMaybe x) = x n j

nothing : {a : Type} -> BMaybe a
nothing = MkBMaybe (\n, j => n)

just : a -> BMaybe a
just a = MkBMaybe (\n, j => j a)

Functor BMaybe where
  map f = fold nothing (just . f)

Semigroup a => Semigroup (BMaybe a) where
  (<+>) = fold (const nothing) (\a => fold nothing (just . (<+>) a))

Semigroup a => Monoid (BMaybe a) where
  neutral = nothing

Eq a => Eq (BMaybe a) where
  (==) = fold (fold True (const False)) (\a => fold False ((==) a))

Show a => Show (BMaybe a) where
  showPrec d = fold "BNothing" (\a => showCon d "BJust" (showArg a))
