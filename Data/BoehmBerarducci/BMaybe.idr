module Data.BoehmBerarducci.BMaybe

%default total
%access public export


data BMaybe a = MkBMaybe ({r: Type} -> (nothing: r) -> (just: a -> r) -> r)

foldInto : BMaybe a -> (nothing: r) -> (just: a -> r) -> r
foldInto (MkBMaybe ma) = ma

fold : r -> (a -> r) -> BMaybe a -> r
fold n j ma = foldInto ma n j

nothing : {a : Type} -> BMaybe a
nothing = MkBMaybe (\n, j => n)

just : a -> BMaybe a
just a = MkBMaybe (\n, j => j a)

isNothing : BMaybe a -> Bool
isNothing ma = foldInto ma True (\a => False)

Functor BMaybe where
  map f ma = foldInto ma
    nothing
    (\a => just (f a))

Applicative BMaybe where
  pure = just
  mf <*> ma = foldInto mf
    nothing
    (\f => map f ma)

Monad BMaybe where
  ma >>= f = foldInto ma
    nothing
    (\a => f a)

Semigroup a => Semigroup (BMaybe a) where
  (<+>) = liftA2 (<+>)

Semigroup a => Monoid (BMaybe a) where
  neutral = nothing

Eq a => Eq (BMaybe a) where
  ma == mb = foldInto ma
    (isNothing mb)
    (\a => foldInto mb
      False
      (\b => a == b))

Show a => Show (BMaybe a) where
  showPrec d ma = foldInto ma
    "BNothing"
    (\a => showCon d "BJust" (showArg a))
