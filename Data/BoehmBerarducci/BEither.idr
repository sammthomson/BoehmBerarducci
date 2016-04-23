module Data.BoehmBerarducci.BEither

%default total
%access public export


data BEither a b = MkBEither ({r: Type} -> (left: a -> r) -> (right: b -> r) -> r)

fold : (a -> r) -> (b -> r) -> BEither a b -> r
fold l r (MkBEither x) = x l r

left : {b : Type} -> a -> BEither a b
left a = MkBEither (\l, r => l a)

right : {a : Type} -> b -> BEither a b
right b = MkBEither (\l, r => r b)

(Eq a, Eq b) => Eq (BEither a b) where
  (==) = fold (\a => fold ((==) a) (const False)) (\b => fold (const False) ((==) b))

(Show a, Show b) => Show (BEither a b) where
  showPrec d e = showCon d name arg where
    name = fold (const "BLeft") (const "BRight") e
    arg = fold showArg showArg e

Functor (BEither a) where
  map f = fold left (right . f)
