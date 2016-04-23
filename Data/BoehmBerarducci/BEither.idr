module Data.BoehmBerarducci.BEither

%default total
%access public export


data BEither : Type -> Type -> Type where
  BE : ({e: Type} -> (l: a -> e) -> (r: b -> e) -> e) -> BEither a b

fold : (a -> e) -> (b -> e) -> BEither a b -> e
fold l r (BE x) = x l r

left : {b : Type} -> a -> BEither a b
left a = BE (\l, r => l a)

right : {a : Type} -> b -> BEither a b
right b = BE (\l, r => r b)

(Eq a, Eq b) => Eq (BEither a b) where
  (==) = fold (\a => fold ((==) a) (const False)) (\b => fold (const False) ((==) b))

(Show a, Show b) => Show (BEither a b) where
  showPrec d e = showCon d name arg where
    name = fold (const "BLeft") (const "BRight") e
    arg = fold showArg showArg e

Functor (BEither a) where
  map f = fold left (right . f)

exampleL : BEither Int String
exampleL = left 1

exampleR : BEither Int String
exampleR = right "asdf"
