module Data.BoehmBerarducci.BEither

%default total
%access public export


data BEither a b = MkBEither ({r: Type} -> (left: a -> r) -> (right: b -> r) -> r)

foldInto : BEither a b -> (left: a -> r) -> (right: b -> r) -> r
foldInto (MkBEither x) = x

fold : (a -> r) -> (b -> r) -> BEither a b -> r
fold l r x = foldInto x l r

left : {b : Type} -> a -> BEither a b
left a = MkBEither (\l, r => l a)

right : {a : Type} -> b -> BEither a b
right b = MkBEither (\l, r => r b)

isLeft : BEither a b -> Bool
isLeft x = foldInto x (\l => True) (\r => False)

isRight : BEither a b -> Bool
isRight x = foldInto x (\l => False) (\r => True)


Functor (BEither a) where
  map f x = foldInto x
    (\l => left l)
    (\r => right (f r))

(Eq a, Eq b) => Eq (BEither a b) where
  x == y = foldInto x
    (\xl => foldInto y
      (\yl => xl == yl)
      (\yr => False))
    (\xr => foldInto y
      (\yl => False)
      (\yr => xr == yr))

(Show a, Show b) => Show (BEither a b) where
  showPrec d x = showCon d name arg where
    name = foldInto x
      (\l => "BLeft")
      (\r => "BRight")
    arg = foldInto x showArg showArg
