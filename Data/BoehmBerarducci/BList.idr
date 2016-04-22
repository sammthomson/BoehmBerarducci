module Data.BoehmBerarducci.BList

%default total
%access public export


data BList : Type -> Type where
  BL : ({lst: Type} -> (nil: lst) -> (cons: a -> lst -> lst) -> lst) -> BList a


Foldable BList where
  foldr f z (BL xs) = xs z f


nil : BList a
nil = BL const

cons : a -> BList a -> BList a
cons hd (BL tl) = BL (\n, c => c hd (tl n c))

(++) : BList a -> BList a -> BList a
x ++ y = foldr cons y x

Semigroup (BList a) where
  (<+>) = (++)

Monoid (BList a) where
  neutral = nil

Functor BList where
  map f = foldr (cons . f) nil


isEmpty : BList a -> Bool
isEmpty = foldr (const (const False)) True

roll : Maybe (a, BList a) -> BList a
roll = maybe nil (uncurry cons)

unroll : BList a -> Maybe (a, BList a)
unroll = foldr (\hd, tl => Just (hd, roll tl)) Nothing

head' : BList a -> Maybe a
head' = map fst . unroll

tail' : BList a -> Maybe (BList a)
tail' = map snd . unroll

length : BList a -> Int
length = foldr (const ((+) 1)) 0


reverse : BList a -> BList a
reverse xs = foldr f id xs nil where
  f elem acc = \inner => acc (cons elem inner)

last' : BList a -> Maybe a
last' = head' . reverse

init' : BList a -> Maybe (BList a)
init' = map reverse . tail' . reverse

filter : (a -> Bool) -> BList a -> BList a
filter p = foldr f nil where
  f elem acc = if p elem then cons elem acc else acc

takeWhile : (a -> Bool) -> BList a -> BList a
takeWhile p = foldr f nil where
  f elem acc = if p elem then cons elem acc else nil

take : Nat -> BList a -> BList a
take n xs = foldr f (const nil) xs n where
  f elem acc n' = case n' of
    Z   => nil
    S k => cons elem (acc k)

drop : Nat -> BList a -> BList a
drop n xs = foldr f (const nil) xs n where
  f elem acc n' = case n' of
    Z   => cons elem (acc Z)
    S k => acc k

dropWhile : (a -> Bool) -> BList a -> BList a
dropWhile p xs = foldr f (const nil) xs True where
  f elem acc stillDropping =
    if stillDropping && p elem then
      acc True
    else
      cons elem (acc False)

zipWith : (a -> b -> c) -> BList a -> BList b -> BList c
zipWith f l r = foldr op (const nil) l r where
  op a acc r2 = foldr op' nil r2 where
    op' b _ = cons (f a b) (acc (drop 1 r2))

zip : BList a -> BList b -> BList (a, b)
zip = zipWith MkPair

Eq a => Eq (BList a) where
  (==) a b = (length a == length b) && all id (zipWith (==) a b)

Show a => Show (BList a) where
  showPrec d = showCon d "BL" . showArg . toList


example : BList Int
example = cons 1 (cons 2 (cons 3 nil))

