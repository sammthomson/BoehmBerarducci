module Data.BoehmBerarducci.BList

import Data.BoehmBerarducci.BMaybe
import Data.BoehmBerarducci.BPair

%default total
%access public export


data BList a = MkBList ({r: Type} -> (cons: a -> r -> r) -> (nil: r) -> r)


Foldable BList where
  foldr op z (MkBList xs) = xs op z


cons : a -> BList a -> BList a
cons hd (MkBList tl) = MkBList (\c, n => c hd (tl c n))

nil : BList a
nil = MkBList (\c, n => n)

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

roll : BMaybe (BPair a (BList a)) -> BList a
roll = fold nil (fold cons)

unroll : BList a -> BMaybe (BPair a (BList a))
unroll = foldr (\hd, tl => just (pair hd (roll tl))) nothing

head' : BList a -> BMaybe a
head' = map fst . unroll

tail' : BList a -> BMaybe (BList a)
tail' = map snd . unroll

length : BList a -> Int
length = foldr (const ((+) 1)) 0


reverse : BList a -> BList a
reverse xs = foldr op id xs nil where
  op a prependInner = \outer => prependInner (cons a outer)

last' : BList a -> BMaybe a
last' = head' . reverse

init' : BList a -> BMaybe (BList a)
init' = map reverse . tail' . reverse

filter : (a -> Bool) -> BList a -> BList a
filter p = foldr op nil where
  op a acc = if (p a) then (cons a acc) else acc

takeWhile : (a -> Bool) -> BList a -> BList a
takeWhile p = foldr op nil where
  op a acc = if (p a) then (cons a acc) else nil

take : Nat -> BList a -> BList a
take n xs = foldr op (const nil) xs n where
  op a takeXsTail k = case k of
    Z    => nil
    S k' => cons a (takeXsTail k')

drop : Nat -> BList a -> BList a
drop n xs = foldr op (const nil) xs n where
  op a dropXsTail k = case k of
    Z    => cons a (dropXsTail Z)
    S k' => dropXsTail k'

dropWhile : (a -> Bool) -> BList a -> BList a
dropWhile p xs = foldr op (const nil) xs True where
  op a dropXsTail stillDropping =
    if (stillDropping && p a) then
      dropXsTail True
    else
      cons a (dropXsTail False)

zipWith : (a -> b -> c) -> BList a -> BList b -> BList c
zipWith f l r = foldr op (const nil) l r where
  op a zipWithLTail = \r' => fold nil (fold (\b, rTail => cons (f a b) (zipWithLTail rTail))) (unroll r')

zip : BList a -> BList b -> BList (BPair a b)
zip = zipWith pair

Eq a => Eq (BList a) where
  (==) a b = (length a == length b) && all (fold (==)) (zip a b)

Show a => Show (BList a) where
  show xs = "BList [" ++ (show' xs) ++ "]" where
    show' ys = fold "" (fold (\hd, tl => hd ++ concatMap ((++) ", ") tl)) (unroll (map show ys))

