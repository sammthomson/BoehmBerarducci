module Data.BoehmBerarducci.BList

import Data.BoehmBerarducci.BMaybe
import Data.BoehmBerarducci.BPair
import Data.BoehmBerarducci.BNat

%default total
%access public export


data BList a = MkBList ({r: Type} -> (nil: r) -> (cons: a -> r -> r) -> r)

foldInto : BList a -> (nil: r) -> (cons: a -> r -> r) -> r
foldInto (MkBList xs) = xs

Foldable BList where
  foldr op z xs = foldInto xs z op

cons : a -> BList a -> BList a
cons hd tl = MkBList (\n, c => c hd (foldInto tl n c))

nil : BList a
nil = MkBList (\n, c => n)

(++) : BList a -> BList a -> BList a
xs ++ ys = foldInto xs ys cons

Semigroup (BList a) where
  (<+>) = (++)

Monoid (BList a) where
  neutral = nil

Functor BList where
  map f xs = foldInto xs nil (\x, acc => cons (f x) acc)


isEmpty : BList a -> Bool
isEmpty = foldr (\a, acc => False) True

roll : BMaybe (BPair a (BList a)) -> BList a
roll m = foldInto m nil (bUncurry cons)

unroll : BList a -> BMaybe (BPair a (BList a))
unroll xs = foldInto xs
  nothing
  (\hd, tl => just (pair hd (roll tl)))

head' : BList a -> BMaybe a
head' = map fst . unroll

tail' : BList a -> BMaybe (BList a)
tail' = map snd . unroll

length : BList a -> Int
length = foldr (\_, len => len + 1) 0


reverse : BList a -> BList a
reverse xs = (foldInto xs id op) nil where
  op x prependXsTail = \extra => prependXsTail (cons x extra)

last' : BList a -> BMaybe a
last' = head' . reverse

init' : BList a -> BMaybe (BList a)
init' = map reverse . tail' . reverse

filter : (a -> Bool) -> BList a -> BList a
filter p xs = foldInto xs nil op where
  op a acc = if (p a) then (cons a acc) else acc

takeWhile : (a -> Bool) -> BList a -> BList a
takeWhile p xs = foldInto xs nil op where
  op a acc = if (p a) then (cons a acc) else nil

take : BNat -> BList a -> BList a
take n xs = (foldInto xs (const nil) op) n where
  op a takeXsTail = \k => foldInto (unroll k)
    nil
    (\k' => cons a (takeXsTail k'))

drop : BNat -> BList a -> BList a
drop n xs = (foldInto xs (const nil) op) n where
  op a dropXsTail k = foldInto (unroll k)
    (cons a (dropXsTail z))
    (\k' => dropXsTail k')

dropWhile : (a -> Bool) -> BList a -> BList a
dropWhile p xs = (foldInto xs (const nil) op) True where
  op a dropXsTail = \stillDropping =>
    if (stillDropping && p a) then
      dropXsTail True
    else
      cons a (dropXsTail False)

zipWith : (a -> b -> c) -> BList a -> BList b -> BList c
zipWith f xs ys = (foldInto xs (const nil) op) ys where
    op x zipWithXsTail = \ys' => foldInto (unroll ys')
        nil
        (bUncurry (\y, ysTail => cons (f x y) (zipWithXsTail ysTail)))

zip : BList a -> BList b -> BList (BPair a b)
zip = zipWith pair

Eq a => Eq (BList a) where
  xs == ys = (length xs == length ys) && all (bUncurry (==)) (zip xs ys)

Show a => Show (BList a) where
  show xs = "BList [" ++ (show' xs) ++ "]" where
    show' ys = foldInto (unroll (map show ys))
      ""
      (bUncurry (\y, ysTail => y ++ concatMap ((++) ", ") ysTail))
