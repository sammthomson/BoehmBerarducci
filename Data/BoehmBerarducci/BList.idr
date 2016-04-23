module Data.BoehmBerarducci.BList

%default total
%access public export


data BList : Type -> Type where
  BL : ({lst: Type} -> (cons: a -> lst -> lst) -> (nil: lst) -> lst) -> BList a


Foldable BList where
  foldr op z (BL xs) = xs op z


cons : a -> BList a -> BList a
cons hd (BL tl) = BL (\c, n => c hd (tl c n))

nil : BList a
nil = BL (\c, n => n)

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
reverse xs = foldr op id xs nil where
  op elem prependInner = \outer => prependInner (cons elem outer)

last' : BList a -> Maybe a
last' = head' . reverse

init' : BList a -> Maybe (BList a)
init' = map reverse . tail' . reverse

filter : (a -> Bool) -> BList a -> BList a
filter p = foldr op nil where
  op elem acc = if (p elem) then (cons elem acc) else acc

takeWhile : (a -> Bool) -> BList a -> BList a
takeWhile p = foldr op nil where
  op elem acc = if (p elem) then (cons elem acc) else nil

take : Nat -> BList a -> BList a
take n xs = foldr op (const nil) xs n where
  op elem acc k = case k of
    Z    => nil
    S k' => cons elem (acc k')

drop : Nat -> BList a -> BList a
drop n xs = foldr op (const nil) xs n where
  op elem acc k = case k of
    Z    => cons elem (acc Z)
    S k' => acc k'

dropWhile : (a -> Bool) -> BList a -> BList a
dropWhile p xs = foldr op (const nil) xs True where
  op elem acc stillDropping =
    if (stillDropping && p elem) then
      acc True
    else
      cons elem (acc False)

zipWith : (a -> b -> c) -> BList a -> BList b -> BList c
zipWith f l r = foldr op (const nil) l r where
  op a zipWithLTail = \r' => case unroll r' of
    Nothing         => nil
    Just (b, rTail) => cons (f a b) (zipWithLTail rTail)

zip : BList a -> BList b -> BList (a, b)
zip = zipWith MkPair

Eq a => Eq (BList a) where
  (==) a b = (length a == length b) && all (uncurry (==)) (zip a b)

Show a => Show (BList a) where
  show xs = "BL [" ++ (show' xs) ++ "]" where
    show' ys = case unroll (map show ys) of
      Nothing       => ""
      Just (hd, tl) => hd ++ concat (map ((++) ", ") tl)


example : BList Int
example = cons 1 (cons 2 (cons 3 nil))

nilExample : BList Int
nilExample = nil
