module Data.BoehmBerarducci.BNat

import Data.BoehmBerarducci.BMaybe

%default total
%access public export


data BNat = MkBNat ({r : Type} -> (zero : r) -> (succ : r -> r) -> r)

foldInto : BNat -> (zero : r) -> (succ : r -> r) -> r
foldInto (MkBNat x) = x

fold : (zero : r) -> (succ : r -> r) -> BNat -> r
fold z s n = foldInto n z s

z : BNat
z = MkBNat (\z, s => z)

s : BNat -> BNat
s k = MkBNat (\z, s => s (foldInto k z s))

isZero : BNat -> Bool
isZero = fold True (\_ => False)

isSucc : BNat -> Bool
isSucc = fold False (\_ => True)

roll : BMaybe BNat -> BNat
roll m = foldInto m z s

||| aka pred
unroll : BNat -> BMaybe BNat
unroll n = foldInto n nothing (\p => just (roll p))

pred' : BNat -> BMaybe BNat
pred' = unroll

plus : (m, n : BNat) -> BNat
plus m n = foldInto m n s

mult : (m, n : BNat) -> BNat
mult m n = foldInto m z (plus n)

toIntegerBNat : BNat -> Integer
toIntegerBNat n = foldInto n 0 ((+) 1)

||| Aaaah, recursive!
fromIntegerBNat : Integer -> BNat
fromIntegerBNat i =
  if (i > 0) then
    s (fromIntegerBNat (assert_smaller i (i - 1)))
  else
    z

Num BNat where
  (+) = plus
  (*) = mult
  fromInteger = fromIntegerBNat

Eq BNat where
  m == n = (foldInto m isZero step) n where
    step eqPredM = \n' => foldInto (pred' n') False eqPredM

Ord BNat where
  compare m n = (foldInto m compare0 step) n where
    compare0 k = foldInto k EQ (const LT)
    step comparePred k = foldInto (pred' k) GT comparePred

Show BNat where
  showPrec d n = showCon d "BNat" (showArg (toIntegerBNat n))
