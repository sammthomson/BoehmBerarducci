module Data.BoehmBerarducci.BSign

%default total
%access public export


data BSign = MkBSign ({r : Type} -> (n : r) -> (z : r) -> (p : r) -> r)

foldInto : BSign -> (n : r) -> (z : r) -> (p : r) -> r
foldInto (MkBSign s) = s

fold : (n : r) -> (z : r) -> (p : r) -> BSign -> r
fold n z p s = foldInto s n z p

negative : BSign
negative = MkBSign (\n, z, p => n)

zero : BSign
zero = MkBSign (\n, z, p => z)

positive : BSign
positive = MkBSign (\n, z, p => p)

isNegative : BSign -> Bool
isNegative = fold True False False

isZero : BSign -> Bool
isZero = fold False True False

isPositive : BSign -> Bool
isPositive = fold False False True

negate : BSign -> BSign
negate = fold positive zero negative

mult : (i, j : BSign) -> BSign
mult = fold negate (const zero) id

toIntegerBSign : BSign -> Integer
toIntegerBSign = fold (-1) 0 1

fromIntegerBSign : Integer -> BSign
fromIntegerBSign i =
  if (i < 0) then
    negative
  else if (i == 0) then
    zero
  else
    positive

Semigroup BSign where
  (<+>) = mult

Monoid BSign where
  neutral = positive

Eq BSign where
  (==) = fold isNegative isZero isPositive

Cast BSign Ordering where
  cast = fold LT EQ GT

Cast Ordering BSign where
  cast LT = negative
  cast EQ = zero
  cast GT = positive

Ord BSign where
  compare a b = foldInto b
    (if isNegative a then EQ else GT)
    (cast a)
    (if isPositive a then EQ else LT)

Show BSign where
  show = fold "BNegative" "BZero" "BPositive"
