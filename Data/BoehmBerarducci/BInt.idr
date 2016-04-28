module Data.BoehmBerarducci.BInt

import Data.BoehmBerarducci.BSign
import Data.BoehmBerarducci.BNat
import Data.BoehmBerarducci.BPair
import Data.BoehmBerarducci.BMaybe

%default total
%access public export


data BInt = MkBInt ({r : Type} ->
                    (pos : BNat -> r) ->
                    (negS : BNat -> r)
                    -> r)

foldInto : BInt -> (pos : BNat -> r) -> (negS : BNat -> r) -> r
foldInto (MkBInt i) = i

fold : (pos : BNat -> r) -> (negS : BNat -> r) -> BInt -> r
fold p n i = foldInto i p n

pos : BNat -> BInt
pos x = MkBInt (\p, n => p x)

negS : BNat -> BInt
negS x = MkBInt (\p, n => n x)

z : BInt
z = pos z

neg : BNat -> BInt
neg x = foldInto (pred' x) z negS

sign : BInt -> BSign
sign = fold
  (fold zero (const positive))
  (const negative)

mag : BInt -> BNat
mag = fold id s

succ : BInt -> BInt
succ = fold (pos . s) neg

pred : BInt -> BInt
pred i = foldInto i
  (\p => foldInto (pred' p) (neg (s z)) pos)
  (neg . s . s)

plus : (i, j : BInt) -> BInt
plus i j = foldInto i
  (fold j succ)
  (pred . (fold j pred))

fromSignedNat : BPair BSign BNat -> BInt
fromSignedNat = uncurry (\sgn, n => foldInto sgn (neg n) z (pos n))

toSignedNat : BInt -> BPair BSign BNat
toSignedNat i = pair (sign i) (mag i)

mult : (i, j : BInt) -> BInt
mult i j = fromSignedNat (pair (sign i `mult` sign j) (mag i `mult` mag j))

toIntegerBInt : BInt -> Integer
toIntegerBInt = fold toIntegerBNat (negate . toIntegerBNat . s)

fromIntegerBInt : Integer -> BInt
fromIntegerBInt i =
  if (i >= 0) then
    pos (fromIntegerBNat i)
  else
    neg (fromIntegerBNat (-i))

Num BInt where
  (+) = plus
  (*) = mult
  fromInteger = fromIntegerBInt

Neg BInt where
  negate = fold neg (pos . s)
  (-) i j = i + (-j)
  abs = pos . mag

Eq BInt where
  i == j = (toSignedNat i) == (toSignedNat j)

Ord BInt where
  compare i j = cast (sign (i - j))

Show BInt where
  showPrec d n = showCon d "BInt" (showArg (toIntegerBInt n))

Cast BNat BInt where
  cast n = pos n
