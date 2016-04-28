module Data.BoehmBerarducci.BBTree

import Data.BoehmBerarducci.BEither
import Data.BoehmBerarducci.BTuple3
import Data.BoehmBerarducci.BNat
import Data.BoehmBerarducci.BList

%default total
%access public export


data BBTree n a = MkBBTree ({r : Type} -> (leaf : a -> r) -> (node : n -> r -> r -> r) -> r)

foldInto : BBTree n a -> (leaf: a -> r) -> (node: n -> r -> r -> r) -> r
foldInto (MkBBTree xs) = xs

fold : (leaf: a -> r) -> (node: n -> r -> r -> r) -> BBTree n a -> r
fold a n xs = foldInto xs a n

leaf : a -> BBTree n a
leaf x = MkBBTree (\a, n => a x)

node : (value : n) -> (left : BBTree n a) -> (right : BBTree n a) -> BBTree n a
node v x y = MkBBTree (\l, n => n v (fold l n x)  (fold l n y))

isLeaf : BBTree n a -> Bool
isLeaf = fold (\_ => True) (\_, _, _ => False)

isNode : BBTree n a -> Bool
isNode = fold (\_ => False) (\_, _, _ => True)

roll : BEither a (BTuple3 n (BBTree n a) (BBTree n a)) -> BBTree n a
roll e = foldInto e leaf (uncurry3 node)

unroll : BBTree n a -> BEither a (BTuple3 n (BBTree n a) (BBTree n a))
unroll = fold
  left
  (\v, l, r => right (tuple3 v (roll l) (roll r)))

Semigroup (BBTree () l) where
  (<+>) = node ()

Functor (BBTree n) where
  map f t = foldInto t (leaf . f) node

Applicative (BBTree n) where
  pure = leaf
  mf <*> mx = foldInto mf (\f => map f mx) node

Monad (BBTree n) where
  mx >>= f = foldInto mx f node

Foldable (BBTree n) where
  foldr op acc t = foldInto t op (const (.)) acc

Traversable (BBTree n) where
  traverse f t = foldInto t
    (\a => [| leaf (f a) |])
    (\v, l, r => [| node (pure v) l r |])

depth : BBTree n a -> BNat
depth = fold
  (const 1)
  (\_, l, r => 1 + max l r)

numLeaves : BBTree n a -> BNat
numLeaves = fold (const 1) (const (+))

numNodes : BBTree n a -> BNat
numNodes = fold (const 0) (\_, l, r => 1 + l + r)

reverse : BBTree n a -> BBTree n a
reverse = fold leaf (flip . node)

shape : BBTree n a -> BBTree () ()
shape = fold (\_ => leaf ()) (\_ => node ())

nodes : BBTree n a -> BList n
nodes = fold (const nil) (\v, l, r => l ++ (cons v r))

leaves : BBTree n a -> BList a
leaves = fold pure (const (++))

(Eq a, Eq n) => Eq (BBTree n a) where
  (==) = fold
      (\xa => fold ((==) xa) (\_, _, _ => False))
      (\xv, eqL, eqR, y => foldInto (unroll y)
        (const False)
        (uncurry3 (\yv, yl, yr =>
          xv == yv && eqL yl && eqR yr
        ))
      )

(Show a, Show n) => Show (BBTree n a) where
  showPrec d t = foldInto t
    (\a => showCon d "BLeaf" (showArg a))
    (\v, l, r => showCon d "BNode" (showArg v ++ " (" ++ l ++ ") (" ++ r ++ ")"))
