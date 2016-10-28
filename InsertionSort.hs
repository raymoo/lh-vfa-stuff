module InsertionSort where

import ListUtil
import Permutation
import qualified Data.Set as S

-- The type of lists in ascending order, taken from "Putting Things in Order"
-- [http://goto.ucsd.edu/~rjhala/liquid/haskell/blog/blog/2013/07/29/putting-things-in-order.lhs/]
-- This definition is similar in spirit to the "alternative" sorted definition given in VFA:
{-
Definition sorted' (al: list nat) :=
 ∀ i j, i < j < length al → nth i al 0 ≤ nth j al 0.
-}

{-@ sort :: xs:[a] -> { ys:IncrList a | Permutation xs ys } @-}
sort :: Ord a => [a] -> [a]
sort []     = []
sort (x:xs) = insert x (sort xs)

{-@ insert :: x:a ->
              xs:IncrList a  ->
              { ys:IncrList a | listElts ys = Set_cup (listElts xs) (Set_sng x)
                             && len ys == len xs + 1
              }
@-}
insert :: Ord a => a -> [a] -> [a]
insert v []     = [v]
insert v (x:xs)
  | v <= x      = v : x : xs
  | otherwise   = x : insert v xs

-- Things to prove

-- `insert x l` is a permutation of `x:l`: Somewhat done: bad Permutation definition
-- `sort l` is a permutation of `l`: Somewhat done: bad Permutation definition
-- `insert x l` is sorted, given `l` is sorted: Done
-- `sort l` is sorted: Done
-- VFA has separate proofs of these four for its inductive definition of
-- sortedness, and the definition similar to IncrList.

-- The inductive definition of sortedness from VFA is equivalent to something
-- being an IncrList a: Not done
{-
Inductive sorted: list nat → Prop :=
| sorted_nil:
    sorted nil
| sorted_1: ∀ x,
    sorted (x::nil)
| sorted_cons: ∀ x y l,
   x ≤ y → sorted (y::l) → sorted (x::y::l).
-}

