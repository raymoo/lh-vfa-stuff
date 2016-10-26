module Permutation where

import qualified Data.Set as S

type Proof = ()
trivial :: Proof
trivial = ()

-- Not a sufficient condition for something to be a permutation, but we can work
-- with this for now.
{-@ predicate Permutation X Y = (listElts X = listElts Y) && (len X = len Y)  @-}

-- Should fail
{-@ notPerm :: ([Int], [Int])<{\x y -> Permutation x y}> @-}
notPerm :: ([Int], [Int])
notPerm = ([1,1], [1,2])

-- Should succeed
{-@ goodPerm :: ([Int], [Int])<{\x y -> Permutation x y}> @-}
goodPerm :: ([Int], [Int])
goodPerm = ([1, 2, 3, 4], [3, 4, 2, 1])

{-@ equalLengths :: xs:[a] -> ys:[a] -> { _:Proof | Permutation xs ys }
                 -> { _:Proof | len xs = len ys } @-}
equalLengths :: [a] -> [a] -> Proof -> Proof
equalLengths _ _ _ = trivial

{-@ commutative :: xs:[a] -> ys:[a] -> { _:Proof | Permutation xs ys }
                 -> { _:Proof | Permutation ys xs } @-}
commutative :: [a] -> [a] -> Proof -> Proof
commutative _ _ _ = trivial

-- Things to prove

-- The lengths of permutations are equal: Done
-- Permutation is commutative: Done
-- [1,1] is not a permutation of [1,2]: Done (fails as expected)
-- [1,2,3,4] is a permutation of [3,4,2,1]: Done
