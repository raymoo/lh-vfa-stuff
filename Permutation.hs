module Permutation where

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

-- Things to prove

-- The lengths of permutations are equal: Not done
-- Permutation is commutative: Not done
-- [1,1] is not a permutation of [1,2]: Broken?
-- [1,2,3,4] is a permutation of [3,4,2,1]: Broken?
