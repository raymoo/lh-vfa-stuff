module SelectionSort (selsort) where

{-@ LIQUID "--maxparams=5" @-}

import ListUtil
import Permutation
import qualified Data.Set as S

{-@ data OP a = OP { opElt :: a, opList :: [{ x:a | opElt <= x }] } @-}
data OP a = OP { opElt :: a, opList :: [a] }

{-@ predicate OpElts O = Set_cup (Set_sng (opElt O)) (listElts (opList O)) @-}
{-@ predicate ConsElts X XS = Set_cup (Set_sng X) (listElts XS) @-}

{-@ select :: x:a
           -> xs:[a]
           -> { op:OP a | OpElts op = ConsElts x xs && len (opList op) = len xs && opElt op <= x }
@-}
select :: Ord a => a -> [a] -> OP a
select x []     = OP x []
select x (y:ys)
  | x <= y    = let OP j ys' = select x ys in OP j (y:ys')
  | otherwise = let OP j ys' = select y ys in OP j (x:ys')

{-@ selsort :: xs:[a] -> { ys : IncrList a | Permutation xs ys } @-}
selsort :: Ord a => [a] -> [a]
selsort []     = []
selsort (x:xs) = j : selsort xs'
  where OP j xs' = select x xs

-- Things to prove

-- If `(j, xs') = select x xs`, then `x:xs` and `j:xs'` are permutations:
--   Somewhat done (bad Permutation definition)
-- `selsort` is a permutation: Done
-- If `(j, xs') = select x xs`, then `j` is less than or equal to all elements of xs': Done
-- `selsort xs` is sorted: Somewhat done (bad Permutation definition)
