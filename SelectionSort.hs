module SelectionSort where

import Permutation
import qualified Data.Set as S

{-@ select :: x:a
           -> xs:[a]
           -> (a, [a])<{\y ys ->
                Set_cup (Set_sng x) (listElts xs) = Set_cup (Set_sng y) (listElts ys) &&
                (len xs = len ys)
              }>
@-}
select :: Ord a => a -> [a] -> (a, [a])
select x []     = (x, [])
select x (y:ys)
  | x <= y    = let (j, ys') = select x ys in (j, y:ys')
  | otherwise = let (j, ys') = select y ys in (j, x:ys')

selsort :: Ord a => [a] -> [a]
selsort []     = []
selsort (x:xs) = j : selsort xs'
  where (j, xs') = select x xs

-- Things to prove

-- If `(j, xs') = select x xs`, then `x:xs` and `j:xs'` are permutations: Not done
-- `selsort` is a permutation: Not done
-- If `(j, xs') = select x xs`, then `j` is less than or equal to all elements of xs': Not done
-- `selsort xs` is sorted: Not done
