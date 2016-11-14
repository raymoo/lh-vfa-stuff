module BST where

import TotalMap (TotalMap)
import qualified TotalMap as TM

combine :: Ord k => k -> TotalMap k v -> TotalMap k v -> TotalMap k v
combine pivot m1 m2 k
  | k < pivot = m1 k
  | otherwise = m2 k

{-@
data Tree k v
  = E
  | T (x :: k) (_ :: v) (Tree { xl:k | xl < x } v) (Tree { xr:k | xr > x } v)
@-}
data Tree k v = E
              | T k v (Tree k v) (Tree k v)
              deriving (Show)

goodTree :: Tree Int ()
goodTree = T 0 () (T (-1) () E E) E

{-
badTree :: Tree Int ()
badTree = T 0 () (T 1 () E E) E
-}

{-@ measure mmax @-}
mmax :: Ord a => a -> a -> a
mmax x y
  | x > y     = x
  | otherwise = y

{-@ measure height @-}
height :: Tree k v -> Int
height E           = 0
height (T _ _ l r) = mmax (height l) (height r) + 1

emptyTree :: Tree k v
emptyTree = E

lookupTree :: Ord k => k -> Tree k v -> Maybe v
lookupTree _ E            = Nothing
lookupTree k (T k' v l r)
  | k < k'    = lookupTree k l
  | k > k'    = lookupTree k r
  | otherwise = Just v

insert :: Ord k => k -> v -> Tree k v -> Tree k v
insert k v E            = T k v E E
insert k v (T k' v' l r)
  | k < k'    = T k' v' (insert k v l) r
  | k > k'    = T k' v' l              (insert k v r)
  | otherwise = T k' v  l              r

{-@ measure elements' @-}
elements' :: [(k, v)] -> Tree k v -> [(k, v)]
elements' base E           = base
elements' base (T k v l r) = elements' ((k, v) : elements' base r) l

{-@ measure elements @-}
elements :: Tree k v -> [(k, v)]
elements E = elements' [] E
elements (T k v l r) = elements' [] (T k v l r)

tAbs :: Ord k => Tree k v -> TotalMap k (Maybe v)
tAbs E           = TM.empty Nothing
tAbs (T k v l r) = TM.update k (Just v) (combine k (tAbs l) (tAbs r))

-- Things to prove
{-
TotalMaps that "correspond" with a BST will get the same lookup results: Not done
If TotalMap m "corresponds" to BST t, then insert k v t corresponds to
  TM.update k (Just v) m: Not done
elements is correct: Not done
The operations respect the BST invariant: Done
-}
