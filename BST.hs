module BST where

{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--exact-data-cons" @-}

import Language.Haskell.Liquid.ProofCombinators

{-@ reflect combine @-}
combine :: Ord k => k -> TotalMap k v -> TotalMap k v -> TotalMap k v
combine pivot m1 m2 k
  | k < pivot = m1 k
  | otherwise = m2 k

{-@
data Tree [height] k v
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

{-@ measure height @-}
{-@ height :: Tree k v -> Nat @-}
height :: Tree k v -> Int
height E           = 0
height (T _ _ l r)
  | hL < hR   = hR + 1
  | otherwise = hL + 1
  where hL = height l
        hR = height r

{-@ reflect emptyTree @-}
emptyTree :: Tree k v
emptyTree = E

{-@ reflect lookupTree @-}
lookupTree :: Ord k => k -> Tree k v -> Maybe v
lookupTree _ E            = Nothing
lookupTree k (T k' v l r)
  | k < k'    = lookupTree k l
  | k > k'    = lookupTree k r
  | otherwise = Just v

{-@ reflect insert @-}
insert :: Ord k => k -> v -> Tree k v -> Tree k v
insert k v E            = T k v E E
insert k v (T k' v' l r)
  | k < k'    = T k' v' (insert k v l) r
  | k > k'    = T k' v' l              (insert k v r)
  | otherwise = T k' v  l              r

{-@ elements' :: l:_ -> t:_ -> _ / [height t] @-}
elements' :: [(k, v)] -> Tree k v -> [(k, v)]
elements' base E           = base
elements' base (T k v l r) = elements' ((k, v) : elements' base r) l

elements :: Tree k v -> [(k, v)]
elements E = elements' [] E
elements (T k v l r) = elements' [] (T k v l r)

-- A correspondence relation between trees and partial maps
-- (total maps to Maybe a)
{-@ reflect tAbs @-}
tAbs :: Ord k => Tree k v -> TotalMap k (Maybe v)
tAbs E           k' = empty Nothing k'
tAbs (T k v l r) k' = update k (Just v) (combine k (tAbs l) (tAbs r)) k'

-- Things to prove
{-
TotalMaps that "correspond" with a BST will get the same lookup results: Not done
If TotalMap m "corresponds" to BST t, then insert k v t corresponds to
  TM.update k (Just v) m: Not done
elements is correct: Not done
The operations respect the BST invariant: Done
-}

{-@ lookupEquiv :: t:_ -> m:{ _ | m = tAbs t} -> k:_ -> {m k = lookupTree k t} @-}
lookupEquiv :: Ord k => Tree k v -> TotalMap k (Maybe v) -> k -> Proof
lookupEquiv E m k = m k
                    ==. tAbs E k
                    ==. empty Nothing k
                    ==. Nothing
                    ==. lookupTree k E
                    *** QED
lookupEquiv (T k' v l r) m k
  | k == k' = m k
              ==. tAbs (T k' v l r) k
              ==. update k' (Just v) (combine k' (tAbs l) (tAbs r)) k
              ==. Just v
              ==. lookupTree k (T k' v l r)
              *** QED
  | k < k' = m k
             ==. tAbs (T k' v l r) k
             ==. update k' (Just v) (combine k' (tAbs l) (tAbs r)) k
             ==. combine k' (tAbs l) (tAbs r) k
             ==. tAbs l k
             ==. lookupTree k l ∵ lookupEquiv l (tAbs l) k
             ==. lookupTree k (T k' v l r)
             *** QED
  | otherwise = m k
                ==. tAbs (T k' v l r) k
                ==. update k' (Just v) (combine k' (tAbs l) (tAbs r)) k
                ==. combine k' (tAbs l) (tAbs r) k
                ==. tAbs r k
                ==. lookupTree k r ∵ lookupEquiv r (tAbs r) k
                ==. lookupTree k (T k' v l r)
                *** QED
                              

-- TODO
{- insertEquiv :: t:_ -> m:{ _ | m = tAbs t} -> k:_ -> v:_ -> k':_
                   -> {update k (Just v) m k' = tAbs (insert k v t) k'}
@-}
insertEquiv :: Ord k => Tree k v -> TotalMap k (Maybe v) -> k -> v -> k -> Proof
insertEquiv E m k v k'
  | k == k' = update k (Just v) m k'
              ==. update k (Just v) m k'
              ==. Just v ∵ updateEq k (Just v) m
              ==. update k (Just v) (combine k (tAbs E) (tAbs E)) k'
              ==. tAbs (T k v E E) k'
              ==. tAbs (insert k v E) k'
              *** QED
  | otherwise = undefined

-- TotalMap.hs is duplicated below, since reflections don't cross module
-- boundaries.

type TotalMap k v = k -> v

{-@ reflect update @-}
update :: Eq k => k -> v -> TotalMap k v -> TotalMap k v
update k v m k'
  | k' == k   = v
  | otherwise = m k'

{-@ reflect empty @-}
empty :: v -> TotalMap k v
empty v _ = v

{-@ updateEq :: k:_ -> v:_ -> m:_ -> {update k v m k == v} @-}
updateEq :: Eq k => k -> v -> TotalMap k v -> Proof
updateEq k v m = update k v m k ==. v *** QED

{-@ updateNeq :: k1:_ -> k2:{ _ | k1 /= k2 } -> v:_ -> m:_ -> {update k1 v m k2 = m k2} @-}
updateNeq :: Eq k => k -> k -> v -> TotalMap k v -> Proof
updateNeq k1 k2 v m = update k1 v m k2 ==. m k2 *** QED

{-@ updateShadow :: k:_ -> v1:_ -> v2:_ -> m:_ -> k':_
  -> {update k v2 (update k v1 m) k' = update k v2 m k'} @-}
updateShadow :: Eq k => k -> v -> v -> TotalMap k v -> k -> Proof
updateShadow k v1 v2 m k'
  | k == k'   = update k v2 (update k v1 m) k'
                ==. v2
                ==. update k v2 m k
                *** QED
  | otherwise =
      update k v2 (update k v1 m) k'
      ==. update k v1 m k' ∵ updateNeq k k' v2 (update k v1 m)
      ==. m k'
      ==. update k v2 m k' ∵ updateNeq k k' v2 m
      *** QED

{-@ updateSame :: k:_ -> m:_ -> k':_ -> {update k (m k) m k' = m k'} @-}
updateSame :: Eq k => k -> TotalMap k v -> k -> Proof
updateSame k m k'
  | k == k'   = update k (m k) m k'
                ==. m k'
                *** QED
  | otherwise = update k (m k) m k'
                ==. m k
                ==. m k'
                *** QED

{-@ updatePermute :: k1:_ -> k2:{ _ | k1 /= k2} -> v1:_ -> v2:_ -> m:_ -> k:_
    -> {update k1 v1 (update k2 v2 m) k = update k2 v2 (update k1 v1 m) k} @-}
updatePermute :: Eq k => k -> k -> v -> v -> TotalMap k v -> k -> Proof
updatePermute k1 k2 v1 v2 m k'
  | k' == k1 = update k1 v1 (update k2 v2 m) k'
               ==. v1
               ==. update k1 v1 m k'
               ==. update k2 v2 (update k1 v1 m) k'
               *** QED
  | k' == k2 = update k1 v1 (update k2 v2 m) k'
               ==. update k2 v2 m k'
               ==. v2
               ==. update k2 v2 (update k1 v1 m) k'
               *** QED
  | otherwise = update k1 v1 (update k2 v2 m) k'
                ==. update k2 v2 m k'
                ==. m k'
                ==. update k1 v1 m k'
                ==. update k2 v2 (update k1 v1 m) k'
                *** QED

{-@ applyEmpty :: v:_ -> k:_ -> {empty v k = v} @-}
applyEmpty :: v -> k -> Proof
applyEmpty v k = empty v k *** QED
