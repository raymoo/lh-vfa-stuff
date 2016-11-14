module TotalMap where

{-@ LIQUID "--higherorder" @-}

import Language.Haskell.Liquid.ProofCombinators

type TotalMap k v = k -> v

{-@ reflect update @-}
update :: Eq k => k -> v -> TotalMap k v -> TotalMap k v
update k v m k'
  | k' == k   = v
  | otherwise = m k'

{-@ reflect empty @-}
empty :: v -> TotalMap k v
empty v _ = v

{-@ update_eq :: k:_ -> v:_ -> m:_ -> {update k v m k == v} @-}
update_eq :: Eq k => k -> v -> TotalMap k v -> Proof
update_eq k v m = update k v m k ==. v *** QED

{-@ update_neq :: k1:_ -> k2:{ _ | k1 /= k2 } -> v:_ -> m:_ -> {update k1 v m k2 = m k2} @-}
update_neq :: Eq k => k -> k -> v -> TotalMap k v -> Proof
update_neq k1 k2 v m = update k1 v m k2 ==. m k2 *** QED

{-@ update_shadow :: k:_ -> v1:_ -> v2:_ -> m:_ -> k':_
  -> {update k v2 (update k v1 m) k' = update k v2 m k'} @-}
update_shadow :: Eq k => k -> v -> v -> TotalMap k v -> k -> Proof
update_shadow k v1 v2 m k'
  | k == k'   = update k v2 (update k v1 m) k'
                ==. v2
                ==. update k v2 m k
                *** QED
  | otherwise =
      update k v2 (update k v1 m) k'
      ==. update k v1 m k' ∵ update_neq k k' v2 (update k v1 m)
      ==. m k'
      ==. update k v2 m k' ∵ update_neq k k' v2 m
      *** QED

{-@ update_same :: k:_ -> m:_ -> k':_ -> {update k (m k) m k' = m k'} @-}
update_same :: Eq k => k -> TotalMap k v -> k -> Proof
update_same k m k'
  | k == k'   = update k (m k) m k'
                ==. m k'
                *** QED
  | otherwise = update k (m k) m k'
                ==. m k
                ==. m k'
                *** QED

{-@ update_permute :: k1:_ -> k2:{ _ | k1 /= k2} -> v1:_ -> v2:_ -> m:_ -> k:_
    -> {update k1 v1 (update k2 v2 m) k = update k2 v2 (update k1 v1 m) k} @-}
update_permute :: Eq k => k -> k -> v -> v -> TotalMap k v -> k -> Proof
update_permute k1 k2 v1 v2 m k'
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

{-@ apply_empty :: v:_ -> k:_ -> {empty v k = v} @-}
apply_empty :: v -> k -> Proof
apply_empty v k = empty v k *** QED

-- Things to prove
{-
update_eq: k:_ -> v:_ -> m:_ -> {update k v m k = v}
update_neq: k1 -> k2 -> v -> m -> {k1 /= k2 -> update k1 v m k2 = m k2}
update_shadow: k1 -> k2 -> v -> m -> k' -> {update k v2 (update k v1 m) k' = update k v2 m k'}
update_same: update k (m k) m = m
update_permute: k2 /= k1 -> update k1 v1 (update k2 v2 m) =
  update k2 v2 (update k1 v1 m)
apply_empty: empty v k = v
-}
