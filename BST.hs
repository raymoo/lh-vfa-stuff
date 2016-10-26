module BST where

data Tree k v = E
              | T (Tree k v) k v (Tree k v)
              deriving (Show)

emptyTree :: Tree k v
emptyTree = E

lookupTree :: k -> Tree k v -> Maybe v
lookupTree _ E            = Nothing
lookupTree k (T l k' v r)
  | k < k'    = lookupTree k l
  | k > k'    = lookupTree k r
  | otherwise = Just v

insert :: k -> v -> Tree k v -> Tree k v
insert k v E            = T E k v E
insert k v (T l k' v' r)
  | k < k'    = T (insert k v l) k' v' r
  | k > k'    = T l              k' v' (insert k v r)
  | otherwise = T l k' v' r

elements :: Tree k v -> [(k, v)]
elements E = []
elements (T l k v r) = elements l ++ (k, v) : elements r
