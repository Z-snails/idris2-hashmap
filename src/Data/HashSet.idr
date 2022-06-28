module Data.HashSet

import Data.HashMap
import Data.Maybe

export
record HashSet k where
    constructor MkHashSet
    hashmap: HashMap k ()

export
empty : Hashable k => Eq k => HashSet k
empty = MkHashSet empty

export
insert : Hashable k => Eq k => k -> HashSet k -> HashSet k
insert k = { hashmap $= insert k () }

export
contains : Hashable k => Eq k => k -> HashSet k -> Bool
contains k (MkHashSet hm) = isJust $ lookup k hm
