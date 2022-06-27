module Data.HashSet

import Data.HashMap

export
record HashSet k where
    constructor MkHashSet
    hashmap: HashMap k ()

export
insert : Hashable k => Eq k => k -> HashSet k -> HashSet k
insert k = { hashmap $= insert k () }
