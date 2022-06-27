module Data.HashMap.Dependant

import Data.HashMap.Internal

export
data HashDMap : (key : Type) -> (val : key -> Type) -> Type where
    Empty : HashDMap key val
    Trie : HAMT key val -> HashDMap key val

