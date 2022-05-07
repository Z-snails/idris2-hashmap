module Data.HashMap

import Data.HashMap.Internal

data HashMap : (key : Type) -> (val : Type) -> Type where
    Empty : HashMap key val
    Trie : HAMT key (const val) -> HashMap key val

%name HashMap hm

export
lookup : Hashable key => Eq key => key -> HashMap key val -> Maybe val
lookup key Empty = Nothing
lookup key (Trie hamt) = map snd $ lookup (==) key hamt

export
insert : Hashable key => Eq key => key -> val -> HashMap key val -> HashMap key val
insert key val Empty = Trie $ singleton key val
insert key val (Trie hamt) = Trie $ insert (==) key val hamt

export
Functor (HashMap key) where
    map f Empty = Empty
    map f (Trie hamt) = Trie $ trieMap f hamt
