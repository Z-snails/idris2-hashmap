module Data.HashMap

import Data.Array16
import public Data.Hashable
import Data.HashMap.Internal as Internal
import Data.List
import Data.String

||| Hash map implemented with Hash-array mapped tries
export
data HashMap : Type -> Type -> Type where
    MkHM : (eq : k -> k -> Bool) -> (hws : Bits64 -> k -> Bits64) -> HashArrayMapTrie k v -> HashMap k v

||| Unsafely get the internals of a HashMap.
export
unsafeFoldHashMap : ((eq : k -> k -> Bool) -> (hws : Bits64 -> k -> Bits64) -> HashArrayMapTrie k v -> r) -> HashMap k v -> r
unsafeFoldHashMap f (MkHM eq hws m) = f eq hws m

||| Lookup the value at `k` if it exists.
export
lookup : k -> HashMap k v -> Maybe v
lookup k (MkHM eq hws m) = Internal.lookup eq hws bitMask0 (hws defaultSalt k) k m

||| Insert a value at a key, replacing it if it already exists.
export
insert : k -> v -> HashMap k v -> HashMap k v
insert k v (MkHM eq hws m) = MkHM eq hws $ Internal.insert eq hws defaultSalt bitMask0 (hws defaultSalt k) k v m

||| Delete the value at a key.
export
delete : k -> HashMap k v -> HashMap k v
delete k (MkHM eq hws m) = MkHM eq hws $ Internal.delete eq hws bitMask0 (hws defaultSalt k) k m

||| Alter the value at a key.
-- TODO: Make faster.
export
alter : k -> (Maybe v -> Maybe v) -> HashMap k v -> HashMap k v
alter k f m = case f (lookup k m) of
    Nothing => delete k m
    Just v => insert k v m

||| Empty HashMap.
export
empty : Eq k => Hashable k => HashMap k v
empty = MkHM (==) hashWithSalt Internal.empty

||| Construct a HashMap from a single key and value.
export
singleton : Eq k => Hashable k => k -> v -> HashMap k v
singleton k v = MkHM (==) hashWithSalt $ Internal.singleton (hashWithSalt defaultSalt k) k v

||| Construct a HashMap from a `Foldable` structure of key-value pairs.
export
fromFoldable : Foldable f => Eq k => Hashable k => f (k, v) -> HashMap k v
fromFoldable kvs =
    MkHM (==) hashWithSalt
        $ foldr (\(k, v) =>
            Internal.insert (==) hashWithSalt defaultSalt bitMask0 (hashWithSalt defaultSalt k) k v)
            Internal.empty kvs

||| Construct a HashMap from a List of key-value pairs.
||| Specialised and inlined for speed.
export
fromList : Eq k => Hashable k => List (k, v) -> HashMap k v
fromList kvs = MkHM (==) hashWithSalt (go kvs Internal.empty)
  where
    go : List (k, v) -> HashArrayMapTrie k v -> HashArrayMapTrie k v
    go [] m = m
    go ((k, v) :: kvs) m =
        go kvs
            $ Internal.insert (==) hashWithSalt defaultSalt bitMask0
                (hashWithSalt defaultSalt k) k v m

||| Fold a hashmap with the key.
||| Note: Due to hashing keys and values are stored in an arbitrary order.
export
foldWithKey : (k -> v -> acc -> acc) -> acc -> HashMap k v -> acc
foldWithKey f z (MkHM _ _ m) = Internal.foldWithKey f z m

-- Should this exist given the lack of order?
export
Foldable (HashMap k) where
    foldl f = foldWithKey (const $ flip f)
    foldr f = foldWithKey (const f)

||| Convert a HashMap to a List of key-value pairs.
export
toList : HashMap k v -> List (k, v)
toList = foldWithKey (\k, v, acc => (k, v) :: acc) []

export covering
Show k => Show v => Show (HashMap k v) where
    showPrec d hm = showCon d "fromList" $ showArg $ Data.HashMap.toList hm

||| Merge 2 hashmaps with a preference for entries in the left map.
export
mergeL : HashMap k v -> HashMap k v -> HashMap k v
mergeL m0 m1 = foldWithKey insert m1 m0

||| Merge 2 hashmaps with a preference for entries in the right map.
export
mergeR : HashMap k v -> HashMap k v -> HashMap k v
mergeR m0 m1 = foldWithKey insert m0 m1

||| Merges 2 hashmaps with a preference for entries in the left map.
Semigroup (HashMap k v) where
    (<+>) = mergeL

||| Merges 2 hashmaps with a preference for entries in the right map.
[HMRightSemigroup] Semigroup (HashMap k v) where
    (<+>) = mergeR

Eq k => Hashable k => Monoid (HashMap k v) where
    neutral = empty

[HMRightMonoid] Eq k => Hashable k => Monoid (HashMap k v) using HMRightSemigroup where
    neutral = empty
