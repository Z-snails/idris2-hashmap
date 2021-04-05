module Data.HashSet

import public Data.Hashable
import Data.HashMap.Internal

||| A hash set.
export
data HashSet : Type -> Type where
    MkHS :
        (eq : k -> k -> Bool) ->
        (hashWithSalt : Salt -> k -> Hash) ->
        HashArrayMapTrie k () ->
        HashSet k

||| Create an empty `HashSet`.
export
empty : Hashable k => Eq k => HashSet k
empty = MkHS (==) hashWithSalt Internal.empty

||| Create a `HashSet` from a single element.
export
singleton : Hashable k => Eq k => k -> HashSet k
singleton k = MkHS (==) hashWithSalt $ Internal.singleton (hashWithSalt defaultSalt k) k ()

||| Returns `True` if the `HashSet` contains provided element.
export
member : k -> HashSet k -> Bool
member k (MkHS eq hws m) = case Internal.lookup eq hws bitMask0 (hws defaultSalt k) k m of
    Nothing => False
    Just _ => True

||| Remove an element from a `HashSet`.
export
delete : k -> HashSet k -> HashSet k
delete k (MkHS eq hws m) = MkHS eq hws $ Internal.delete eq hws bitMask0 (hws defaultSalt k) k m

||| Add an element to a `HashSet`.
export
insert : k -> HashSet k -> HashSet k
insert k (MkHS eq hws m) = MkHS eq hws $ Internal.insert eq hws defaultSalt bitMask0 (hws defaultSalt k) k () m

||| Fold the elements in a `HashSet`
export
foldKeys : (k -> acc -> acc) -> acc -> HashSet k -> acc
foldKeys f z (MkHS _ _ m) = foldWithKey go z m
  where
    go : k -> () -> acc -> acc
    go k _ acc = f k acc