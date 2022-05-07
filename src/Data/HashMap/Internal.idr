module Data.HashMap.Internal

import Data.Bits
import public Data.Hashable
import Data.HashMap.SparseArray
import Data.HashMap.Array
import Decidable.Equality

-- import Data.List

%default total

chunkSize : Bits64
chunkSize = 6

-- 10 * 6 + 4
-- 10 groups of 6, then one group of 4
maxDepth : Bits64
maxDepth = 10

{-
Take 6 bits at a time
Starting from least significant bits
-}

||| A non-empty dependently-typed hash-array mapped trie
export
data HAMT : (key : Type) -> (val : key -> Type) -> Type where
    Leaf : (hash : Bits64) -> (k : key) -> (v : val k) -> HAMT key val
    Node : SparseArray (HAMT key val) -> HAMT key val
    Collision : (hash : Bits64) -> Array (k ** val k) -> HAMT key val

%name HAMT hamt

getMask : (depth : Bits64) -> Bits64
getMask depth = baseMask `prim__shl_Bits64` (depth * 5)
  where
    baseMask : Bits64
    baseMask = 0b111111

getIndex : (depth : Bits64) -> (hash : Bits64) -> Int
getIndex depth hash = cast $ (getMask depth .&. hash) `prim__shr_Bits64` (depth * 5)

export
singletonWithHash : (hash : Bits64) -> (k : key) -> val k -> HAMT key val
singletonWithHash = Leaf

export
singleton : Hashable key => (k : key) -> val k -> HAMT key val
singleton k x = singletonWithHash (hash k) k x

parameters
    {0 key : Type}
    {0 val : key -> Type}
    (keyEq : (x : key) -> (y : key) -> Bool)

    lookupEntry : (k : key) -> (idx : Int) -> List (k ** val k) -> Maybe (Int, (k ** val k))
    lookupEntry k idx [] = Nothing
    lookupEntry k idx (entry :: xs) = if keyEq k entry.fst
        then Just (idx, entry)
        else lookupEntry k (idx + 1) xs

    export
    lookupWithHash :
        (k : key) ->
        (hash : Bits64) ->
        (depth : Bits64) ->
        HAMT key val ->
        Maybe (k ** val k)
    lookupWithHash k0 hash0 depth (Leaf hash1 k1 val) = if hash0 == hash1
        then if keyEq k0 k1
            then Just (k1 ** val)
            else Nothing
        else Nothing
    lookupWithHash k0 hash0 depth (Node arr) =
        let idx = getIndex depth hash0
         in index (cast idx) arr >>=
            lookupWithHash k0 hash0 (assert_smaller depth $ depth + 1)
    lookupWithHash k0 hash0 depth (Collision hash1 arr) = if hash0 == hash1
        then
            let arrL = toList arr
             in snd <$> lookupEntry k0 0 arrL
        else Nothing

    export
    lookup :
        Hashable key =>
        (k : key) ->
        HAMT key val ->
        Maybe (k ** val k)
    lookup k hamt = lookupWithHash k (hash k) 0 hamt

    node2 :
        (tree0 : HAMT key val) ->
        (hash0 : Bits64) ->
        (tree1 : HAMT key val) ->
        (hash1 : Bits64) ->
        (depth : Bits64) ->
        HAMT key val
    node2 hamt0 hash0 hamt1 hash1 depth =
        let idx0 = getIndex depth hash0
            idx1 = getIndex depth hash1
         in Node (fromList
            [ (idx0, hamt0)
            , (idx1, hamt1)
            ])

    export
    insertWithHash :
        (k : key) ->
        val k ->
        (hash : Bits64) ->
        (depth : Bits64) ->
        HAMT key val ->
        HAMT key val
    insertWithHash k0 val0 hash0 depth hamt@(Leaf hash1 k1 val1) = if hash0 == hash1
        then Collision hash0 (fromList [(k0 ** val0), (k1 ** val1)])
        else node2 (singletonWithHash hash0 k0 val0) hash0 hamt hash1 depth
    insertWithHash k val hash0 depth (Node arr) =
        let idx = getIndex depth hash0
         in case index idx arr of
            Just hamt => Node $ set idx
                (insertWithHash k val hash0 (assert_smaller depth $ depth + 1) hamt)
                arr
            Nothing => Node $ set idx (singletonWithHash hash0 k val) arr
    insertWithHash k val hash0 depth hamt@(Collision hash1 arr) =
        if hash0 == hash1
            then case lookupEntry k 0 (toList arr) of
                Just (idx, _) => Collision hash1 (update arr [(idx, (k ** val))])
                Nothing => Collision hash1 (append (k ** val) arr)
            else node2 (singletonWithHash hash0 k val) hash0 hamt hash1 depth

    export
    insert :
        Hashable key =>
        (k : key) ->
        val k ->
        HAMT key val ->
        HAMT key val
    insert k x hamt = insertWithHash k x (hash k) 0 hamt

export
trieMap : ({k : _} -> val0 k -> val1 k) -> HAMT key val0 -> HAMT key val1
trieMap f (Leaf hash k v) = Leaf hash k (f v)
trieMap f (Node arr) = Node $ assert_total $ map (trieMap f) arr
trieMap f (Collision hash arr) = Collision hash $ map ({ snd $= f }) arr

{-
-- testing

export
printTree :
    Show key =>
    String ->
    HAMT key val ->
    List String
printTree indent (Leaf hash k val) = ["\{indent}(\{show k}#\{show hash})"]
printTree indent (Node arr) =
    "n" ::
    (SparseArray.toList (map (printTree (indent ++ "  ")) arr)
        >>= \(idx, ls) =>
            "\{indent} \{show idx}:" :: ls)
printTree indent (Collision hash arr) =
    [ "\{indent}c#\{show hash}"
    , (indent
    ++ concat (intersperse ", " $ Array.toList $ map (\(key ** _) => show key) arr))
    ]
-}
