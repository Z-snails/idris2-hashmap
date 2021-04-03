module Data.HashMap

import Data.Array16
import public Data.Hashable
import Data.List
import Data.String

infix 6 `eq`

infixr 5 .&.
infixr 4 >>

||| Binary and.
%inline
(.&.) : Bits64 -> Bits64 -> Bits64
(.&.) = prim__and_Bits64

||| Right shift.
%inline
(>>) : Bits64 -> Bits64 -> Bits64
(>>) = prim__shr_Bits64

data BitMask
    = BM0
    | BM1
    | BM2
    | BM3
    | BM4
    | BM5
    | BM6
    | BM7
    | BM8
    | BM9
    | BMa
    | BMb
    | BMc
    | BMd
    | BMe
    | BMf

Hash : Type
Hash = Bits64

bitMask : BitMask -> Hash -> Bits64
bitMask mask h = case mask of
    BM0 => 0x000000000000000f .&. h >> 0x00
    BM1 => 0x00000000000000f0 .&. h >> 0x04
    BM2 => 0x0000000000000f00 .&. h >> 0x08
    BM3 => 0x000000000000f000 .&. h >> 0x0c
    BM4 => 0x00000000000f0000 .&. h >> 0x10
    BM5 => 0x0000000000f00000 .&. h >> 0x14
    BM6 => 0x000000000f000000 .&. h >> 0x18
    BM7 => 0x00000000f0000000 .&. h >> 0x1c
    BM8 => 0x0000000f00000000 .&. h >> 0x20
    BM9 => 0x000000f000000000 .&. h >> 0x24
    BMa => 0x00000f0000000000 .&. h >> 0x28
    BMb => 0x0000f00000000000 .&. h >> 0x2c
    BMc => 0x000f000000000000 .&. h >> 0x30
    BMd => 0x00f0000000000000 .&. h >> 0x34
    BMe => 0x0f00000000000000 .&. h >> 0x38
    BMf => 0xf000000000000000 .&. h >> 0x3c

nextBitMask : BitMask -> BitMask
nextBitMask = \case
    BM0 => BM1
    BM1 => BM2
    BM2 => BM3
    BM3 => BM4
    BM4 => BM5
    BM5 => BM6
    BM6 => BM7
    BM7 => BM8
    BM8 => BM9
    BM9 => BMa
    BMa => BMb
    BMb => BMc
    BMc => BMd
    BMd => BMe
    BMe => BMf
    BMf => BM1

isLastBM : BitMask -> Bool
isLastBM = \case
    BMf => True
    _ => False

Salt : Type
Salt = Bits64

-- TODO: get better algorithm
nextSalt : Salt -> Salt
nextSalt = (2 +)

justWhen : Bool -> Lazy a -> Maybe a
justWhen True x = Just x
justWhen False _ = Nothing

joinWhen : Bool -> Lazy (Maybe a) -> Maybe a
joinWhen True x = x
joinWhen False _ = Nothing

||| Internal HashMap that assumes the same hash and Eq is used.
data HashMapInternal k v
    = Empty
    | Leaf Hash k v -- full hash
    | Collision Hash Salt (HashMapInternal k v) -- full hash
    | Node (Array16 (HashMapInternal k v))

namespace TrieShow
    indent : (ind : Nat) -> String
    indent ind = fastConcat $ replicate ind " "

    export
    showTrie : Show k => Show v => (ind : Nat) -> HashMapInternal k v -> String
    showTrie ind Empty = "Empty"
    showTrie ind (Leaf _ k v) = show k ++ " : " ++ show v
    showTrie ind (Collision _ _ m1) =
        "Collision :\n"
        ++ indent (1 + ind) ++ showTrie (1 + ind) m1
    showTrie ind (Node ar) = foldMap (\m1 => indent (1 + ind) ++ showTrie (1 + ind) m1 ++ "\n") ar

-- Hashes aren't equal
node2 : BitMask -> Hash -> k -> v -> Hash -> k -> v -> HashMapInternal k v
node2 bm0 h0 k0 v0 h1 k1 v1 = Node $
    write (bitMask bm0 h0) (Leaf h0 k0 v0) $
    write (bitMask bm0 h1) (Leaf h1 k1 v1) $
    new Empty

mutual
    collision2 : 
        (eq : k -> k -> Bool) ->
        (hashWithSalt : Salt -> k -> Hash) ->
        Salt -> Hash ->
        k -> v -> k -> v ->
        HashMapInternal k v
    collision2 eq hws s0 h k0 v0 k1 v1 =
        let s1 = nextSalt s0
            h0 = hws s1 k0
            h1 = hws s1 k1
            m0 = insertInternal eq hws s1 BM0 h0 k0 v0
                $ insertInternal eq hws s1 BM0 h1 k1 v1
                Empty
        in Collision h s1 m0

    insertInternal :
        (eq : k -> k -> Bool) ->
        (hashWithSalt : Salt -> k -> Hash) ->
        Salt ->
        BitMask ->
        Hash -> k -> v ->
        HashMapInternal k v ->
        HashMapInternal k v
    insertInternal eq hws s0 bm0 h0 k0 v0 m0 = case m0 of
        Empty => Leaf h0 k0 v0
        Leaf h1 k1 v1 => if h0 /= h1
            then node2 bm0 h0 k0 v0 h1 k1 v1
            else if k0 `eq` k1
                then Leaf h0 k0 v0
                else collision2 eq hws s0 h0 k0 v0 k1 v1
        n@(Collision h1 s1 m1) => if h0 == h1
            then Collision h1 s1
                (insertInternal eq hws s1 BM0 (hws s1 k0) k0 v0 m1)
            else -- hashes are different so it can't be the last bit mask
                Node $
                update (bitMask bm0 h0) (insertInternal eq hws s0 (nextBitMask bm0) h0 k0 v0) $
                write (bitMask bm0 h1) n $
                new Empty
        Node ar =>
            Node $ update (bitMask bm0 h0)
            (insertInternal eq hws s0 (nextBitMask bm0) h0 k0 v0) ar

export
lookupInternal :
    (eq : k -> k -> Bool) ->
    (hashWithSalt : Salt -> k -> Hash) ->
    BitMask ->
    Hash -> k ->
    HashMapInternal k v ->
    Maybe v
lookupInternal eq hws bm0 h0 k0 m0 = case m0 of
    Empty => Nothing
    Leaf h1 k1 v => justWhen (h0 == h1 && k0 `eq` k1) v
    Collision h1 s m1 => joinWhen (h0 == h1)
        $ lookupInternal eq hws BM0 (hws s k0) k0 m1
    Node ar => lookupInternal eq hws (nextBitMask bm0) h0 k0 $ index (bitMask bm0 h0) ar

foldWithKeyInternal : (k -> v -> acc -> acc) -> acc -> HashMapInternal k v -> acc
foldWithKeyInternal _ z Empty = z
foldWithKeyInternal f z (Leaf _ k v) = f k v z
foldWithKeyInternal f z (Collision _ _ m) = foldWithKeyInternal f z m
foldWithKeyInternal f z (Node ar) = foldr (flip $ foldWithKeyInternal f) z ar

||| Hash map implemented with Hash-array mapped tries
export
data HashMap : Type -> Type -> Type where
    MkHM : (eq : k -> k -> Bool) -> (hws : Bits64 -> k -> Bits64) -> HashMapInternal k v -> HashMap k v

||| Lookup the value at `k` if it exists.
export
lookup : k -> HashMap k v -> Maybe v
lookup k (MkHM eq hws m) = lookupInternal eq hws BM0 (hws defaultSalt k) k m

||| Insert `v` at `k` in a map.
export
insert : k -> v -> HashMap k v -> HashMap k v
insert k v (MkHM eq hws m) = MkHM eq hws $ insertInternal eq hws defaultSalt BM0 (hws defaultSalt k) k v m

||| Empty HashMap.
export
empty : Eq k => Hashable k => HashMap k v
empty = MkHM (==) hashWithSalt Empty

||| Construct a HashMap from a single key and value.
export
singleton : Eq k => Hashable k => k -> v -> HashMap k v
singleton k v = MkHM (==) hashWithSalt $ Leaf (hashWithSalt defaultSalt k) k v

||| Construct a HashMap from a `Foldable` structure of key-value pairs.
export
fromFoldable : Foldable f => Eq k => Hashable k => f (k, v) -> HashMap k v
fromFoldable kvs =
    MkHM (==) hashWithSalt
        $ foldr (\(k, v) =>
            insertInternal (==) hashWithSalt defaultSalt BM0 (hashWithSalt defaultSalt k) k v)
            Empty kvs

||| Construct a HashMap from a List of key-value pairs.
||| Specialised and inlined for speed.
export
fromList : Eq k => Hashable k => List (k, v) -> HashMap k v
fromList kvs = MkHM (==) hashWithSalt (go kvs Empty)
  where
    go : List (k, v) -> HashMapInternal k v -> HashMapInternal k v
    go [] m = m
    go ((k, v) :: kvs) m =
        go kvs
            $ insertInternal (==) hashWithSalt defaultSalt BM0
                (hashWithSalt defaultSalt k) k v m

||| Fold a hashmap with the key.
||| Note: Due to hashing keys and values are stored in an arbitrary order.
export
foldWithKey : (k -> v -> acc -> acc) -> acc -> HashMap k v -> acc
foldWithKey f z (MkHM _ _ m) = foldWithKeyInternal f z m

-- Should this exist given the lack of order?
export
Foldable (HashMap k) where
    foldl f = foldWithKey (const $ flip f)
    foldr f = foldWithKey (const f)

||| Convert a HashMap to a List of key-value pairs.
export
toList : HashMap k v -> List (k, v)
toList = foldWithKey (\k, v, acc => (k, v) :: acc) []

export
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
