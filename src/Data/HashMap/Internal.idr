||| Internal functions used by HashMap and HashSet
module Data.HashMap.Internal

import Data.Array16
import public Data.Hashable

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

||| Mask for 4 bits.
export
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

||| Initial bit mask.
export
bitMask0 : BitMask
bitMask0 = BM0

public export
Hash : Type
Hash = Bits64

||| Mask 4 bits.
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

||| Get the `BitMask` for the next 4 bits.
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
    BMf => BM0

||| Is this the last 4 bits?
isLastBM : BitMask -> Bool
isLastBM = \case
    BMf => True
    _ => False

public export
Salt : Type
Salt = Bits64

||| Get the next salt.
-- TODO: get better algorithm
nextSalt : Salt -> Salt
nextSalt = (2 +)

||| Return just if a predicate is satisfied.
justWhen : Bool -> Lazy a -> Maybe a
justWhen True x = Just x
justWhen False _ = Nothing

||| Return `Nothing` is predicate is false, else return other value.
joinWhen : Bool -> Lazy (Maybe a) -> Maybe a
joinWhen True x = x
joinWhen False _ = Nothing

||| Internal Hash-array map trie (HAMT) that assumes the same hash and Eq is used.
export
data HashArrayMapTrie k v
    = Empty
    | Leaf Hash k v -- full hash
    | Collision Hash Salt (HashArrayMapTrie k v) -- full hash
    | Node (Array16 (HashArrayMapTrie k v))

||| An empty HAMT.
export
empty : HashArrayMapTrie k v
empty = Empty

||| A HAMT containing one key and value.
export
singleton : Hash -> k -> v -> HashArrayMapTrie k v
singleton = Leaf

||| Create a HAMT from 2 keys and values, which have different hashes.
node2 : BitMask -> Hash -> k -> v -> Hash -> k -> v -> HashArrayMapTrie k v
node2 bm h0 k0 v0 h1 k1 v1 = Node $
    write (bitMask bm h0) (Leaf h0 k0 v0) $
    write (bitMask bm h1) (Leaf h1 k1 v1) $
    new Empty

mutual
    ||| Create a HAMT from 2 keys and values, where the hashes collide.
    collision2 : 
        (eq : k -> k -> Bool) ->
        (hashWithSalt : Salt -> k -> Hash) ->
        Salt -> Hash ->
        k -> v -> k -> v ->
        HashArrayMapTrie k v
    collision2 eq hws s0 h k0 v0 k1 v1 =
        let s1 = nextSalt s0
            h0 = hws s1 k0
            h1 = hws s1 k1
            m0 = insert eq hws s1 BM0 h0 k0 v0
                $ insert eq hws s1 BM0 h1 k1 v1
                Empty
        in Collision h s1 m0

    export
    ||| Insert a key and value into a HAMT, replacing any existing values.
    insert :
        (eq : k -> k -> Bool) ->
        (hashWithSalt : Salt -> k -> Hash) ->
        Salt ->
        BitMask ->
        Hash ->
        k ->
        v ->
        HashArrayMapTrie k v ->
        HashArrayMapTrie k v
    insert eq hws s0 bm0 h0 k0 v0 m0 = case m0 of
        Empty => Leaf h0 k0 v0
        Leaf h1 k1 v1 => if h0 /= h1
            then node2 bm0 h0 k0 v0 h1 k1 v1
            else if k0 `eq` k1
                then Leaf h0 k0 v0
                else collision2 eq hws s0 h0 k0 v0 k1 v1
        Collision h1 s1 m1 => if h0 == h1
            then Collision h1 s1
                $ insert eq hws s1 BM0 (hws s1 k0) k0 v0 m1
            else -- hashes are different so it can't be the last bit mask
                Node $
                update (bitMask bm0 h0) (insert eq hws s0 (nextBitMask bm0) h0 k0 v0) $
                write (bitMask bm0 h1) m0 $
                new Empty
        Node ar =>
            Node $ update (bitMask bm0 h0)
            (insert eq hws s0 (nextBitMask bm0) h0 k0 v0) ar

||| Delete a key and value from a HAMT.
export
delete :
    (eq : k -> k -> Bool) ->
    (hashWithSalt : Salt -> k -> Hash) ->
    BitMask ->
    Hash -> k ->
    HashArrayMapTrie k v ->
    HashArrayMapTrie k v
delete eq hws bm0 h0 k0 m0 = case m0 of
    Empty => Empty
    Leaf h1 k1 v1 => if h0 == h1 && k0 `eq` k1
        then Empty
        else Leaf h1 k1 v1
    Collision h1 s1 m1 => if h0 == h1
        then Collision h1 s1
            $ delete eq hws BM0 (hws s1 k0) k0 m1
        else m0
    Node ar => Node $ update (bitMask bm0 h0) (delete eq hws (nextBitMask bm0) h0 k0) ar

||| Lookup a value at a key in a HAMT.
export
lookup :
    (eq : k -> k -> Bool) ->
    (hashWithSalt : Salt -> k -> Hash) ->
    BitMask ->
    Hash -> k ->
    HashArrayMapTrie k v ->
    Maybe v
lookup eq hws bm0 h0 k0 m0 = case m0 of
    Empty => Nothing
    Leaf h1 k1 v => justWhen (h0 == h1 && k0 `eq` k1) v
    Collision h1 s m1 => joinWhen (h0 == h1)
        $ lookup eq hws BM0 (hws s k0) k0 m1
    Node ar => lookup eq hws (nextBitMask bm0) h0 k0 $ index (bitMask bm0 h0) ar

||| Fold a HAMT with the key and value.
||| Note: this is based on the order of the hash not the key.
export
foldWithKey : (k -> v -> acc -> acc) -> acc -> HashArrayMapTrie k v -> acc
foldWithKey _ z Empty = z
foldWithKey f z (Leaf _ k v) = f k v z
foldWithKey f z (Collision _ _ m) = foldWithKey f z m
foldWithKey f z (Node ar) = foldr (flip $ foldWithKey f) z ar
