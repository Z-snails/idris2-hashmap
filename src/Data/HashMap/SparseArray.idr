module Data.HashMap.SparseArray

import Data.HashMap.Bits
import public Data.HashMap.Array
import Data.List

%default total

||| An array storing up to 64 elements
public export
record SparseArray a where
    constructor MkSparseArray
    bitmap : Bits64
    array : Array a

%name SparseArray arr

export
empty : SparseArray a
empty = MkSparseArray 0 empty

bits32SortNub : List (Bits32, a) -> List (Bits32, a) -> List (Bits32, a)
bits32SortNub [] acc = acc
bits32SortNub lst@(x :: xs) acc =
    let (lt, gt) = seperate (fst x) xs [] []
     in bits32SortNub (assert_smaller lst lt) $ x :: bits32SortNub (assert_smaller lst gt) acc
  where
    seperate : Bits32 -> List (Bits32, a) -> (lt : List (Bits32, a)) -> (gt : List (Bits32, a)) -> (List (Bits32, a), List (Bits32, a))
    seperate x [] lt gt = (lt, gt)
    seperate x (y :: xs) lt gt = case compare (fst y) x of
        LT => seperate x xs (y :: lt) gt
        EQ => seperate x xs lt gt
        GT => seperate x xs lt (y :: gt)

export %inline
singleton : (Bits32, a) -> SparseArray a
singleton (k, v) = MkSparseArray (bit k) (Array.singleton v)

export
doubleton : (Bits32, a) -> (Bits32, a) -> SparseArray a
doubleton (k0, v0) (k1, v1) = case compare k0 k1 of
    LT => MkSparseArray (bit k0 .|. bit k1) (fromList [v0, v1])
    EQ => singleton (k1, v1)
    GT => MkSparseArray (bit k1 .|. bit k0) (fromList [v1, v0])

export
fromList : List (Bits32, a) -> SparseArray a
fromList xs =
    let xs = bits32SortNub xs []
        bitmap = foldl (\acc, (idx, _) => setBit acc idx) 0 xs
        arr = Array.fromList (map snd xs)
     in MkSparseArray bitmap arr

export
hasEntry : Bits32 -> SparseArray a -> Bool
hasEntry idx arr = testBit arr.bitmap idx

export
findIndex : Bits32 -> Bits64 -> Bits32
findIndex idx bitmap =
    let mask = oneBits `shiftR` cast (64 - idx)
     in cast $ popCount $ bitmap .&. mask

export
index : (idx : Bits32) -> (arr : SparseArray a) -> Maybe a
index idx arr = if hasEntry idx arr
    then
        let arrIdx = findIndex idx arr.bitmap
         in Array.index arr.array arrIdx
    else Nothing

export
set : (idx : Bits32) -> (val : a) -> (arr : SparseArray a) -> SparseArray a
set sparseIdx val arr =
    if hasEntry sparseIdx arr 
        then
            let arrIdx = findIndex sparseIdx arr.bitmap
             in MkSparseArray
                { bitmap = arr.bitmap
                , array = update arr.array [(arrIdx, val)]
                }
        else
            let bitmap = setBit arr.bitmap sparseIdx
                arrIdx = findIndex sparseIdx bitmap
             in MkSparseArray
                { bitmap
                , array = insert arrIdx val arr.array
                }

export
delete : (idx : Bits32) -> (arr : SparseArray a) -> SparseArray a
delete idx arr = if hasEntry idx arr
    then
        let arrIdx = findIndex idx arr.bitmap
         in MkSparseArray
            { bitmap = clearBit arr.bitmap idx
            , array = delete arrIdx arr.array
            }
    else arr

export
length : SparseArray a -> Nat
length arr = cast $ popCount arr.bitmap

export
indexes : SparseArray a -> List Bits32
indexes arr = filter (\idx => hasEntry idx arr) [0..63]

export
Functor SparseArray where
    map f arr = MkSparseArray arr.bitmap (map f arr.array)

export
Foldable SparseArray where
    foldr f z arr = foldr f z arr.array
    foldl f z arr = foldl f z arr.array
    null arr = arr.bitmap == 0
    toList arr = toList arr.array
    foldMap f arr = foldMap f arr.array

export
toList : SparseArray a -> List (Bits32, a)
toList arr = zip (indexes arr) (toList arr)

export
Show a => Show (SparseArray a) where
    show arr = "[" ++ fastConcat (intersperse ", " (map show (SparseArray.toList arr))) ++ "]"

export
Eq a => Eq (SparseArray a) where
    x == y =
        length x == length y
        && all (\idx => index idx x == index idx y) (indexes x)
