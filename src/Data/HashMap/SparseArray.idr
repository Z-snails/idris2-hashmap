module Data.HashMap.SparseArray

import public Data.HashMap.Array
import Data.Bits
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
empty = MkSparseArray zeroBits empty

intToFin : {n : _} -> Int -> Maybe (Fin n)
intToFin x = integerToFin (cast x) n

intSortNub : List (Int, a) -> List (Int, a) -> List (Int, a)
intSortNub [] acc = acc
intSortNub lst@(x :: xs) acc =
    let (lt, gt) = seperate (fst x) xs [] []
     in intSortNub (assert_smaller lst lt) $ x :: intSortNub (assert_smaller lst gt) acc
  where
    seperate : Int -> List (Int, a) -> (lt : List (Int, a)) -> (gt : List (Int, a)) -> (List (Int, a), List (Int, a))
    seperate x [] lt gt = (lt, gt)
    seperate x (y :: xs) lt gt = case compare (fst y) x of
        LT => seperate x xs (y :: lt) gt
        EQ => seperate x xs lt gt
        GT => seperate x xs lt (y :: gt)

getBit : Int -> Bits64
getBit k = 1 `prim__shl_Bits64` cast k

export %inline
singleton : (Int, a) -> SparseArray a
singleton (k, v) = MkSparseArray (getBit k) (Array.singleton v)

export
doubleton : (Int, a) -> (Int, a) -> SparseArray a
doubleton (k0, v0) (k1, v1) = case compare k0 k1 of
    LT => MkSparseArray (getBit k0 .|. getBit k1) (fromList [v0, v1])
    EQ => singleton (k1, v1)
    GT => MkSparseArray (getBit k1 .|. getBit k0) (fromList [v1, v0])

export
fromList : List (Int, a) -> SparseArray a
fromList xs =
    let xs = intSortNub xs []
        bitmap =
            foldl
                (\acc, (idx, _) => the Bits64 $ 
                    maybe
                        acc
                        (setBit acc)
                        (intToFin idx))
                zeroBits
                xs
        arr = Array.fromList (map snd xs)
     in MkSparseArray bitmap arr

export
hasEntry : Int -> SparseArray a -> Bool
hasEntry idx arr = case intToFin idx of
    Nothing => False
    Just idx => testBit arr.bitmap idx

export
findIndex : Int -> Bits64 -> Int
findIndex idx bitmap =
    let mask = oneBits `prim__shr_Bits64` cast (64 - idx)
     in cast $ popCount $ bitmap .&. mask

export
index : (idx : Int) -> (arr : SparseArray a) -> Maybe a
index idx arr = if hasEntry idx arr
    then
        let arrIdx = findIndex idx arr.bitmap
         in Array.index arr.array arrIdx
    else Nothing

export
set : (idx : Int) -> (val : a) -> (arr : SparseArray a) -> SparseArray a
set sparseIdx val arr =
    if hasEntry sparseIdx arr 
        then
            let arrIdx = findIndex sparseIdx arr.bitmap
             in MkSparseArray
                { bitmap = arr.bitmap
                , array = update arr.array [(arrIdx, val)]
                }
        else
            let bitmap = maybe arr.bitmap (setBit arr.bitmap) (intToFin sparseIdx)
                arrIdx = findIndex sparseIdx bitmap
             in MkSparseArray
                { bitmap
                , array = insert arrIdx val arr.array
                }

export
delete : (idx : Int) -> (arr : SparseArray a) -> SparseArray a
delete idx arr = if hasEntry idx arr
    then
        let arrIdx = findIndex idx arr.bitmap
         in MkSparseArray
            { bitmap = maybe arr.bitmap (clearBit arr.bitmap) (intToFin idx)
            , array = delete arrIdx arr.array
            }
    else arr

export
length : SparseArray a -> Nat
length arr = popCount arr.bitmap

export
indexes : SparseArray a -> List Int
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
toList : SparseArray a -> List (Int, a)
toList arr = zip (indexes arr) (toList arr)

export
Show a => Show (SparseArray a) where
    show arr = "[" ++ fastConcat (intersperse ", " (map show (SparseArray.toList arr))) ++ "]"

export
Eq a => Eq (SparseArray a) where
    x == y =
        length x == length y
        && all (\idx => index idx x == index idx y) (indexes x)
