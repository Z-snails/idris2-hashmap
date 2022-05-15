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

export
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
  where
    popCount : Bits64 -> Bits64
    popCount x0 =
        let x1 = (x0 .&. 0x5555555555555555) +
                ((x0 `shiftR` 1) .&. 0x5555555555555555)
            x2 = (x1 .&. 0x3333333333333333)
                + ((x1 `shiftR` 2) .&. 0x3333333333333333)
            x3 = ((x2 + (x2 `shiftR` 4)) .&. 0x0F0F0F0F0F0F0F0F)
            x4 = (x3 * 0x0101010101010101) `shiftR` 56
        in cast x4


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
            { bitmap = maybe arr.bitmap (clearBit arr.bitmap) (intToFin arrIdx)
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
toList : SparseArray a -> List (Int, a)
toList arr = zip (indexes arr) (toList arr.array)

export
Functor SparseArray where
    map f arr = MkSparseArray arr.bitmap (map f arr.array)

export
Show a => Show (SparseArray a) where
    show arr = "[" ++ fastConcat (intersperse ", " (map show (SparseArray.toList arr))) ++ "]"

export
Eq a => Eq (SparseArray a) where
    x == y =
        length x == length y
        && all (\idx => index idx x == index idx y) (indexes x)
