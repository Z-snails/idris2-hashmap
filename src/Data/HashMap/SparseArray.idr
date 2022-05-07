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
fromList : List (Int, a) -> SparseArray a
fromList xs =
    let xs' = sortBy (\(x, _), (y, _) => compare x y) xs
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
findIndex : Int -> SparseArray a -> Int
findIndex idx arr =
    let mask = oneBits `prim__shr_Bits64` cast (64 - idx)
     in cast $ popCount $ arr.bitmap .&. mask

export
index : (idx : Int) -> (arr : SparseArray a) -> Maybe a
index idx arr = if hasEntry idx arr
    then
        let arrIdx = findIndex idx arr
         in Array.index arr.array arrIdx
    else Nothing

export
set : (idx : Int) -> (val : a) -> (arr : SparseArray a) -> SparseArray a
set sparseIdx val arr =
    let arrIdx = findIndex sparseIdx arr
     in if hasEntry sparseIdx arr
        then MkSparseArray
            { bitmap = arr.bitmap
            , array = (update arr.array [(arrIdx, val)])
            }
        else MkSparseArray
            { bitmap = maybe arr.bitmap (setBit arr.bitmap) (intToFin arrIdx)
            , array = insert arrIdx val arr.array
            }

export
length : SparseArray a -> Nat
length arr = popCount arr.bitmap

export
indexes : SparseArray a -> List Int
indexes arr = mapMaybe
    (\idx => if hasEntry idx arr then Just idx else Nothing)
    [0..63]

export
toList : SparseArray a -> List (Int, a)
toList arr = zip (indexes arr) (toList arr.array)

export
Functor SparseArray where
    map f arr = MkSparseArray arr.bitmap (map f arr.array)

export
Show a => Show (SparseArray a) where
    show arr = "[" ++ fastConcat (intersperse ", " (map show (SparseArray.toList arr))) ++ "]"
