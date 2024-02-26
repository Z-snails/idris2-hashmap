module Data.HashMap.Array

import Data.Fin
import Data.IOArray.Prims
import Data.List

%default total

%inline
unsafeNewArray : Int -> IO (ArrayData a)
unsafeNewArray len = fromPrim $ prim__newArray len (believe_me ())

%inline
unsafeInlinePerformIO : IO a -> a
unsafeInlinePerformIO act =
    let MkIORes res %MkWorld = toPrim act %MkWorld
     in res

-- Copy from[fromStart..fromStop) to to[toStart..)
%spec f
copyFromArrayBy :
    (from : ArrayData a) ->
    (to : ArrayData b) ->
    (fromStart : Int) ->
    (toStart : Int) ->
    (fromStop : Int) ->
    (f : a -> b) ->
    IO ()
copyFromArrayBy from to fromStart toStart fromStop f = if fromStart < fromStop
    then do
        val <- fromPrim $ prim__arrayGet from fromStart
        fromPrim $ prim__arraySet to toStart (f val)
        copyFromArrayBy from to (assert_smaller fromStart $ fromStart + 1) (toStart + 1) fromStop f
    else pure ()

copyFromArray :
    (from : ArrayData a) ->
    (to : ArrayData a) ->
    (idxFrom : Int) ->
    (idxTo : Int) ->
    (lenFrom : Int) ->
    IO ()
copyFromArray from to idxFrom idxTo lenFrom =
    copyFromArrayBy from to idxFrom idxTo lenFrom id

copyFromList : ArrayData a -> List a -> Int -> IO ()
copyFromList arr [] idx = pure ()
copyFromList arr (x :: xs) idx = do
    fromPrim $ prim__arraySet arr idx x
    copyFromList arr xs (idx + 1)

export
data Array : Type -> Type where
    MkArray : (len : Int) -> (arr : ArrayData a) -> Array a

%name Array arr

export
empty : Array a
empty = MkArray 0 $ unsafeInlinePerformIO $ unsafeNewArray 0

export
singleton : a -> Array a
singleton x = unsafeInlinePerformIO $ do
    arr <- fromPrim $ prim__newArray 1 x
    pure $ MkArray 1 arr

export
fromList : (xs : List a) -> Array a
fromList [] = empty
fromList (x :: xs) = unsafeInlinePerformIO $ do
    let len = 1 + cast (length xs)
    arr <- fromPrim $ prim__newArray len x
    fromPrim $ prim__arraySet arr 0 x
    copyFromList arr xs 1
    pure $ MkArray len arr

toListOnto : Array a -> List a -> List a
toListOnto (MkArray 0 _) acc = acc
toListOnto xs@(MkArray len arr) acc =
    let last = unsafeInlinePerformIO $ fromPrim $ prim__arrayGet arr (len - 1)
     in case len of
        1 => last :: acc
        _ => toListOnto (assert_smaller xs $ MkArray (len - 1) arr) (last :: acc)

export %inline
length : Array a -> Int
length (MkArray len x) = len

%inline
unsafeIndex : Array a -> Int -> a
unsafeIndex (MkArray _ arr) idx = unsafeInlinePerformIO $ fromPrim $ prim__arrayGet arr idx

export
index : Array a -> Int -> Maybe a
index arr idx =
    if 0 <= idx && idx < length arr
        then Just $ unsafeIndex arr idx
        else Nothing

export
update : Array a -> List (Int, a) -> Array a
update arr [] = arr
update (MkArray len arr) xs = unsafeInlinePerformIO $ do
    arr' <- unsafeNewArray len
    copyFromArray arr arr' 0 0 len
    updateFromList arr' xs len
    pure $ MkArray len arr'
  where
    updateFromList :
        (arr : ArrayData a) ->
        (upds : List (Int, a)) ->
        (len : Int) ->
        IO ()
    updateFromList arr [] len = pure ()
    updateFromList arr ((idx, val) :: xs) len = do
        when (idx < len) $ fromPrim $ prim__arraySet arr idx val
        updateFromList arr xs len

export
insert : (idx : Int) -> (val : a) -> Array a -> Array a
insert idx val arr@(MkArray len orig) = if idx <= len
    then unsafeInlinePerformIO $ do
        new <- unsafeNewArray (len + 1)
        copyFromArray orig new 0 0 idx
        fromPrim $ prim__arraySet new idx val
        copyFromArray orig new idx (idx + 1) len
        pure $ MkArray (len + 1) new
    else arr

export
delete : (idx : Int) -> Array a -> Array a
delete idx arr@(MkArray len orig) =
    if idx >= len
        then arr
    else if len <= 1
        then empty
    else unsafeInlinePerformIO $ do
            new <- unsafeNewArray (len - 1)
            -- orig: 0 .. idx, new: 0 .. idx
            copyFromArray orig new 0 0 idx
            -- orig: idx + 1 .. len, new: idx .. len - 1
            copyFromArray orig new (idx + 1) idx len
            pure $ MkArray (len - 1) new

export
findIndex : (a -> Bool) -> Array a -> List Int
findIndex f arr = findIndexOnto 0 []
  where
    findIndexOnto : Int -> List Int -> List Int
    findIndexOnto idx acc = if idx < length arr
        then findIndexOnto (assert_smaller idx $ idx + 1)
            (if f (unsafeIndex arr idx)
                then idx :: acc
                else acc)
        else acc

export
append : (val : a) -> Array a -> Array a
append val arr = insert (length arr) val arr

export
Functor Array where
    map f (MkArray len arr) = MkArray len $
        unsafeInlinePerformIO $ do
            arr' <- unsafeNewArray len
            copyFromArrayBy arr arr' 0 0 len f
            pure arr'

foldrImpl :
    {0 elem : _} ->
    (f : elem -> acc -> acc) ->
    acc ->
    Int ->
    Array elem ->
    acc
foldrImpl f z i arr = if i < 0
    then z
    else
        let elem = unsafeIndex arr i
         in foldrImpl f (f elem z) (assert_smaller i $ i - 1) arr

foldlImpl :
    {0 elem : _} ->
    (f : acc -> elem -> acc) ->
    acc ->
    (index : Int) ->
    (length : Int) ->
    Array elem ->
    acc
foldlImpl f z i len arr = if i >= len
    then z
    else
        let elem = unsafeIndex arr i
         in foldlImpl f z (assert_smaller i $ i + 1) len arr

export
Foldable Array where
    foldr f z arr = foldrImpl f z (length arr - 1) arr

    foldl f z arr = foldlImpl f z 0 (length arr) arr

    null arr = length arr == 0
    toList arr = toListOnto arr []
    foldMap f arr = foldr (\elem, acc => f elem <+> acc) neutral arr

export
Show a => Show (Array a) where
    show = show . toList

parameters (pred : a -> b -> Bool)
    allFrom : Int -> Array a -> Array b -> Bool
    allFrom idx arr1 arr2 = if length arr1 <= idx || length arr2 <= idx
        then True
        else
            let x = index arr1 idx
                y = index arr2 idx
             in fromMaybe False [| pred x y |]
                && allFrom (assert_smaller idx $ idx + 1) arr1 arr2

    export
    all : Array a -> Array b -> Bool
    all = allFrom 0

export
Eq a => Eq (Array a) where
    x == y = length x == length y && all (==) x y
