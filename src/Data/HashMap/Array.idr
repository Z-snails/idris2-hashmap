module Data.HashMap.Array

import Data.Fin
import Data.IOArray.Prims
import Data.List
import Data.HashMap.Bits

%default total

%inline
prim__newArray : Bits32 -> a -> PrimIO (ArrayData a)
prim__newArray len x = Prims.prim__newArray (unsafeCast len) x

%inline
prim__arrayGet : ArrayData a -> Bits32 -> PrimIO a
prim__arrayGet arr i = Prims.prim__arrayGet arr (unsafeCast i)

%inline
prim__arraySet : ArrayData a -> Bits32 -> a -> PrimIO ()
prim__arraySet arr i x = Prims.prim__arraySet arr (unsafeCast i) x

%inline
unsafeNewArray : Bits32 -> IO (ArrayData a)
unsafeNewArray len = fromPrim $ prim__newArray len (believe_me ())

%inline
unsafeInlinePerformIO : IO a -> a
unsafeInlinePerformIO act =
    let MkIORes res %MkWorld = toPrim act %MkWorld
     in res

-- Copy from[fromStart..fromStop) to to[toStart..)
-- %spec f
copyFromArrayBy :
    (f : a -> b) ->
    (from : ArrayData a) ->
    (to : ArrayData b) ->
    (fromStart : Bits32) ->
    (toStart : Bits32) ->
    (fromStop : Bits32) ->
    IO ()
copyFromArrayBy f from to fromStart toStart fromStop = case fromStart `prim__lt_Bits32` fromStop of
    0 => pure ()
    _ => do
        val <- fromPrim $ prim__arrayGet from fromStart
        fromPrim $ prim__arraySet to toStart (f val)
        copyFromArrayBy f from to (assert_smaller fromStart $ unsafeIncr fromStart) (unsafeIncr toStart) fromStop

-- Hand specialised version of copyFromArrayBy id
copyFromArray :
    (from : ArrayData a) ->
    (to : ArrayData a) ->
    (fromStart : Bits32) ->
    (toStart : Bits32) ->
    (fromStop : Bits32) ->
    IO ()
copyFromArray from to fromStart toStart fromStop = case fromStart `prim__lt_Bits32` fromStop of
    0 => pure ()
    _ => do
        val <- fromPrim $ prim__arrayGet from fromStart
        fromPrim $ prim__arraySet to toStart val
        copyFromArray from to (assert_smaller fromStart $ unsafeIncr fromStart) (unsafeIncr toStart) fromStop


copyFromList : ArrayData a -> List a -> Bits32 -> IO ()
copyFromList arr [] idx = pure ()
copyFromList arr (x :: xs) idx = do
    fromPrim $ prim__arraySet arr idx x
    copyFromList arr xs (idx + 1)

export
data Array : Type -> Type where
    MkArray : (len : Bits32) -> (arr : ArrayData a) -> Array a

%name Array arr

export
empty : Array a
empty = MkArray 0 $ unsafeInlinePerformIO $ unsafeNewArray 0

export
singleton : a -> Array a
singleton x = unsafeInlinePerformIO $ do
    arr <- fromPrim $ Prims.prim__newArray 1 x
    pure $ MkArray 1 arr

export
fromList : (xs : List a) -> Array a
fromList [] = empty
fromList (x :: xs) = unsafeInlinePerformIO $ do
    let len = 1 + cast (length xs)
    arr <- fromPrim $ prim__newArray len x
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
length : Array a -> Bits32
length (MkArray len x) = len

%inline
unsafeIndex : Array a -> Bits32 -> a
unsafeIndex (MkArray _ arr) idx = unsafeInlinePerformIO $ fromPrim $ prim__arrayGet arr idx

export
index : Array a -> Bits32 -> Maybe a
index arr idx =
    if 0 <= idx && idx < length arr
        then Just $ unsafeIndex arr idx
        else Nothing

export
update : Array a -> List (Bits32, a) -> Array a
update arr [] = arr
update (MkArray len arr) xs = unsafeInlinePerformIO $ do
    arr' <- unsafeNewArray len
    copyFromArray arr arr' 0 0 len
    updateFromList arr' xs len
    pure $ MkArray len arr'
  where
    updateFromList :
        (arr : ArrayData a) ->
        (upds : List (Bits32, a)) ->
        (len : Bits32) ->
        IO ()
    updateFromList arr [] len = pure ()
    updateFromList arr ((idx, val) :: xs) len = do
        when (idx < len) $ fromPrim $ prim__arraySet arr idx val
        updateFromList arr xs len

export
insert : (idx : Bits32) -> (val : a) -> Array a -> Array a
insert idx val arr@(MkArray len orig) = if idx <= len
    then unsafeInlinePerformIO $ do
        new <- unsafeNewArray (len + 1)
        copyFromArray orig new 0 0 idx
        fromPrim $ prim__arraySet new idx val
        copyFromArray orig new idx (idx + 1) len
        pure $ MkArray (len + 1) new
    else arr

export
delete : (idx : Bits32) -> Array a -> Array a
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
findIndex : (a -> Bool) -> Array a -> Maybe Bits32
findIndex f arr = go 0 (length arr)
  where
    go : Bits32 -> Bits32 -> Maybe Bits32
    go i len =
        if i >= len
            then Nothing
        else if f (unsafeIndex arr i)
            then Just i
        else go (assert_smaller i $ i + 1) len

export
findWithIndex : (a -> Bool) -> Array a -> Maybe (Bits32, a)
findWithIndex f arr = go 0 (length arr)
  where
    go : Bits32 -> Bits32 -> Maybe (Bits32, a)
    go i len =
        if i >= len
            then Nothing
        else
            let elem = unsafeIndex arr i
            in if f elem then Just (i, elem) else go (assert_smaller i $ i + 1) len

export
append : (val : a) -> Array a -> Array a
append val arr = insert (length arr) val arr

export
Functor Array where
    map f (MkArray len arr) = MkArray len $
        unsafeInlinePerformIO $ do
            arr' <- unsafeNewArray len
            copyFromArrayBy f arr arr' 0 0 len
            pure arr'

foldrImpl :
    {0 elem : _} ->
    (f : elem -> acc -> acc) ->
    acc -> Bits32 -> Array elem ->
    acc
foldrImpl f z i arr = if i == 0
    then f (unsafeIndex arr i) z
    else
        let elem = unsafeIndex arr i
         in foldrImpl f (f elem z) (assert_smaller i $ i - 1) arr

foldlImpl :
    {0 elem : _} ->
    (f : acc -> elem -> acc) ->
    acc ->
    (index : Bits32) ->
    (length : Bits32) ->
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
    allFrom : Bits32 -> Array a -> Array b -> Bool
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
