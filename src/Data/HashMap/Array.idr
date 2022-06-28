module Data.HashMap.Array

import Data.Fin
import Data.IOArray.Prims
import Data.List

-- eventually this may be its own package

%default total

-- index differently
%spec f
copyFromArrayBy :
    (from : ArrayData a) ->
    (to : ArrayData b) ->
    (idxFrom : Int) ->
    (idxTo : Int) ->
    (lenFrom : Int) ->
    (f : a -> b) ->
    IO ()
copyFromArrayBy from to idxFrom idxTo lenFrom f = if idxFrom < lenFrom
    then do
        val <- fromPrim $ prim__arrayGet from idxFrom
        fromPrim $ prim__arraySet to idxTo (f val)
        copyFromArrayBy from to (assert_smaller idxFrom $ idxFrom + 1) (idxTo + 1) lenFrom f
    else pure ()

copyFromArray :
    (from : ArrayData a) ->
    (to : ArrayData a) ->
    (idxFrom : Int) ->
    (idxTo : Int) ->
    (lenFrom : Int) ->
    IO ()
copyFromArray from to idxFrom idxTo lenFrom = copyFromArrayBy from to idxFrom idxTo lenFrom id

copyFromList : ArrayData a -> List a -> Int -> IO ()
copyFromList arr [] idx = pure ()
copyFromList arr (x :: xs) idx = do
    fromPrim $ prim__arraySet arr idx x
    copyFromList arr xs (idx + 1)

export
data Array : Type -> Type where
    Empty : Array a
    -- Safety: len >= 1
    MkArray : (len : Int) -> (arr : ArrayData a) -> Array a

%name Array arr

export
empty : Array a
empty = Empty

export
fromList : (xs : List a) -> Array a
fromList [] = Empty
fromList (x :: xs) = unsafePerformIO $ do
    let len = 1 + cast (length xs)
    arr <- fromPrim $ prim__newArray len x
    fromPrim $ prim__arraySet arr 0 x
    copyFromList arr xs 1
    pure $ MkArray len arr

toListOnto : Array a -> List a -> List a
toListOnto Empty acc = acc
toListOnto xs@(MkArray len arr) acc =
    let last = unsafePerformIO $ fromPrim $ prim__arrayGet arr (len - 1)
     in case len of
        1 => last :: acc
        _ => toListOnto (assert_smaller xs $ MkArray (len - 1) arr) (last :: acc)

export
length : Array a -> Int
length Empty = 0
length (MkArray len x) = len

export
index : Array a -> Int -> Maybe a
index Empty idx = Nothing
index (MkArray len arr) idx =
    if idx < len
        then Just $ unsafePerformIO $ fromPrim $ prim__arrayGet arr idx
        else Nothing

export
update : Array a -> List (Int, a) -> Array a
update arr [] = arr
update Empty xs = Empty
update (MkArray len arr) xs@(_ :: _) = unsafePerformIO $ do
    init <- fromPrim $ prim__arrayGet arr 0 -- Safety: len >= 1
    arr' <- fromPrim $ prim__newArray len init
    fromPrim $ prim__arraySet arr 0 init
    copyFromArray arr arr' 1 1 len
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
insert 0 val Empty = fromList [val]
insert _ val Empty = Empty
insert idx val arr@(MkArray len orig) = if idx <= len
    then unsafePerformIO $ do
        init <- fromPrim $ prim__arrayGet orig 0
        new <- fromPrim $ prim__newArray (len + 1) init
        _ <- copyFromArray orig new 0 0 idx
        _ <- fromPrim $ prim__arraySet new idx val
        _ <- copyFromArray orig new idx (idx + 1) len
        pure $ MkArray (len + 1) new
    else arr

export
delete : (idx : Int) -> Array a -> Array a
delete idx Empty = Empty
delete idx arr@(MkArray len orig) = if idx < len
    then if len <= 1 then Empty else
        unsafePerformIO $ do
        init <- fromPrim $ prim__arrayGet orig 0
        new <- fromPrim $ prim__newArray (len - 1) init
        -- orig: 0 .. idx, new: 0 .. idx
        copyFromArray orig new 0 0 idx
        -- orig: idx + 1 .. len, new: idx .. len - 1
        copyFromArray orig new (idx + 1) idx len
        pure $ MkArray (len - 1) new
    else arr

export
findIndex : (a -> Bool) -> Array a -> List Int
findIndex f arr = findIndexOnto 0 []
  where
    findIndexOnto : Int -> List Int -> List Int
    findIndexOnto idx acc = if idx < length arr
        then findIndexOnto (assert_smaller idx $ idx + 1)
            (if maybe False f (index arr idx)
                then idx :: acc
                else acc)
        else acc

export
append : (val : a) -> Array a -> Array a
append val arr = insert (length arr) val arr

export
Functor Array where
    map f Empty = Empty
    map f (MkArray len arr) = MkArray len $
        unsafePerformIO $ do
            init <- fromPrim $ prim__arrayGet arr 0
            arr' <- fromPrim $ prim__newArray len (f init)
            fromPrim $ prim__arraySet arr' 0 (f init)
            copyFromArrayBy arr arr' 1 1 len f
            pure arr'

foldrImpl :
    {0 elem : _} ->
    (f : elem -> acc -> acc) ->
    acc ->
    Int ->
    ArrayData elem ->
    acc
foldrImpl f z 0 arr = z
foldrImpl f z i arr =
    let elem = unsafePerformIO $ fromPrim $ prim__arrayGet arr i
     in foldrImpl f (f elem z) (assert_smaller i $ i - 1) arr

foldlImpl :
    {0 elem : _} ->
    (f : acc -> elem -> acc) ->
    acc ->
    (index : Int) ->
    (length : Int) ->
    ArrayData elem ->
    acc
foldlImpl f z i len arr =
    if i >= len
        then z
        else
            let elem = unsafePerformIO $ fromPrim $ prim__arrayGet arr i
             in foldlImpl f z (assert_smaller i $ i + 1) len arr

export
Foldable Array where
    foldr f z Empty = z
    foldr f z (MkArray len arr) = foldrImpl f z (len - 1) arr

    foldl f z Empty = z
    foldl f z (MkArray len arr) = foldlImpl f z 0 len arr

    null arr = length (arr) == 0
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

    ||| Check if 
    export
    all : Array a -> Array b -> Bool
    all = allFrom 0

export
Eq a => Eq (Array a) where
    Empty == Empty = True
    x@(MkArray l1 _) == y@(MkArray l2 _) =
        l1 == l2
        && all (==) x y
    _ == _ = False
