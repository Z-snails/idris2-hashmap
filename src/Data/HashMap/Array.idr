module Data.HashMap.Array

import Data.Fin
import Data.IOArray.Prims
import Data.List

-- eventually this will be its own package

%default total

%spec f
copyFromArrayBy :
    (from : ArrayData a) ->
    (to : ArrayData b) ->
    (idx : Int) ->
    (len : Int) ->
    (f : a -> b) ->
    IO ()
copyFromArrayBy from to idx len f = if idx < len
    then do
        val <- fromPrim $ prim__arrayGet from idx
        fromPrim $ prim__arraySet to idx (f val)
        copyFromArrayBy from to (assert_smaller idx $ idx + 1) len f
    else pure ()

copyFromArray :
    (from : ArrayData a) ->
    (to : ArrayData a) ->
    (idx : Int) ->
    (len : Int) ->
    IO ()
copyFromArray from to idx len = copyFromArrayBy from to idx len id

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
toList : Array a -> List a
toList arr = toListOnto arr []

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
    copyFromArray arr arr' 1 len
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
insert idx val (MkArray len arr) = if idx <= len
    then unsafePerformIO $ do
        init <- fromPrim $ prim__arrayGet arr 0
        arr' <- fromPrim $ prim__newArray (len + 1) init
        copyFromArray arr arr' 0 idx
        fromPrim $ prim__arraySet arr' idx val
        copyFromArray arr arr' (idx + 1) (len + 1)
        pure $ MkArray (len + 1) arr'
    else MkArray len arr

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
            copyFromArrayBy arr arr' 1 len f
            pure arr'

export
Show a => Show (Array a) where
    show arr = "[" ++ fastConcat (intersperse "," (toList (map show arr))) ++ "]" 
