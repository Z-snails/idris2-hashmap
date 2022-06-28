||| Utilities for inspecting the structure of a `HashMap`
module Data.HashMap.Internal.Debug

import Data.HashMap
import Data.HashMap.Internal
import Data.HashMap.SparseArray
import Data.List
import Data.String

export
printTree :
    Show key =>
    String ->
    HAMT key val ->
    List String
printTree indent (Leaf hash k val) = ["\{indent}(\{show k}#\{show hash})"]
printTree indent (Node arr) =
    "\{indent}n" ::
    (SparseArray.toList (assert_total $ map (printTree (indent ++ "  ")) arr)
        >>= \(idx, ls) =>
            "\{indent} \{show idx}:" :: ls)
printTree indent (Collision hash arr) =
    [ "\{indent}c#\{show hash}:"
    , (indent ++ " "
    ++ concat (intersperse ", " $ toList $ map (\(key ** _) => show key) arr))
    ]

export
[Raw] Show key => Show val => Show (HashMap key val) where
    show Empty = "Empty"
    show (Trie hamt) = unlines $ "Trie $" :: printTree " " hamt
