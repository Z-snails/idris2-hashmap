module Test

import Data.HashMap.Array
import Data.HashMap.SparseArray
import Data.HashMap.Internal as HM
import Decidable.Equality
import Data.String
import Control.Function

withDecEq : DecEq key => ((x, y : key) -> Maybe (x === y))
withDecEq x y = case decEq x y of
    Yes prf => Just prf
    No _ => Nothing

record BadHash a where
    constructor MkBadHash
    hash : Bits64
    val : a

badHashInjective : {x, y : Bits64} -> (MkBadHash x v0 === MkBadHash y v1) -> x === y
badHashInjective Refl = Refl

{h : _} -> Injective (MkBadHash h) where
    injective Refl = Refl

Eq a => Eq (BadHash a) where
    x == y = x.val == y.val

Hashable (BadHash a) where
    hash = (.hash)
    hashWithSalt _ = (.hash)

Show a => Show (BadHash a) where
    show bh = show bh.val

export
main : IO ()
main = do
    let sarr = SparseArray.fromList [(3, "!"), (1, "hello"), (2, "world"), (7, "!!!")]
    printLn sarr.bitmap

    for_ {t = List} [1, 2, 3, 7] $ \idx => putStrLn "\{show idx}: \{show $ findIndex idx sarr}"

    printLn $ length sarr
    printLn sarr

    let hamt = the (HAMT (BadHash Int) (const String)) $ HM.singleton (MkBadHash 0b1000001 0) "hello"
    let hamt = the (HAMT (BadHash Int) (const String)) $ HM.insert (==) (MkBadHash 0b1000001 1) "world" hamt
    let hamt = the (HAMT (BadHash Int) (const String)) $ HM.insert (==) (MkBadHash 0b1000000 2) "world" hamt

    putStrLn $ unlines $ printTree "" hamt
