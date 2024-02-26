module Data.HashMap.SparseArray.Spec

import Data.HashMap.SparseArray as SA
import Hedgehog

index, value : Gen Bits32
index = bits32 (linear 0 63)
value = bits32 (linear 0 1000)

genSparseArray : Gen a -> Gen (SparseArray a)
genSparseArray gen =
    SA.fromList
        <$> list
            (linear 0 64)
            [| (index, gen) |]

export
spec : Group
spec = MkGroup "Data.HashMap.SparseArray" [
    ("fromList . toList == id", withTests 1000 $ property $ do
        sarr <- forAll $ genSparseArray value
        sarr === SA.fromList (SA.toList sarr)
    ),
    ("hasEntry,findIndex", withTests 1000 $ property $ do
        idx <- forAll $ bits32 $ linear 0 62
        let sarr = SA.fromList [(idx, 0)]
        hasEntry idx sarr === True
        findIndex idx sarr.bitmap === 0

        let sarr = SA.fromList [(idx, 0), (idx + 1, 1)]
        hasEntry (idx + 1) sarr === True
        findIndex (idx + 1) sarr.bitmap === 1
        findIndex idx sarr.bitmap === 0
    ),
    ("set/index", withTests 1000 $ property $ do
        sarr <- forAll $ genSparseArray value
        idx <- forAll index
        val <- forAll value
        set idx val sarr === SA.fromList ((idx, val) :: SA.toList sarr)
        index idx (set idx val sarr) === Just val
    ),
    ("singleton", withTests 1000 $ property $ do
        idx <- forAll index
        val <- forAll value
        let sarr = singleton (idx, val)
        index idx sarr === Just val
    ),
    ("doubleton", withTests 1000 $ property $ do
        idx0 <- forAll index
        idx1 <- forAll index
        val0 <- forAll value
        val1 <- forAll value
        let sarr = doubleton (idx0, val0) (idx1, val1)
        if idx0 == idx1
            then do
                index idx0 sarr === Just val1
                index idx1 sarr === Just val1
            else do
                index idx0 sarr === Just val0
                index idx1 sarr === Just val1
    )
]
