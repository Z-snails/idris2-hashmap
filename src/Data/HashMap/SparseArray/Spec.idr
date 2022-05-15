module Data.HashMap.SparseArray.Spec

import Data.HashMap.SparseArray as SA
import Hedgehog

genSparseArray : Gen a -> Gen (SparseArray a)
genSparseArray gen =
    SA.fromList
        <$> list
            (linear 0 64)
            ((,) <$> int (linear 0 63) <*> gen)

export
spec : Group
spec = MkGroup "Data.HashMap.SparseArray" [
    ("fromList . toList == id", withTests 1000 $ property $ do
        sarr <- forAll $ genSparseArray $ int (linear 0 1000)
        sarr === SA.fromList (SA.toList sarr)
    ),
    ("hasEntry,findIndex", withTests 1000 $ property $ do
        idx <- forAll $ int (linear 0 60)
        let sarr = SA.fromList [(idx, 0)]
        hasEntry idx sarr === True
        findIndex idx sarr.bitmap === 0

        let sarr = SA.fromList [(idx, 0), (idx + 1, 1)]
        hasEntry (idx + 1) sarr === True
        findIndex (idx + 1) sarr.bitmap === 1
        findIndex idx sarr.bitmap === 0
    ),
    ("set/index", withTests 1000 $ property $ do
        sarr <- forAll $ genSparseArray $ int (linear 0 1000)
        idx <- forAll $ int (linear 0 63)
        val <- forAll $ int (linear 0 1000)
        set idx val sarr === SA.fromList ((idx, val) :: SA.toList sarr)
        -- index idx (set idx val sarr) === Just val
    )
]
