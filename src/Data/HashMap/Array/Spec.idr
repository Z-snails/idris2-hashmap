module Data.HashMap.Array.Spec

import Data.Nat
import Hedgehog

import Data.HashMap.Array

listGen : Gen (List Int)
listGen = list (exponential 0 1000) (int $ linear 0 1000)

arrayGen : Gen (Array Int)
arrayGen = Array.fromList <$> listGen

export
spec : Group
spec = MkGroup "Data.HashMap.Array" [
    ("toList . fromList", withTests 1000 $ property $ do
        xs <- forAll listGen
        xs === Array.toList (Array.fromList xs)
    ),
    ("length empty = 0", withTests 10 $ property $ do
        empty {a=Int} === Array.fromList []
    ),
    ("index correct", withTests 1000 $ property $ do
        xs <- forAll listGen
        idx <- forAll $ nat $ exponential 0 1000
        getAt idx xs === index (Array.fromList xs) (cast idx)
    ),
    ("insert/index,length", withTests 1000 $ property $ do
        arr <- forAll arrayGen
        idx <- forAll $ int (linear 0 (length arr))
        val <- forAll $ int (linear 0 1000)
        let arr' = insert idx val arr
        index arr' idx === Just val
        length arr' === length arr + 1
    ),
    ("fromList", withTests 1000 $ property $ do
        list <- forAll listGen
        let len = length list
            arr = Array.fromList list
        length arr === cast len
        index arr (cast $ len `minus` 1) === getAt (len `minus` 1) list
        index arr 0 === getAt 0 list
    )
]
