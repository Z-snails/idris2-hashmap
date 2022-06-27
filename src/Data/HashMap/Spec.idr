module Data.HashMap.Spec

import Hedgehog
import Data.Vect
import Data.HashMap
import Data.Hashable

%default total

record BadHash where
    constructor MkBadHash
    inner : Int

Hashable BadHash where
    hash x = cast $ x.inner `div` 100
    hashWithSalt _ x = hash x

Show BadHash where
    show x = show x.inner

Eq BadHash where
    x == y = x.inner == y.inner

data Act : key -> val -> Type where
    Insert : key -> val -> Act key val
    Delete : key -> Act key val

runAct : Hashable key => Eq key => HashMap key val -> Act key val -> HashMap key val
runAct hm (Insert key val) = insert key val hm
runAct hm (Delete key) = delete key hm

genAct : Gen key -> Gen val -> Gen (Act key val)
genAct kg vg = frequency
    [ (10, [| Insert kg vg |])
    , (3, [| Delete kg |])
    ]

genHashmap : Hashable key => Eq key => Gen key -> Gen val -> Gen (HashMap key val)
genHashmap gk gv = foldl runAct empty <$> list (exponential 20 1000) (genAct gk gv)

export
spec : Group
spec = MkGroup "Data.HashMap" [
    ("lookup/insert,delete", withTests 1000 $ property $ do
        hm <- forAll $ genHashmap (int (linear 0 1000)) (int (linear 0 1000))
        key <- forAll $ int (linear 0 1000)
        val <- forAll $ int (linear 0 1000)
        unless (lookup key (insert key val hm) == Just val) $ failWith Nothing (show @{Raw} hm)
        lookup key (insert key val hm) === Just val
        lookup key (delete key hm) === Nothing
    ),
    ("collisions: lookup/insert,delete", withTests 1000 $ property $ do
        hm <- forAll $ genHashmap
            (MkBadHash <$> int (linear 0 1000))
            (MkBadHash <$> int (linear 0 1000))
        key <- forAll $ MkBadHash <$> int (linear 0 1000)
        val <- forAll $ MkBadHash <$> int (linear 0 1000)
        unless (lookup key (insert key val hm) == Just val) $ failWith Nothing (show @{Raw} hm)
        lookup key (insert key val hm) === Just val
        lookup key (delete key hm) === Nothing
    )
]
