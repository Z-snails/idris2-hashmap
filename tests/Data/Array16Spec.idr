module Data.Array16Spec

import Data.Array16
import Data.List
import Data.String
import Hedgehog

export
Show a => Show (Array16 a) where
    showPrec prec arr = showCon prec "MkA16" $ fastConcat $ intersperse " "
        $ foldr (\elem, acc => showPrec App elem :: acc) [] arr

export
array16Gen : Gen a -> Gen (Array16 a)
array16Gen gen = [| MkA16 gen gen gen gen gen gen gen gen gen gen gen gen gen gen gen gen |]

propFoldable : Property
propFoldable = property $ do
    arr <- forAll $ array16Gen $ int $ linear (-100) 100
    null arr === False




export
specArray16 : IO Bool
specArray16 =
    checkGroup $ MkGroup "Array16"
        [ ("Foldable", propFoldable)
        ]
