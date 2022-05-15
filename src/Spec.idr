module Spec

import Data.HashMap.Array.Spec
import Data.HashMap.SparseArray.Spec
import Data.HashMap.Internal.Spec
import Data.HashMap.Spec
import Hedgehog

main : IO ()
main = traverse_ checkGroup
    [ Array.Spec.spec
    , SparseArray.Spec.spec
    , Internal.Spec.spec
    , HashMap.Spec.spec
    ]
