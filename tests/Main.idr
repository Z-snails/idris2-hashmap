module Main

import Data.Array16Spec
import Data.HashMapSpec

main : IO ()
main = do
    ignore $ specArray16
    ignore $ specHashMap