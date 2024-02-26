module Main

import ParkBench
import Data.HashMap

act : Int32 -> HashMap Int32 Int32 -> HashMap Int32 Int32
act 0 hm = insert 0 0 hm
act x hm = act (x - 1) (insert x x hm)

main : IO ()
main = do
    for_ [0, 1, 10, 100, 1000, 10000, 100000] $ \n => do
        let hm = act n
        bench "insert: size = \{show n}" (act 1000) empty >>= printLn
