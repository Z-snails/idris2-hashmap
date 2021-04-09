
import Data.HashMap


main : IO ()
main = go max_n empty
  where
    max_n : Int
    max_n = 10

    go : Int -> HashMap String Int -> IO ()
    go 0 hm = putStrLn "finished"
    go n hm = do
        printLn n
        str <- getLine
        putStrLn str
        let hm' = insert str n hm
        go (n - 1) hm'
