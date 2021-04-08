import Data.HashSet

s0 : HashSet Int
s0 = empty

s1 : HashSet Int
s1 = insert 10 $ insert 20 s0

main : IO ()
main = do
    printLn $ member 10 s0
    printLn $ member 10 s1
    printLn $ member 11 s1