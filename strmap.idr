import Data.HashMap


m0 : HashMap String Int
m0 = empty

m1 : HashMap String Int
m1 = insert "Bah" 10 $ insert "Foo" 11 m0

main : IO ()
main = do
    printLn $ lookup "Bah" m0
    printLn $ lookup "Bah" m1
    printLn $ lookup "Foo" m1
    printLn $ lookup "Fa" m1
    str <- getLine
    let m2 = insert str 12 m1
    str <- getLine
    printLn $ lookup str m2
