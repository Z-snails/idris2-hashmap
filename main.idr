import Data.HashMap

m0 : HashMap Int String
m0 = empty

m1 : HashMap Int String
m1 = fromList [(10, "Foo"), (2, "Bah")]

m2 : HashMap Int String
m2 = insert 22 "Baz" m1

m3 : HashMap Int String
m3 = insert 22 "Baz2" m2

main : IO ()
main = do
    printLn m1
    printLn $ lookup 2 m1
    printLn $ lookup 2 m0
    printLn m2
    printLn m3