import Data.HashMap
import Data.HashMap.Internal.Debug
%default total

{- Create test cases with upt to 5 elements -}
Test1, Test2, Test3, Test4, Test5 : HashMap Int32 Nat
Test1 = insert (-27266) 0 empty
Test2 = insert (-35458) 1 Test1
-- Test3 = insert "baz"  2 Test2
-- Test4 = insert "quux" 3 Test3
-- Test5 = insert "frob" 4 Test4

{- check a single property -}
check : Show a => String -> a -> IO ()
check name prop = do
  putStrLn (name ++ ": " ++ show prop)

{- check all the properties for the given test case -}
test : String -> HashMap Int32 Nat -> IO ()
test name testCase = do
  check (name ++ " Has -27266"   )      (lookup (-27266) testCase == Just 0)
  check (name ++ " keys")               (keys testCase)
  check (name ++ " has -27266 in keys") (elem (-27266) (keys testCase))
  putStrLn $ show @{Raw} testCase
  putStrLn ""

main : IO ()
main = do
  let hm = the (HashMap Int32 Int32) empty
  let hm = insert 0 0 hm
  let hm = insert 1 1 hm
  putStrLn $ show @{Raw} hm
  printLn $ keys hm

  -- test "Test1" Test1
  -- test "Test2" Test2
  -- test "Test3" Test3
  -- test "Test4" Test4
  -- test "Test5" Test5
