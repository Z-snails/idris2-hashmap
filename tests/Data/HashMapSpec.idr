module Data.HashMapSpec

import Data.HashMap
import Data.Vect
import Data.Vect
import Hedgehog

%hide Prelude.Range

data Op : Type -> Type -> Type where
    Insert : k -> v -> Op k v
    Delete : k -> Op k v

runOp : Op k v -> HashMap k v -> HashMap k v
runOp (Insert k v) = insert k v
runOp (Delete k) = delete k

runOps' : List (Op k v) -> HashMap k v -> HashMap k v
runOps' [] m = m
runOps' (op :: ops) m = runOps' ops (runOp op m)

runOps : Hashable k => Eq k => List (Op k v) -> HashMap k v
runOps ops = runOps' ops empty

genOp : Gen k -> Gen v -> Gen (Op k v)
genOp k v = choice [ [| Insert k v |], [| Delete k |] ]

genHashMap : Hashable k => Eq k => Range Nat -> Gen (Op k v) -> Gen (HashMap k v)
genHashMap size op = runOps <$> list size op

int1000 : Gen Int
int1000 = int $ linear 0 1000

genHMDefault : Gen (HashMap Int Int)
genHMDefault = genHashMap (linear 25 100) (genOp int1000 int1000)

insertLookupProp : Property
insertLookupProp = property $ do
    hm <- forAll genHMDefault
    k <- forAll int1000
    v <- forAll int1000
    Just v === lookup k (insert k v hm)

deleteLookupProp : Property
deleteLookupProp = property $ do
    hm <- forAll genHMDefault
    k <- forAll int1000
    v <- forAll int1000
    Nothing === lookup k (delete k (insert k v hm))

str25 : Gen String
str25 = string (linear 20 30) ascii

strInsertLookupProp : Property
strInsertLookupProp = property $ do
    hm <- forAll $ genHashMap (linear 100 150) (genOp str25 int1000)
    k <- forAll str25
    v <- forAll int1000
    Just v === lookup k (insert k v hm)

export
specHashMap : IO Bool
specHashMap =
    checkGroup $
        MkGroup "HashMap"
            [ ("lookup/insert", insertLookupProp)
            , ("lookup/delete", deleteLookupProp)
            , ("String lookup/insert", strInsertLookupProp)
            ]
