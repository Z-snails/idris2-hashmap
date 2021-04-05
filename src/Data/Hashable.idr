module Data.Hashable

import Data.String

||| Default salt to use with `hashWithSalt`
export
defaultSalt : Bits64
defaultSalt = 14695981039346656037

||| Interface for type that can be hashed.
|||
||| `hash` and `hashWithSalt` don't need to be 1-to-1, however for best performance
||| in hash based data structures it is best to produce the most
||| unique values.
|||
||| `hashWithSalt` should ideally produce different hashes with a
||| different salt when applied to two values that produce the
||| same hash from a given salt.
|||
||| Note: this is using Bits64 because it is better defined that Int
||| (See https://github.com/idris-lang/Idris2/issues/1048)
public export
interface Hashable a where
    hash : a -> Bits64
    hash = hashWithSalt defaultSalt

    hashWithSalt : Bits64 -> a -> Bits64

||| Default implementation of `hashWithSalt`
||| Note: only use this if `hash` is 1-to-1
export
defaultHashWithSalt : Hashable a => Bits64 -> a -> Bits64
defaultHashWithSalt salt a = combine salt (hash a)
  where
    combine : Bits64 -> Bits64 -> Bits64
    combine h1 h2 = (h1 * 16777619) `prim__xor_Bits64` h2

export
Hashable Int where
    hash = cast
    hashWithSalt = defaultHashWithSalt

export
Hashable Bits8 where
    hash = cast
    hashWithSalt = defaultHashWithSalt

export
Hashable Bits16 where
    hash = cast
    hashWithSalt = defaultHashWithSalt

export
Hashable Bits32 where
    hash = cast
    hashWithSalt = defaultHashWithSalt

export
Hashable Bits64 where
    hash = id
    hashWithSalt = defaultHashWithSalt

export
Hashable Char where
    -- Not neccessarily safe until we get properly specified Ints
    -- because a Char can be bigger than a 32 bit signed int. :/
    -- However this is probably not a problem because very few people
    -- have strings with lots of characters in that range.
    hash = cast . ord
    hashWithSalt = defaultHashWithSalt

export
Hashable a => Hashable b => Hashable (a, b) where
    hashWithSalt salt (a, b) = hashWithSalt (hashWithSalt salt a) b

export
Hashable a => Hashable (Maybe a) where
    hashWithSalt salt Nothing = salt
    hashWithSalt salt (Just a) = hashWithSalt salt a

export
Hashable a => Hashable (List a) where
    hashWithSalt salt [] = salt
    hashWithSalt salt (a :: as) = hashWithSalt (hashWithSalt salt as) a

export
Hashable String where
    hashWithSalt salt str = hashWithSalt salt (fastUnpack str)
