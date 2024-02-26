module Data.HashMap.Bits

import System.Info

export %inline
oneBits : Bits64
oneBits = 0xffff_ffff_ffff_ffff

infixl 5 .|.

export %inline
(.|.) : Bits64 -> Bits64 -> Bits64
(.|.) = prim__or_Bits64

infixl 7 .&.

export %inline
(.&.) : Bits64 -> Bits64 -> Bits64
(.&.) = prim__and_Bits64

export %inline
not : Bits64 -> Bits64
not = prim__xor_Bits64 oneBits

export %inline
shiftR : Bits64 -> Bits64 -> Bits64
shiftR = prim__shr_Bits64

export %inline
shiftL : Bits64 -> Bits64 -> Bits64
shiftL = prim__shl_Bits64

export %inline
bit : Bits32 -> Bits64
bit k = 1 `shiftL` cast k

export %inline
setBit : Bits64 -> Bits32 -> Bits64
setBit x k = bit k .|. x

export %inline
clearBit : Bits64 -> Bits32 -> Bits64
clearBit x k = not (bit k) .&. x

export %inline
testBit : Bits64 -> Bits32 -> Bool
testBit x k = (bit k .&. x) /= 0

export %inline
popCount : Bits64 -> Bits64
popCount x0 =
    -- see https://stackoverflow.com/questions/109023/how-to-count-the-number-of-set-bits-in-a-64-bit-Bits32eger
    let x1 = (x0 .&. 0x5555555555555555) +
             ((x0 `shiftR` 1) .&. 0x5555555555555555)
        x2 = (x1 .&. 0x3333333333333333)
             + ((x1 `shiftR` 2) .&. 0x3333333333333333)
        x3 = ((x2 + (x2 `shiftR` 4)) .&. 0x0F0F0F0F0F0F0F0F)
        x4 = (x3 * 0x0101010101010101) `shiftR` 56
     in x4

export
isScheme : Bool
isScheme = (codegen == "chez") || (codegen == "racket")

export %inline
unsafeIncr : Bits32 -> Bits32
unsafeIncr x = if isScheme
     then believe_me $ the Nat $ believe_me x + 1
     else x + 1

export %inline
unsafeCast : Cast a b => a -> b
unsafeCast x = if isScheme
    then believe_me x
    else cast x
