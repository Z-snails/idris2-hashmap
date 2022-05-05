module Data.Array16

||| Array of 16 elements.
||| This is designed for speed not as a user facing interface.
public export
record Array16 a where
    constructor MkA16
    i_0 : a
    i_1 : a
    i_2 : a
    i_3 : a
    i_4 : a
    i_5 : a
    i_6 : a
    i_7 : a
    i_8 : a
    i_9 : a
    i_a : a
    i_b : a
    i_c : a
    i_d : a
    i_e : a
    i_f : a

export
Functor Array16 where
    map f =
        { i_0 $= f
        , i_1 $= f
        , i_2 $= f
        , i_3 $= f
        , i_4 $= f
        , i_5 $= f
        , i_6 $= f
        , i_7 $= f
        , i_8 $= f
        , i_9 $= f
        , i_a $= f
        , i_b $= f
        , i_c $= f
        , i_d $= f
        , i_e $= f
        , i_f $= f
        }

export
Foldable Array16 where
    foldl f z ar = let f' = flip f in
        f' ar.i_f $
        f' ar.i_e $
        f' ar.i_d $
        f' ar.i_c $
        f' ar.i_b $
        f' ar.i_a $
        f' ar.i_9 $
        f' ar.i_8 $
        f' ar.i_7 $
        f' ar.i_6 $
        f' ar.i_5 $
        f' ar.i_4 $
        f' ar.i_3 $
        f' ar.i_2 $
        f' ar.i_1 $
        f' ar.i_0 z

    foldr f z ar =
        f ar.i_0 $
        f ar.i_1 $
        f ar.i_2 $
        f ar.i_3 $
        f ar.i_4 $
        f ar.i_5 $
        f ar.i_6 $
        f ar.i_7 $
        f ar.i_8 $
        f ar.i_9 $
        f ar.i_a $
        f ar.i_b $
        f ar.i_c $
        f ar.i_d $
        f ar.i_e $
        f ar.i_f z

||| Get the `idx`th value.
||| If out of bounds return the last value.
export
index : (idx : Bits64) -> Array16 a -> a
index i ar = case i of
    0x0 => ar.i_0
    0x1 => ar.i_1
    0x2 => ar.i_2
    0x3 => ar.i_3
    0x4 => ar.i_4
    0x5 => ar.i_5
    0x6 => ar.i_6
    0x7 => ar.i_7
    0x8 => ar.i_8
    0x9 => ar.i_9
    0xa => ar.i_a
    0xb => ar.i_b
    0xc => ar.i_c
    0xd => ar.i_d
    0xe => ar.i_e
    _   => ar.i_f

||| Write a new value to the `idx`th value.
||| If out of bounds leave unmodified.
export
write : (idx : Bits64) -> a -> Array16 a -> Array16 a
write idx a ar = case idx of
    0x0 => {i_0 := a} ar
    0x1 => {i_1 := a} ar
    0x2 => {i_2 := a} ar
    0x3 => {i_3 := a} ar
    0x4 => {i_4 := a} ar
    0x5 => {i_5 := a} ar
    0x6 => {i_6 := a} ar
    0x7 => {i_7 := a} ar
    0x8 => {i_8 := a} ar
    0x9 => {i_9 := a} ar
    0xa => {i_a := a} ar
    0xb => {i_b := a} ar
    0xc => {i_c := a} ar
    0xd => {i_d := a} ar
    0xe => {i_e := a} ar
    0xf => {i_f := a} ar
    _ => ar

||| Update the `idx`th value.
||| If out of bounds leave unmodified.
export
update : (idx : Bits64) -> (a -> a) -> Array16 a -> Array16 a
update idx f ar = case idx of
    0x0 => {i_0 $= f} ar
    0x1 => {i_1 $= f} ar
    0x2 => {i_2 $= f} ar
    0x3 => {i_3 $= f} ar
    0x4 => {i_4 $= f} ar
    0x5 => {i_5 $= f} ar
    0x6 => {i_6 $= f} ar
    0x7 => {i_7 $= f} ar
    0x8 => {i_8 $= f} ar
    0x9 => {i_9 $= f} ar
    0xa => {i_a $= f} ar
    0xb => {i_b $= f} ar
    0xc => {i_c $= f} ar
    0xd => {i_d $= f} ar
    0xe => {i_e $= f} ar
    0xf => {i_f $= f} ar
    _ => ar

||| Initial an Array with a default value.
export
new : a -> Array16 a
new a = MkA16
    { i_0 = a
    , i_1 = a
    , i_2 = a
    , i_3 = a
    , i_4 = a
    , i_5 = a
    , i_6 = a
    , i_7 = a
    , i_8 = a
    , i_9 = a
    , i_a = a
    , i_b = a
    , i_c = a
    , i_d = a
    , i_e = a
    , i_f = a
    }
