import @builtin.foreign as Foreign
foreign checked library Native {
    profile "x86_64-unknown-linux-gnu"
    repr I32 = signed(32)
    assumption Callee "the admitted callee follows its declared native contract"
    symbol Abs<Before : EffectRow, H, T, After : EffectRow> : Int -> Foreign.CheckedCall<Int> {
        name "abs"
        abi (I32) -> I32
        host H
        assumes { Callee }
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
    assumption OtherCallee "the other admitted contract holds"
    symbol Other<Before : EffectRow, H, T, After : EffectRow> : Int -> Foreign.CheckedCall<Int> {
        name "abs"
        abi (I32) -> I32
        host H
        assumes { OtherCallee }
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
}
effect First {
    first : Unit -> Unit
}
effect Last {
    last : Unit -> Unit
}
pub opaque type Box<A> = Box(A)
pub wrap<A> : A -> Box<A>
wrap value = Box value
pub interface Read<A> {
    read<X> : (A, X) -> Foreign.CheckedCall<Int>
}
pub impl Read<(Unit -> Unit ! {First}, Unit -> Unit ! {Last})> {
    read (value, ignored) = foreign host Local {
        match true {
            true => perform Abs<{First}, Local, (Unit -> Unit ! {First}, Unit -> Unit ! {Last}), {Last}>.call 1
            false => perform Other<{Last}, Local, (Unit -> Unit ! {Last}, Unit -> Unit ! {First}), {First}>.call 2
        }
    }
}
pub impl<A> Read<Box<A>> where Read<A> {
    read (Box value, ignored) = read (value, ignored)
}
pub invoke<A> : A -> Foreign.CheckedCall<Int> where Read<A>
invoke value = read (value, true)
pub before : Unit -> Unit ! {First}
before () = perform First.first ()
pub after : Unit -> Unit ! {Last}
after () = perform Last.last ()
