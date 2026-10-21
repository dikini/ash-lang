import @builtin.foreign as Foreign
foreign checked library Native {
    profile "x86_64-unknown-linux-gnu"
    repr I32 = signed(32)
    assumption Callee "the admitted native contract holds"
    symbol Abs<H, T> : Int -> Foreign.CheckedCall<Int> {
        name "abs"
        abi (I32) -> I32
        host H
        assumes { Callee }
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
}
type Held = Held(Int)
type Spare = Spare(Int)
closed<T> : (T, Int) -> Foreign.CheckedCall<Int>
closed (unused, value) = foreign host Local {
    perform Abs<Local, T>.call value
}
select : Int -> (Unit -> Foreign.CheckedCall<Int>)
select value = {
    let held = Held value
    fn(ignored) {
        match held {
            Held(captured) => closed (held, captured)
        }
    }
}
pub interface Read<A> {
    read : A -> (Unit -> Foreign.CheckedCall<Int>)
}
pub impl Read<Int> {
    read value = select value
}
