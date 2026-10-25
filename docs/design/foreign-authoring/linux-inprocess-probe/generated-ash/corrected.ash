import @builtin.foreign as Foreign
foreign library C {
    profile "x86_64-unknown-linux-gnu"
    repr CInt = signed(32)
    const Negative : CInt = -7
    symbol Abs : Int -> Foreign.Call<Int> {
        name "abs"
        abi (CInt) -> CInt
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
}
main : Unit -> Foreign.Call<Int> ! {Abs}
main () = perform Abs.call Negative
