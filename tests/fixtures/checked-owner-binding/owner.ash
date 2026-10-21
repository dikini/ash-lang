import @builtin.foreign as Foreign
foreign checked library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
    repr Address = opaque
    assumption Callee "the admitted native owner contract holds"
    owner State<H, R> {
        representation Address
        owned R
        host H
        teardown Free
    }
    symbol Allocate<H, R> : Int -> Foreign.CheckedCall<Foreign.Output<Foreign.Nullable<State<H, R>>>> {
        name "malloc"
        abi (Size) -> pointer(Address)
        host H
        assumes { Callee }
        operand 0 from 0 scalar
        output result as owner(State<H, R>)
        outcome result nonnull { readable result }
        outcome otherwise { readable result }
    }
    symbol Free<H, R> : State<H, R> -> Foreign.CheckedCall<Foreign.Disposition<Unit>> {
        name "free"
        abi (pointer(Address)) -> void
        host H
        assumes { Callee }
        operand 0 from 0 current
        retained_dependents block
        outcome otherwise { consumed 0 }
    }
}
pub idle : Unit -> Int
idle () = 42
