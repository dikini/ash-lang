import @builtin.foreign as Foreign
foreign checked library Native {
    profile "x86_64-unknown-linux-gnu"
    repr I32 = signed(32)
    assumption Callee "the admitted native contract holds"
    symbol Abs<H> : Int -> Foreign.CheckedCall<Int> {
        name "abs"
        abi (I32) -> I32
        host H
        assumes { Callee }
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
}
type Leaf = Leaf(Int)
type Donor = Donor(Int)
type Spare = Spare(Int)
pub type Envelope = Envelope(Leaf)
pub type Witness = Witness(Donor)
closed : Int -> Foreign.CheckedCall<Int>
closed value = foreign host Local {
    perform Abs<Local>.call value
}
pub make : Int -> Envelope
make value = Envelope (Leaf value)
pub inspect : Envelope -> Foreign.CheckedCall<Int>
inspect envelope = match envelope {
    Envelope(Leaf(value)) => closed value
}
