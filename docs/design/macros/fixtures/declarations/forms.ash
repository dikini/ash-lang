import @builtin.foreign as F

pub syntax declaration: (make_type) $T:ident constructor $C:ident => {
    pub type $T = $C(Int)
}

pub syntax declaration: (make_newtype) $T:ident constructor $C:ident => {
    pub newtype $T = $C(Int)
}

pub syntax declaration: (make_interface) $T:ident method $m:ident => {
    pub interface $T<A> {
        $m : A -> Bool
    }
}

pub syntax declaration: (make_impl) $I:ident for $T:ident method $m:ident => {
    impl $I<$T> {
        $m _ = true
    }
}

pub syntax declaration: (make_effect) $E:ident operation $op:ident => {
    pub effect $E {
        $op : Unit -> Int
    }
}

pub syntax declaration: (make_foreign) $L:ident symbol $S:ident => {
    pub foreign library $L {
        profile "x86_64-unknown-linux-gnu"
        symbol $S : Unit -> F.Address { name "fixture_make" }
    }
}

pub syntax declaration: (make_identity) $name:ident for $T:type => {
    pub $name : $T -> $T
    $name value = value
}

pub syntax declaration: (make_inline) $name:ident for $T:type => {
    pub fn $name(value: $T) -> $T {
        value
    }
}
