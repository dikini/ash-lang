import @builtin.compiler.syntax as Syntax

effect Pulse {
    ping : Unit -> Unit
}

next : Int -> (Int, Syntax.ExpressionFragment)
next state = handle {
    let _ = perform Pulse.ping ()
    (state + 1, syntax { 42 })
} with Pulse {
    ping ignored => resume ()
}

pub syntax declaration: (capture_step) $( $name:ident ),+ => {
    $(
        pub $name : Unit -> Int
        $name () = $number
    )+
} with {
    $number from 0 step next
}
