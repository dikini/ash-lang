next_number : Int -> Int
next_number state = state

pub syntax declaration: (invalid_step) $( $name:ident ),+ => {
    $(
        pub $name : Unit -> Int
        $name () = $number
    )+
} with {
    $number from 0 step next_number
}
