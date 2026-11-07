pub syntax declaration: (make_value) $name:ident => {
    pub $name : Unit -> Int
    $name () = 42
}

make_value number

main : Unit -> Int
main () = number(())
