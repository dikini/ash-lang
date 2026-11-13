pub syntax declaration: (make_value) $name:ident using $helper:ident => {
    $helper : Unit -> Int
    $helper () = 21
    pub $name : Unit -> Int
    $name () = $helper(()) + $helper(())
}
