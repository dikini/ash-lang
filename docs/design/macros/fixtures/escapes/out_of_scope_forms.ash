pub syntax declaration: (out_of_scope) $( $name:ident ),* => {
    pub answer : Unit -> Int
    answer () = ${
        let ignored = $name
        syntax { 0 }
    }
}
