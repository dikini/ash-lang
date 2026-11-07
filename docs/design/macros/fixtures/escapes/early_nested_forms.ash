pub syntax declaration: (nested_quote) $name:ident => {
    pub $name : Unit -> Int
    $name () = ${
        let base = syntax { 10 }
        syntax {
            ${
                let increment = syntax { 1 }
                syntax { $base + $increment }
            } * 2
        }
    }
}
