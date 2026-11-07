pub syntax declaration: (wrong_code_type) => {
    pub answer : Unit -> Int
    answer () = ${
        let value : Int = true
        syntax { 0 }
    }
}
