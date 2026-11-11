pub syntax declaration: (emit) $name:ident method $method:ident => {
    pub interface $name<F : Type -> Type> {
        $method : F<Int> -> Int
    }
}
