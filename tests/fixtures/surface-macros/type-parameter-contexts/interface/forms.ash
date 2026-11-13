pub syntax declaration: (emit) $name:ident method $method:ident => {
    pub interface $name<A> {
        $method : A -> Bool
    }
}
