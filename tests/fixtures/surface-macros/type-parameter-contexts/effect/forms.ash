pub syntax declaration: (emit) $E:ident operation $op:ident => {
    pub effect $E<A> {
        $op : Unit -> A
    }
}
