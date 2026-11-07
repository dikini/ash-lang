pub syntax declaration: (make_nominal) $name:ident constructor $constructor:ident empty $empty:ident => {
    pub type $name<A> = $constructor(A)
        | $empty
}
