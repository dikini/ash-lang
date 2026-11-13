pub syntax declaration: (emit) $I:ident for $T:ident method $m:ident constructor $C:ident => {
    impl<A> $I<$T<A>> where $I<A> {
        $m ($C(left), $C(right)) = $m(left, right)
    }
}
