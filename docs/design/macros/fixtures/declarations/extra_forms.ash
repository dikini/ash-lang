pub syntax declaration: (make_generic_type) $name:ident first $first:ident second $second:ident => {
    pub type $name<A> = $first(A)
        | $second
}

pub syntax declaration: (make_generic_box) $name:ident constructor $constructor:ident => {
    pub newtype $name<A> = $constructor(A)
}

pub syntax declaration: (make_opaque_box) $name:ident constructor $constructor:ident => {
    pub opaque newtype $name = $constructor(Int)
}

pub syntax declaration: (make_opaque_type) $name:ident constructor $constructor:ident => {
    pub opaque type $name = $constructor(Int)
}

pub syntax declaration: (make_methods) $name:ident first $first:ident second $second:ident => {
    pub interface $name<A> {
        $first : A -> Bool
        $second : A -> Bool
    }
}

pub syntax declaration: (make_operations) $name:ident first $first:ident second $second:ident => {
    pub effect $name {
        $first : Unit -> Int
        $second : Unit -> Int
    }
}

pub syntax declaration: (make_relation) $name:ident method $method:ident => {
    pub interface $name<A, B> where A -> B {
        $method : A -> B
    }
}

pub syntax declaration: (make_higher) $name:ident method $method:ident => {
    pub interface $name<F : Type -> Type> {
        $method : F<Int> -> Int
    }
}

pub syntax declaration: (box_implementation) $interface:ident for $box:ident method $method:ident constructor $constructor:ident => {
    impl<A> $interface<$box<A>> where $interface<A> {
        $method ($constructor(left), $constructor(right)) = $method(left, right)
    }
}
