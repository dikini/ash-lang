pub type Option<A> =
None
| Some(A)

pub interface Observe<F : Type -> Type> {
observe : F<Int> -> Int
}

pub impl Observe<Option> {
observe value = 40 + 2
}

pub relay<F : Type -> Type> : F<Int> -> F<Int>
relay value = value
