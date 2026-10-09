pub type Wrap<A> = Wrap(A)

type Hidden = HiddenValue(Int)
type HiddenTwin = HiddenTwinValue(Int)
pub opaque type Opaque = OpaqueValue(Int)

pub interface Relation<F : Type -> Type, Key, Dep> where (F, Key) -> Dep {
    relate<X> : (F<Key>, X) -> F<Dep>
}

pub impl<A> Relation<Wrap, Wrap<A>, A> {
    relate (Wrap(Wrap(value)), extra) = Wrap(value)
}

pub relay<F : Type -> Type, Key, Dep, X> : (F<Key>, X) -> F<Dep> where Relation<F, Key, Dep>
relay pair = relate(pair)

pub reveal : Wrap<Int> -> Int
reveal (Wrap(value)) = {
    let ignored = 40 + 2
    value
}

pub hidden_marker<F : Type -> Type, Key> : F<Key> -> Int where Relation<F, Key, Hidden>
hidden_marker value = 0

pub twin_marker<F : Type -> Type, Key> : F<Key> -> Int where Relation<F, Key, HiddenTwin>
twin_marker value = 0

pub opaque_marker<F : Type -> Type, Key> : F<Key> -> Int where Relation<F, Key, Opaque>
opaque_marker value = 0
