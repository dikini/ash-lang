import api (Marker)

pub syntax derive: (missing_derive_free) $target:ident => {
    impl Marker<$target> {
        mark _ = unknown_helper(())
    }
}
