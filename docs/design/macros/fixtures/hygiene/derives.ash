import api (Marker, mark)

pub syntax derive: (marker) $target:ident => {
    impl Marker<$target> {
        mark _ = true
    }
}
