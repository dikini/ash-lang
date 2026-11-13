import api (Marker, mark)
pub syntax declaration: (make) $target:ident => {
    impl Marker<$target> {
        mark _ = true
    }
}
