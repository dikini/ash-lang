import api (Marker, mark, Tagged, tag)

pub syntax derive: (marker) $target:ident => {
    impl Marker<$target> {
        mark _ = true
    }
}

pub syntax derive: (tagged) $target:ident => {
    impl Tagged<$target> {
        tag _ = 42
    }
}

pub syntax derive: (public_marker) $target:ident => {
    pub impl Marker<$target> {
        mark _ = true
    }
}
