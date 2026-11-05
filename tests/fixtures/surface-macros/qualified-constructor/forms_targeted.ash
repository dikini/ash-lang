import actual (Boxed as Wrap, unwrap)

pub syntax targeted $value:expr => {
    unwrap (Wrap($value))
}

pub syntax targeted_pattern $value:expr => {
    match $value {
        Wrap(inner) => inner + 1
    }
}
