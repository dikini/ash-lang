import facade (Boxed as Wrap, unwrap)

pub syntax through_facade $value:expr => {
    unwrap (Wrap($value))
}
