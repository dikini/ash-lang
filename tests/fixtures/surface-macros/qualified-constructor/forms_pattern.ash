import actual as Helper

pub syntax unpack $value:expr => {
    match $value {
        Helper.Boxed(inner) => inner + 1
    }
}
