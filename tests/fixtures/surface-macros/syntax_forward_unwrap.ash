import syntax_unwrap_ops (syntax unwrap)

pub syntax forwarded $value:expr => {
    unwrap $value
}

pub syntax grouped_forward $value:expr => {
    unwrap ($value)
}
