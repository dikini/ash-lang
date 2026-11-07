import api as Owner

pub syntax measure $value:expr => {
    Owner.read($value)
}
