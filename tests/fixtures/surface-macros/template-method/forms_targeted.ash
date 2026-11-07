import api (read as owner_read)

pub syntax measure $value:expr => {
    owner_read($value)
}
