pub syntax proceed $value:expr => {
    resume $value
}

pub syntax stop $unused:expr => {
    discard
}

pub syntax keep $unused:expr => {
    retain
}
