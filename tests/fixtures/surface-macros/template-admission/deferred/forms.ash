import inner (syntax bomb)

pub syntax outer $value:expr => {
    bomb $value
}
