import macros (syntax twice)

pub type Padding = Padding

pub syntax wrap $value:expr => {
    twice $value
}
