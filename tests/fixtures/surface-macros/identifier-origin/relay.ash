import inner (syntax observe)
pub syntax forward $name:ident = $value:expr => {
    observe $name = $value
}
