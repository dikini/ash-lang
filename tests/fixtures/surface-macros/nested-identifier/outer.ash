import inner (syntax bind)
pub syntax outer $value:expr => {
    bind local = $value in local
}
