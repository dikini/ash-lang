pub syntax bind $name:ident in $body:expr => {
    newtype $name = $name(Int)
    $body
}
