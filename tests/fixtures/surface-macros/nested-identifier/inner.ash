pub syntax bind $name:ident = $initial:expr in $body:expr => {
    let $name = $initial
    $body
}
