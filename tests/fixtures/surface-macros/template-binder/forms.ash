pub syntax bind $name:ident then $body:expr => {
    let $name = 41
    $body + 1
}
