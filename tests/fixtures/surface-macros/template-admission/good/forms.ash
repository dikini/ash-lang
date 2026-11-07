pub syntax lookup $name:ident then $ignored:expr => {
    $name
}

pub syntax through $value:expr => {
    helper $value
}

helper : Int -> Int
helper value = value + 1

pub syntax reuse $name:ident then $ignored:expr => {
    let $name = 41
    $name
}
