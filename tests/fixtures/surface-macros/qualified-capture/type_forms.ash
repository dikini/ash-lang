import types as Owner

pub syntax pack $path:ident then $value:expr => {
    let item : $path.Token = $value
    item
}

pub syntax owner_type $member:ident then $value:expr => {
    let item : Owner.$member = $value
    item
}

pub syntax create $member:ident with $value:expr => {
    Owner.$member($value)
}

pub syntax make $path:ident with $value:expr => {
    $path.Token($value)
}
