import helpers as H

pub syntax call $member:ident with $value:expr => {
    H.$member($value)
}

pub syntax through $path:ident with $value:expr => {
    $path.increment($value)
}
