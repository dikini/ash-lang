import api as Owner

pub syntax unpack $name:ident in $value:expr => {
    match $value {
        Owner.$name(inner) => inner
    }
}

pub syntax unpack_caller $path:ident in $value:expr => {
    match $value {
        $path.Boxed(inner) => inner
    }
}

pub syntax unpack_name $name:ident in $value:expr => {
    match $value {
        $name(inner) => inner
    }
}
