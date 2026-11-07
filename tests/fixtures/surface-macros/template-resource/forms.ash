import @builtin.cell as Cell

pub syntax hold $initial:expr => {
    resource cell<R> c = $initial {
        Cell.read c
    }
}

pub syntax with_body $initial:expr in $body:expr => {
    resource cell<R> c = $initial {
        (Cell.read c) + $body
    }
}

pub syntax typed $initial:expr => {
    resource cell<R> c = $initial {
        let reader : Cell.Handle<R> = c
        Cell.read reader
    }
}

pub syntax escape $ignored:expr => {
    resource cell<R> c = 0 {
        c
    }
}
