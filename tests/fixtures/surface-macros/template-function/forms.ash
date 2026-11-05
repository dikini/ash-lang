pub syntax closure $value:expr => {
    fn(temp) {
        temp + $value
    }
}

pub syntax bind_function $name:ident in $body:expr => {
    fn($name) {
        $body
    }
}
