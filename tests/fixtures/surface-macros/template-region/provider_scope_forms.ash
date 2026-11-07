pub syntax invalid $body:expr => {
    region<R> owner = owner {
        $body
    }
}
