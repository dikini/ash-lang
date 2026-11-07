pub syntax clean $body:expr => {
    cleanup fn(ignored) {
        ()
    } {
        $body
    }
}
