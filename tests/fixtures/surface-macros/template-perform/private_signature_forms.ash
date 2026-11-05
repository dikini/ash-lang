type Secret = Hidden(Int)
effect Ask {
    ask : Secret -> Int
}
pub syntax local_ask $value:expr => {
    handle (perform Ask.ask (Hidden($value))) with Ask {
        ask (Hidden(value)) => resume value
    }
}
