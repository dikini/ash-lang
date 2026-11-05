type Payload = Hidden(Int)
newtype Secret = Secret(Payload)
effect Ask {
    ask : Secret -> Int
}
pub syntax local_ask $value:expr => {
    handle (perform Ask.ask (Secret(Hidden($value)))) with Ask {
        ask (Secret(Hidden(value))) => resume value
    }
}
