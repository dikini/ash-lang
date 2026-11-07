effect Ask {
    ask : Int -> Int
}

pub syntax listen $op:ident for $body:expr => {
    handle (perform Ask.ask $body) with Ask {
        $op value => resume value
    }
}
