pub effect Ask {
    ask : Int -> Int
}

pub effect Generic<T> {
    ask : T -> T
}

effect Secret {
    ask : Int -> Int
}

pub type NotEffect = NotEffect(Int)
