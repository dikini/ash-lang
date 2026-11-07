private_increment : Int -> Int
private_increment value = value + 1
pub syntax increment $value:expr => {
    private_increment $value
}
