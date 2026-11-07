private_increment : Int -> Int
private_increment value = value + 1
pub syntax add_one $value:expr => {
    private_increment $value
}
