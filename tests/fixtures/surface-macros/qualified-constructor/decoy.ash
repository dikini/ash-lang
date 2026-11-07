pub type Capsule = Boxed(Int)

pub unwrap : Capsule -> Int
unwrap value = match value {
    Boxed(inner) => inner + 100
}
