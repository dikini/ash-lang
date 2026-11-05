pub type Capsule = Boxed(Int)
pub opaque type Secret = Hidden(Int)

pub unwrap : Capsule -> Int
unwrap value = match value {
    Boxed(inner) => inner + 1
}

pub evaluate : (Capsule -> Int) -> Int
evaluate function = function (Boxed(41))
