type Inner = Inside(Int)
pub opaque type Outer = Outside(Inner)

pub syntax reveal $value:expr => {
    match Outside(Inside($value)) {
        Outside(Inside(found)) => found
    }
}
