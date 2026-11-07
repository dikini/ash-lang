import types (Boxed as Package, Number)

pub syntax accept $value:expr => {
    let result : Package<Package<Number>> = $value
    42
}
