import helpers as Helpers
import other_dsl (syntax bump, syntax choose)

pub opaque type Secret = Hidden(Int)

private_increment : Int -> Int
private_increment value = Helpers.increment(value)

pub syntax bind $name:ident = $initial:expr when $condition:expr in $body:expr => {
    let temp = 1
    let $name = $initial
    match Hidden($body + temp) {
        Hidden(value) => choose $condition then private_increment (bump value) else 0
    }
}
