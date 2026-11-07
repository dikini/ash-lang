pub first : Bool -> Int
first value = match value {
    true => second(false)
    false => 42
}

pub second : Bool -> Int
second value = first(value)

main : Unit -> Int
main () = first(true)
