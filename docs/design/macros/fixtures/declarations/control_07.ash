pub id : Int -> Int
id value = value
pub fn same(value: Int) -> Int {
    value
}

main : Unit -> Int
main () = id(same(42))
