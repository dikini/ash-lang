main : Unit -> Int
main () = {
    let temp = 10
    let result = {
        let item = 5
        let introduced_temp = 1
        let payload = item + temp + introduced_temp
        let bumped = payload + 1
        bumped + 1
    }
    result + result + 6
}
