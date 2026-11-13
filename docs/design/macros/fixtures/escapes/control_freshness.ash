answer : Unit -> Int
answer () = {
    let left = {
        let temporary = 10
        temporary
    }
    let right = {
        let temporary = 10
        temporary
    }
    left + right
}

main : Unit -> Int
main () = answer(())
