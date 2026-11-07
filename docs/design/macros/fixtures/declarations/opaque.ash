import opaque_generated (Secret, build, SecretSum, build_sum)

main : Unit -> Int
main () = {
    let _ = build(42)
    let _ = build_sum(42)
    42
}
