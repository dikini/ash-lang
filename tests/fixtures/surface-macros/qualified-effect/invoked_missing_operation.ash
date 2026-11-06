import missing_operation (syntax unused)

effect Ask {
    missing : Int -> Int
}

main : Unit -> Int
main () = unused 42
