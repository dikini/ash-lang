import facade (UserId)

read : UserId -> Int
read (UserId value) = value

main : Unit -> Int
main () = read(UserId(42))
