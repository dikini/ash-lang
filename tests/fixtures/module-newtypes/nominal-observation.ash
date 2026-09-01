newtype UserId = UserId(Int)

round_trip : UserId -> UserId
round_trip (UserId value) = UserId(value)

main : Unit -> UserId
main () = round_trip(UserId(42))
