import forms (syntax send_owner)

main : Unit -> Int
main () = send_owner NotEffect with 42
