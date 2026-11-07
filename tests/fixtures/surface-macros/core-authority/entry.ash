import forms (syntax increment)
ordinary : Int -> Int
ordinary value = value + 10
use_generated : Int -> Int
use_generated value = increment value
main : Unit -> Int
main () = (use_generated 30) + ordinary 1
