helper : Unit -> Int
helper () = 2

first : Unit -> Int
first () = helper(()) + 100

second : Unit -> Int
second () = helper(()) + 100

from_definition : Unit -> Int
from_definition () = 1

main : Unit -> Int
main () = first(()) + second(()) + from_definition(())
