import carrier (make, step, read)

main : Unit -> Int
main () = read(step(make(41)))
