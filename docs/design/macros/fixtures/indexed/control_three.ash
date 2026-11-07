import api (Indexed, index)

type Color = Red
    | Blue
    | Green

impl Indexed<Color> {
    index Red = 1
    index Blue = 1
    index Green = 1
}

main : Unit -> Int
main () = index(Red) + index(Blue) + index(Green) + 39
