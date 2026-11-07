import api (Indexed, index)

type Color = Red
    | Blue

impl Indexed<Color> {
    index Red = 1
    index Blue = 1
}

main : Unit -> Int
main () = index(Red) + index(Blue) + 40
