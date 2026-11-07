import api (Indexed, index)

type Color = Red

impl Indexed<Color> {
    index Red = 1
}

main : Unit -> Int
main () = index(Red) + 41
