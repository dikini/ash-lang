type HiddenFirst = HiddenFirst
type HiddenSecond = HiddenSecond

pub first : Unit -> Int
first () = match HiddenFirst {
    HiddenFirst => 42
}

pub second : Unit -> Int
second () = match HiddenSecond {
    HiddenSecond => 42
}

type Hidden = Hidden

main : Unit -> Int
main () = first(()) + second(())
