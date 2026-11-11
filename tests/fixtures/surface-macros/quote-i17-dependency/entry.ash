import forms (syntax i17_0, syntax i17_1, syntax i17_2, syntax i17_3, syntax i17_4, syntax i17_5)

i17_0 v0
i17_1 v1
i17_2 v2
i17_3 v3
i17_4 v4
i17_5 v5

main : Unit -> Int
main () = match (v0(()) == 100, v1(()) == 1, v2(()) == 2, v3(()) == 3, v4(()) == 4, v5(()) == 5) {
    (true, true, true, true, true, true) => 42
    _ => 0
}
