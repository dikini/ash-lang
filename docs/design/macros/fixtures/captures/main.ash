import forms (syntax expression_value, syntax predicate, syntax pass_declaration, syntax zeroes, syntax ones)

expression_value forty_two from 40 + 2
predicate selected when true
pass_declaration {
    passed : Unit -> Int
    passed () = 42
}
zeroes
ones first, second

main : Unit -> Int
main () = forty_two(()) + selected(true) + passed(()) + first(()) + second(())
