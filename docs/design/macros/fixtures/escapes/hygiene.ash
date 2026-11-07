import forms (syntax hygienic, syntax definition_helper)

helper : Unit -> Int
helper () = 2

hygienic first from (helper(()))
hygienic second from (helper(()))
definition_helper from_definition

main : Unit -> Int
main () = first(()) + second(()) + from_definition(())
