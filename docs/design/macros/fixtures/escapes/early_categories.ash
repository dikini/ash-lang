import early_categories_forms (syntax make_expr, syntax local_capture, syntax make_ident, syntax make_type, syntax make_pattern, syntax pass_declaration)

make_expr plus from 5
local_capture local from 5
make_ident named
make_type identity for Int
make_pattern choose when true
pass_declaration {
    pub declared : Unit -> Int
    declared () = 42
}

main : Unit -> Int
main () = plus(()) + local(()) + named(()) + identity(3) + choose(true) + declared(())
