import @builtin.compiler.syntax as Syntax

pub syntax unused $value:expr => using transformer

transformer : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
transformer input = {
    let origin = Syntax.invocation_origin(input)
    Syntax.Rejected(Syntax.MacroDiagnostic("unused transformer ran", origin, Syntax.NoOrigins))
}

main : Unit -> Int
main () = 42
