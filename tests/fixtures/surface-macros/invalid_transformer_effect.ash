import @builtin.compiler.syntax as Syntax

effect Other {
    ping : Unit -> Unit
}

pub syntax invalid $value:expr => using wrong

wrong : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops, Other}
wrong input = {
    let marker = perform Other.ping ()
    let origin = Syntax.invocation_origin(input)
    Syntax.Rejected(Syntax.MacroDiagnostic("unused", origin, Syntax.NoOrigins))
}

main : Unit -> Int
main () = 42
