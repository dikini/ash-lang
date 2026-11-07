import @builtin.compiler.syntax as Syntax

pub syntax double_origin $value:expr => using expand_double
pub syntax deep_origin $value:expr => using expand_deep
pub syntax repeat_origin $value:expr => using expand_repeated

expand_double : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_double input = {
    let origin = Syntax.invocation_origin(input)
    double (input, origin, origin, 0)
}

double : (Syntax.Input, Syntax.Origin, Syntax.Origin, Int) -> Syntax.MacroResult ! {Syntax.Ops}
double (input, primary, origin, count) = match count == 18 {
    true => Syntax.Rejected(Syntax.MacroDiagnostic("unbounded doubling", primary, Syntax.NoOrigins))
    false => {
        let origins = Syntax.MoreOrigins(origin, Syntax.MoreOrigins(origin, Syntax.NoOrigins))
        match Syntax.combine_origins(input, origins) {
            Syntax.Combined(next) => double (input, primary, next, count + 1)
            _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing origin", primary, Syntax.NoOrigins))
        }
    }
}

expand_deep : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_deep input = {
    let origin = Syntax.invocation_origin(input)
    deep (input, origin, origin, 0)
}

deep : (Syntax.Input, Syntax.Origin, Syntax.Origin, Int) -> Syntax.MacroResult ! {Syntax.Ops}
deep (input, primary, origin, count) = match count == 130 {
    true => Syntax.Rejected(Syntax.MacroDiagnostic("unbounded depth", primary, Syntax.NoOrigins))
    false => {
        let origins = Syntax.MoreOrigins(origin, Syntax.NoOrigins)
        match Syntax.combine_origins(input, origins) {
            Syntax.Combined(next) => deep (input, primary, next, count + 1)
            _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing origin", primary, Syntax.NoOrigins))
        }
    }
}

expand_repeated : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_repeated input = {
    let origin = Syntax.invocation_origin(input)
    repeated (input, origin, origin, 0)
}

repeated : (Syntax.Input, Syntax.Origin, Syntax.Origin, Int) -> Syntax.MacroResult ! {Syntax.Ops}
repeated (input, primary, origin, count) = match count == 14 {
    true => {
        let causes = Syntax.MoreOrigins(origin, Syntax.MoreOrigins(origin, Syntax.NoOrigins))
        Syntax.Rejected(Syntax.MacroDiagnostic("too many causes", primary, causes))
    }
    false => {
        let origins = Syntax.MoreOrigins(origin, Syntax.MoreOrigins(origin, Syntax.NoOrigins))
        match Syntax.combine_origins(input, origins) {
            Syntax.Combined(next) => repeated (input, primary, next, count + 1)
            _ => Syntax.Rejected(Syntax.MacroDiagnostic("missing origin", primary, Syntax.NoOrigins))
        }
    }
}
