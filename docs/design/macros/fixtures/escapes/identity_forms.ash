import @builtin.compiler.syntax as Syntax

pub syntax identity $value:expr => using expand_identity
pub syntax token_kinds $value:expr => using verify_tokens

expand_identity : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_identity input = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.ExpressionCapture(value)) => Syntax.Expanded(Syntax.expression_syntax(value))
    _ => reject(input)
}

verify_tokens : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
verify_tokens input = match Syntax.make_token(Syntax.SyntaxKeyword, "syntax") {
    Syntax.MadeToken(keyword) => match Syntax.token_kind(keyword) {
        Syntax.SyntaxKeyword => verify_dollar(input)
        _ => reject(input)
    }
    _ => reject(input)
}

verify_dollar : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
verify_dollar input = match Syntax.make_token(Syntax.Dollar, "$") {
    Syntax.MadeToken(dollar) => match Syntax.token_kind(dollar) {
        Syntax.Dollar => verify_invalid(input)
        _ => reject(input)
    }
    _ => reject(input)
}

verify_invalid : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
verify_invalid input = match Syntax.make_token(Syntax.SyntaxKeyword, "syntaxes") {
    Syntax.InvalidToken => match Syntax.make_token(Syntax.Dollar, "$$") {
        Syntax.InvalidToken => expand_identity(input)
        _ => reject(input)
    }
    _ => reject(input)
}

reject : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
reject input = Syntax.Rejected(Syntax.MacroDiagnostic("unexpected token result", Syntax.invocation_origin(input), Syntax.NoOrigins))
