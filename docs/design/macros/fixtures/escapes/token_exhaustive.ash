import @builtin.compiler.syntax as Syntax

classify : Syntax.TokenKind -> Int
classify kind = match kind {
    Syntax.Wildcard => 42
    Syntax.IntegerLiteral => 42
    Syntax.StringLiteral => 42
    Syntax.True => 42
    Syntax.False => 42
    Syntax.Fn => 42
    Syntax.Let => 42
    Syntax.Rec => 42
    Syntax.And => 42
    Syntax.Type => 42
    Syntax.Newtype => 42
    Syntax.Effect => 42
    Syntax.Match => 42
    Syntax.Perform => 42
    Syntax.Handle => 42
    Syntax.With => 42
    Syntax.Resume => 42
    Syntax.Resource => 42
    Syntax.Region => 42
    Syntax.Using => 42
    Syntax.Hook => 42
    Syntax.Register => 42
    Syntax.Cleanup => 42
    Syntax.Discard => 42
    Syntax.Retain => 42
    Syntax.Import => 42
    Syntax.As => 42
    Syntax.Pub => 42
    Syntax.Opaque => 42
    Syntax.Interface => 42
    Syntax.Impl => 42
    Syntax.Where => 42
    Syntax.IntType => 42
    Syntax.BytesType => 42
    Syntax.StringType => 42
    Syntax.BoolType => 42
    Syntax.UnitType => 42
    Syntax.At => 42
    Syntax.Dot => 42
    Syntax.Colon => 42
    Syntax.Equal => 42
    Syntax.EqualEqual => 42
    Syntax.Plus => 42
    Syntax.Star => 42
    Syntax.Arrow => 42
    Syntax.FatArrow => 42
    Syntax.Pipe => 42
    Syntax.Bang => 42
    Syntax.Comma => 42
    Syntax.Less => 42
    Syntax.Greater => 42
    Syntax.LineEnd => 42
}

main : Unit -> Int
main () = classify(Syntax.Plus)
