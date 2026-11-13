import @builtin.compiler.syntax as Syntax
import @builtin.string as Text

pub syntax declaration: (inspect) { $( row ( $outer:ident $( item $inner:ident ),* ) );* } => using inspect
pub syntax declaration: (emit_one) $( $item:declaration ),+ => using emit_one

inspect : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
inspect input = match (Syntax.capture(input, 0), Syntax.capture(input, 1), Syntax.capture(input, 2)) {
    (Syntax.Captured(Syntax.RepeatedCapture(outer)), Syntax.Captured(Syntax.RepeatedCapture(inner)), Syntax.MissingCapture) => match (outer_ok(outer), inner_ok(inner)) {
        (true, true) => Syntax.Expanded(Syntax.Syntax(Syntax.NoNodes))
        _ => reject(input)
    }
    _ => reject(input)
}

outer_ok : Syntax.Captures -> Bool ! {Syntax.Ops}
outer_ok (Syntax.NoCaptures) = true
outer_ok (Syntax.MoreCaptures(Syntax.IdentifierCapture(a, _), Syntax.MoreCaptures(Syntax.IdentifierCapture(b, _), Syntax.MoreCaptures(Syntax.IdentifierCapture(c, _), Syntax.NoCaptures)))) = match (Text.equal(Syntax.identifier_spelling(a), "alpha"), Text.equal(Syntax.identifier_spelling(b), "beta"), Text.equal(Syntax.identifier_spelling(c), "gamma")) {
    (true, true, true) => true
    _ => false
}
outer_ok (_) = false

inner_ok : Syntax.Captures -> Bool ! {Syntax.Ops}
inner_ok (Syntax.NoCaptures) = true
inner_ok (Syntax.MoreCaptures(Syntax.RepeatedCapture(Syntax.MoreCaptures(Syntax.IdentifierCapture(a, _), Syntax.MoreCaptures(Syntax.IdentifierCapture(b, _), Syntax.NoCaptures))), Syntax.MoreCaptures(Syntax.RepeatedCapture(Syntax.NoCaptures), Syntax.MoreCaptures(Syntax.RepeatedCapture(Syntax.MoreCaptures(Syntax.IdentifierCapture(c, _), Syntax.NoCaptures)), Syntax.NoCaptures)))) = match (Text.equal(Syntax.identifier_spelling(a), "a"), Text.equal(Syntax.identifier_spelling(b), "b"), Text.equal(Syntax.identifier_spelling(c), "c")) {
    (true, true, true) => true
    _ => false
}
inner_ok (_) = false

emit_one : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
emit_one input = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.RepeatedCapture(Syntax.MoreCaptures(Syntax.DeclarationCapture(item), Syntax.NoCaptures))) => {
        let origin = Syntax.invocation_origin(input)
        Syntax.Expanded(Syntax.Syntax(Syntax.MoreNodes(Syntax.DeclarationNode(item, origin), Syntax.NoNodes)))
    }
    _ => reject(input)
}

reject : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
reject input = Syntax.Rejected(Syntax.MacroDiagnostic("unexpected repeated capture", Syntax.invocation_origin(input), Syntax.NoOrigins))
