import @builtin.compiler.syntax as Syntax
import inner (syntax observe, syntax observe_resolve, syntax observe_member, syntax observe_alias, syntax observe_plain, syntax observe_success, syntax observe_type, syntax observe_tuple)
import helpers as H
import success as Success
import relay (syntax forward)
pub syntax outer $value:expr => using expand
pub syntax outer_forward $value:expr => using expand_forward
pub syntax outer_resolve $value:expr => using expand_resolve
pub syntax outer_member $value:expr => using expand_member
pub syntax outer_alias $value:expr => using expand_alias
pub syntax outer_plain $value:expr => using expand_plain
pub syntax outer_success $value:expr => using expand_success
pub syntax outer_type $value:expr => using expand_type
pub syntax outer_tuple $value:expr => using expand_tuple
expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = expand_for(input, "observe", "item")
expand_forward : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_forward input = expand_for(input, "forward", "item")
expand_resolve : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_resolve input = expand_for(input, "observe_resolve", "item")
expand_member : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_member input = expand_for(input, "observe_member", "item")
expand_alias : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_alias input = expand_for(input, "observe_alias", "item")
expand_plain : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_plain input = expand_for(input, "observe_plain", "item")
expand_success : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_success input = expand_for(input, "observe_success", "item")
expand_type : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_type input = expand_for(input, "observe_type", "MissingType")
expand_tuple : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand_tuple input = expand_for(input, "observe_tuple", "MissingType")
expand_for : (Syntax.Input, String, String) -> Syntax.MacroResult ! {Syntax.Ops}
expand_for (input, target, spelling) = {
    let invocation = Syntax.invocation_origin(input)
    let definition = Syntax.definition_origin(input)
    let causes = Syntax.MoreOrigins(invocation, Syntax.MoreOrigins(definition, Syntax.NoOrigins))
    match Syntax.combine_origins(input, causes) {
        Syntax.Combined(combined) => make_head(input, target, spelling, invocation, definition, combined)
        _ => Syntax.Rejected(Syntax.MacroDiagnostic("combine failed", invocation, Syntax.NoOrigins))
    }
}
make_head : (Syntax.Input, String, String, Syntax.Origin, Syntax.Origin, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
make_head (input, target, spelling, invocation, definition, combined) = match Syntax.definition_identifier(input, target, definition) {
    Syntax.MadeIdentifier(head) => make_name(input, head, spelling, invocation, definition, combined)
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("head failed", invocation, Syntax.NoOrigins))
}
make_name : (Syntax.Input, Syntax.Identifier, String, Syntax.Origin, Syntax.Origin, Syntax.Origin) -> Syntax.MacroResult ! {Syntax.Ops}
make_name (input, head, spelling, invocation, definition, combined) = match Syntax.caller_identifier(input, spelling, combined) {
    Syntax.MadeIdentifier(name) => {
        match (Syntax.make_token(Syntax.Equal, "="), Syntax.capture(input, 0)) {
            (Syntax.MadeToken(equal), Syntax.Captured(Syntax.ExpressionCapture(value))) => {
                let last = Syntax.MoreNodes(Syntax.ExpressionNode(value, invocation), Syntax.NoNodes)
                let after_equal = Syntax.MoreNodes(Syntax.TokenNode(equal, invocation), last)
                let tail = Syntax.MoreNodes(Syntax.IdentifierNode(name, combined), after_equal)
                let nodes = Syntax.MoreNodes(Syntax.IdentifierNode(head, definition), tail)
                Syntax.Expanded(Syntax.Syntax(nodes))
            }
            _ => Syntax.Rejected(Syntax.MacroDiagnostic("tail failed", invocation, Syntax.NoOrigins))
        }
    }
    _ => Syntax.Rejected(Syntax.MacroDiagnostic("name failed", invocation, Syntax.NoOrigins))
}
pub syntax annotated $value:expr => {
    let x : Int = $value
    42
}

pub syntax annotated_function $value:expr => {
    let x : Int -> Bool = $value
    42
}
