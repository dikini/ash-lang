use ash::{
    lexer::lex,
    parser::{
        ConcreteElement, Event, ExpectedForm, NodeKind, ParseContext, ParseReason, ProjectionError,
        ResourceFailure, STRUCTURAL_DEPTH_LIMIT, SynchronizationBoundary, parse, project_module,
    },
    source::SourceFile,
    surface::{SurfaceDefinitionKind, SurfaceKindKind, SurfaceTypeKind},
};

fn spanned_text(source: &SourceFile, span: ash::source::Span) -> &str {
    let range = span.range();
    &source.text()[range.start() as usize..range.end() as usize]
}

fn assert_type_to_type(kind: &ash::surface::SurfaceKind) {
    let SurfaceKindKind::Function { domain, codomain } = &kind.kind else {
        panic!("expected a function kind, found {kind:?}");
    };
    assert_eq!(domain.kind, SurfaceKindKind::Type);
    assert_eq!(codomain.kind, SurfaceKindKind::Type);
}

fn assert_parameter(
    source: &SourceFile,
    parameter: &ash::surface::SurfaceTypeParameter,
    expected_name: &str,
    expected_parameter: &str,
    has_function_kind: bool,
) {
    assert_eq!(parameter.name.text, expected_name);
    assert_eq!(spanned_text(source, parameter.name.span), expected_name);
    assert_eq!(spanned_text(source, parameter.span), expected_parameter);
    match (&parameter.kind, has_function_kind) {
        (Some(kind), true) => assert_type_to_type(kind),
        (None, false) => {}
        (actual, expected) => panic!(
            "unexpected kind annotation for {expected_name}: expected function={expected}, found {actual:?}"
        ),
    }
}

fn assert_complete_balanced_events(tree: &ash::parser::ConcreteTree) {
    let mut depth = 0_usize;
    let mut token_indexes = Vec::new();
    for event in tree.events() {
        match event {
            Event::Start(_) => depth = depth.saturating_add(1),
            Event::Token(index) => token_indexes.push(*index),
            Event::Finish => {
                assert!(depth > 0, "a finish event must close an open node");
                depth -= 1;
            }
            Event::Missing { .. } | Event::Error(_) => {}
        }
    }
    assert_eq!(depth, 0, "all concrete nodes must be closed");
    assert_eq!(
        token_indexes,
        (0..tree.tokens().len()).collect::<Vec<_>>(),
        "events must retain every lexer token exactly once"
    );
}

fn count_nodes(tree: &ash::parser::ConcreteTree, expected: NodeKind) -> usize {
    let mut count = 0;
    let mut pending = tree.root().into_iter().collect::<Vec<_>>();
    while let Some(node) = pending.pop() {
        count += usize::from(node.kind == expected);
        pending.extend(node.children.iter().filter_map(|child| match child {
            ConcreteElement::Node(node) => Some(node),
            ConcreteElement::Token(_)
            | ConcreteElement::Missing { .. }
            | ConcreteElement::Error(_) => None,
        }));
    }
    count
}

#[test]
fn projects_contextual_kinds_and_explicit_binders() {
    let text = "type Wrapped<F : Type -> Type, A> = Wrapped(F<A>)\n\
interface Functor<F : Type -> Type> {\n\
map : (Int -> Int, F<Int>) -> F<Int>\n\
}\n\
keep<F : Type -> Type, A> : F<A> -> F<A>\n\
keep value = value\n\
impl<F : Type -> Type> Functor<Wrapped<F>> {\n\
map (function, Wrapped(value)) = Wrapped(function(value))\n\
}\n\
fn keep_operational<F : Type -> Type, A>(value : F<A>) -> F<A> {\n\
value\n\
}\n\
type Grouped<F : (Type -> Type) -> Type> = Grouped\n\
type Right<F : Type -> Type -> Type> = Right\n\
type Explicit<A : Type, B> = Explicit\n\
type Type = Type\n";
    let source = SourceFile::new("kinds-syntax.ash", text).expect("syntax source should fit");
    let lexed = lex(&source).expect("syntax source should lex");
    assert!(lexed.diagnostics.is_empty(), "{:?}", lexed.diagnostics);

    let tree = parse(lexed);
    assert!(
        tree.parse_diagnostics().is_empty(),
        "unexpected parse diagnostics: {:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).expect("kind and binder syntax should project");

    assert_eq!(module.type_declarations[0].name.text, "Wrapped");
    let [wrapped_f, wrapped_a] = module.type_declarations[0].parameters.as_slice() else {
        panic!("expected both nominal parameters");
    };
    assert_eq!(wrapped_f.name.text, "F");
    assert_eq!(spanned_text(&source, wrapped_f.name.span), "F");
    assert_eq!(spanned_text(&source, wrapped_f.span), "F : Type -> Type");
    assert_type_to_type(wrapped_f.kind.as_ref().expect("F should retain its kind"));
    assert_eq!(wrapped_a.name.text, "A");
    assert_eq!(wrapped_a.kind, None);

    let [interface] = module.interfaces.as_slice() else {
        panic!("expected one interface");
    };
    assert_eq!(interface.parameter.name.text, "F");
    assert_eq!(
        spanned_text(&source, interface.parameter.span),
        "F : Type -> Type"
    );
    assert_type_to_type(
        interface
            .parameter
            .kind
            .as_ref()
            .expect("the interface parameter should retain its kind"),
    );

    let SurfaceDefinitionKind::Equational(keep) = &module.definitions[0].kind else {
        panic!("expected the equational keep definition");
    };
    let keep_parameters = keep
        .interface
        .type_parameters
        .as_ref()
        .expect("the explicit equational list must remain present");
    let [keep_f, keep_a] = keep_parameters.as_slice() else {
        panic!("expected the ordered F, A equational binders");
    };
    assert_parameter(&source, keep_f, "F", "F : Type -> Type", true);
    assert_parameter(&source, keep_a, "A", "A", false);

    let SurfaceDefinitionKind::InlineOperational(operational) = &module.definitions[1].kind else {
        panic!("expected the inline operational definition");
    };
    let [operational_f, operational_a] = operational
        .header
        .type_parameters
        .as_ref()
        .expect("the explicit operational list must remain present")
        .as_slice()
    else {
        panic!("expected the ordered F, A operational binders");
    };
    assert_parameter(&source, operational_f, "F", "F : Type -> Type", true);
    assert_parameter(&source, operational_a, "A", "A", false);

    let [implementation] = module.implementations.as_slice() else {
        panic!("expected one implementation");
    };
    let [impl_f] = implementation
        .type_parameters
        .as_ref()
        .expect("the explicit implementation list must remain present")
        .as_slice()
    else {
        panic!("expected one implementation parameter");
    };
    assert_type_to_type(impl_f.kind.as_ref().expect("F should retain its kind"));

    let grouped = &module.type_declarations[1].parameters[0];
    let SurfaceKindKind::Function { domain, codomain } = &grouped
        .kind
        .as_ref()
        .expect("grouped F should retain its kind")
        .kind
    else {
        panic!("expected the outer grouped function kind");
    };
    assert_eq!(spanned_text(&source, domain.span), "(Type -> Type)");
    assert_type_to_type(domain);
    assert_eq!(codomain.kind, SurfaceKindKind::Type);

    let right = module.type_declarations[2].parameters[0]
        .kind
        .as_ref()
        .expect("right-associated F should retain its kind");
    let SurfaceKindKind::Function { domain, codomain } = &right.kind else {
        panic!("expected the outer function kind");
    };
    assert_eq!(domain.kind, SurfaceKindKind::Type);
    assert_type_to_type(codomain);

    let [explicit_a, explicit_b] = module.type_declarations[3].parameters.as_slice() else {
        panic!("expected explicit A and omitted B parameters");
    };
    assert_eq!(explicit_a.name.text, "A");
    assert_eq!(spanned_text(&source, explicit_a.name.span), "A");
    assert_eq!(spanned_text(&source, explicit_a.span), "A : Type");
    let explicit_a_kind = explicit_a
        .kind
        .as_ref()
        .expect("A : Type must remain an explicit annotation");
    assert_eq!(explicit_a_kind.kind, SurfaceKindKind::Type);
    assert_eq!(spanned_text(&source, explicit_a_kind.span), "Type");
    assert_eq!(explicit_b.name.text, "B");
    assert_eq!(spanned_text(&source, explicit_b.name.span), "B");
    assert_eq!(spanned_text(&source, explicit_b.span), "B");
    assert_eq!(explicit_b.kind, None);

    assert_eq!(module.type_declarations[4].name.text, "Type");
    assert!(matches!(
        module.type_declarations[4].constructors[0]
            .fields
            .as_slice(),
        []
    ));
    assert!(matches!(
        module.type_declarations[0].constructors[0].fields[0].kind,
        SurfaceTypeKind::Application { .. }
    ));
}

#[test]
fn malformed_kind_and_binder_headers_recover_without_projection() {
    let cases = [
        (
            "missing kind",
            "type Bad<F : > = Bad\ntype Next = Next\n",
            ParseReason::ExpectedForm,
            Some(ExpectedForm::Kind),
            ">",
            2,
            SynchronizationBoundary::TypeParameterListClosing,
            ">",
        ),
        (
            "missing arrow codomain",
            "type Bad<F : Type -> > = Bad\ntype Next = Next\n",
            ParseReason::ExpectedForm,
            Some(ExpectedForm::Kind),
            ">",
            2,
            SynchronizationBoundary::TypeParameterListClosing,
            ">",
        ),
        (
            "duplicate separators",
            "type Bad<F,, A> = Bad\ntype Next = Next\n",
            ParseReason::ExpectedForm,
            Some(ExpectedForm::Identifier),
            ",",
            2,
            SynchronizationBoundary::TypeParameterSeparator,
            ",",
        ),
        (
            "empty global binder list",
            "keep<> : Int -> Int\nkeep value = value\ntype Next = Next\n",
            ParseReason::ExpectedForm,
            Some(ExpectedForm::Identifier),
            ">",
            1,
            SynchronizationBoundary::TypeParameterListClosing,
            ">",
        ),
        (
            "implementation list after the head",
            "impl Functor<F><F> {\n}\ntype Next = Next\n",
            ParseReason::ExpectedForm,
            Some(ExpectedForm::LeftBrace),
            "<",
            1,
            SynchronizationBoundary::ImplementationBodyOpeningBrace,
            "{",
        ),
        (
            "empty implementation binder list",
            "impl<> Functor<Int> {\n}\ntype Next = Next\n",
            ParseReason::ExpectedForm,
            Some(ExpectedForm::Identifier),
            ">",
            1,
            SynchronizationBoundary::TypeParameterListClosing,
            ">",
        ),
        (
            "two interface parameters",
            "interface Bad<F, A> {\nmethod : F\n}\ntype Next = Next\n",
            ParseReason::ExpectedForm,
            Some(ExpectedForm::InterfaceParameter),
            ",",
            1,
            SynchronizationBoundary::TypeParameterSeparator,
            ",",
        ),
    ];

    for (
        label,
        text,
        reason,
        expected,
        primary_text,
        expected_type_declarations,
        expected_boundary,
        synchronization_text,
    ) in cases
    {
        let source = SourceFile::new(format!("{label}.ash"), text)
            .expect("malformed syntax source should fit");
        let lexed = lex(&source).expect("malformed syntax source should lex");
        assert!(
            lexed.diagnostics.is_empty(),
            "{label}: {:?}",
            lexed.diagnostics
        );
        let tree = parse(lexed);
        assert_complete_balanced_events(&tree);
        assert_eq!(tree.parse_diagnostics().len(), 1, "{label}: no cascades");
        let diagnostic = tree
            .parse_diagnostics()
            .first()
            .unwrap_or_else(|| panic!("{label}: expected a parser diagnostic"));
        assert_eq!(diagnostic.reason, reason, "{label}");
        assert_eq!(
            diagnostic.expected.as_deref(),
            expected.map(|form| match form {
                ExpectedForm::Kind => "a kind",
                ExpectedForm::RightParen => ")",
                ExpectedForm::Identifier => "an identifier",
                ExpectedForm::LeftBrace => "{",
                ExpectedForm::InterfaceParameter => "one interface type parameter",
                _ => unreachable!("the table contains only named expected forms"),
            }),
            "{label}"
        );
        assert_eq!(
            spanned_text(&source, diagnostic.primary.span()),
            primary_text,
            "{label}"
        );
        assert!(
            matches!(
                diagnostic.context.as_slice(),
                [ParseContext::Synchronization { boundary, span }]
                    if *boundary == expected_boundary
                        && spanned_text(&source, *span) == synchronization_text
            ),
            "{label}: unexpected recovery context: {:?}",
            diagnostic.context
        );
        assert_eq!(
            count_nodes(&tree, NodeKind::TypeDeclaration),
            expected_type_declarations,
            "{label}: the following declaration must parse independently"
        );
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent),
            "{label}"
        );
    }
}

#[test]
fn recovered_kind_group_does_not_permit_a_later_missing_line_end() {
    let text = "type Bad<F : (Type -> Type> = Bad\n\
type Next = Next type Later = Later\n";
    let source = SourceFile::new("scoped-kind-recovery.ash", text)
        .expect("recovery regression source should fit");
    let tree = parse(lex(&source).expect("recovery regression source should lex"));

    assert_complete_balanced_events(&tree);
    assert!(
        tree.parse_diagnostics().iter().any(|diagnostic| {
            diagnostic.reason == ParseReason::ExpectedForm
                && diagnostic.expected.as_deref() == Some("a logical line end")
                && spanned_text(&source, diagnostic.primary.span()) == "type"
        }),
        "the later same-line declaration must not inherit group recovery: {:?}",
        tree.parse_diagnostics()
    );
    assert_eq!(
        project_module(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
}

#[test]
fn unclosed_kind_group_does_not_create_a_declaration_separator() {
    let text = "type Bad<F : (Type> = Bad type Next = Next\n";
    let source = SourceFile::new("kind-group-is-not-line-end.ash", text)
        .expect("kind recovery source should fit");
    let tree = parse(lex(&source).expect("kind recovery source should lex"));

    assert_complete_balanced_events(&tree);
    let [unclosed, line_end] = tree.parse_diagnostics() else {
        panic!(
            "expected the group and declaration-boundary diagnostics: {:?}",
            tree.parse_diagnostics()
        );
    };
    assert_eq!(unclosed.reason, ParseReason::UnclosedGroup);
    assert_eq!(unclosed.expected.as_deref(), Some(")"));
    assert_eq!(spanned_text(&source, unclosed.primary.span()), "(");
    assert!(matches!(
        unclosed.context.as_slice(),
        [ParseContext::Synchronization {
            boundary: SynchronizationBoundary::TypeParameterListClosing,
            span,
        }] if spanned_text(&source, *span) == ">"
    ));
    assert_eq!(line_end.reason, ParseReason::ExpectedForm);
    assert_eq!(line_end.expected.as_deref(), Some("a logical line end"));
    assert_eq!(spanned_text(&source, line_end.primary.span()), "type");
    assert_eq!(
        project_module(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
}

#[test]
fn invalid_contextual_kind_atom_recovers_once() {
    let text = "type Bad<F : Foo> = Bad\ntype Next = Next\n";
    let source =
        SourceFile::new("invalid-kind-atom.ash", text).expect("invalid kind source should fit");
    let tree = parse(lex(&source).expect("invalid kind source should lex"));

    assert_complete_balanced_events(&tree);
    let [diagnostic] = tree.parse_diagnostics() else {
        panic!(
            "expected one causal invalid-kind diagnostic: {:?}",
            tree.parse_diagnostics()
        );
    };
    assert_eq!(diagnostic.reason, ParseReason::ExpectedForm);
    assert_eq!(diagnostic.expected.as_deref(), Some("a kind"));
    assert_eq!(spanned_text(&source, diagnostic.primary.span()), "Foo");
    assert!(matches!(
        diagnostic.context.as_slice(),
        [ParseContext::Synchronization {
            boundary: SynchronizationBoundary::TypeParameterListClosing,
            span,
        }] if spanned_text(&source, *span) == ">"
    ));
    assert_eq!(count_nodes(&tree, NodeKind::TypeDeclaration), 2);
    assert_eq!(
        project_module(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
}

#[test]
fn missing_kinds_stop_at_each_owning_header_boundary() {
    let cases = [
        (
            "nominal missing kind",
            "type Bad<F : = Bad\ntype Next = Next\n",
            SynchronizationBoundary::TypeDeclarationEqual,
            "=",
            2,
        ),
        (
            "equational missing kind",
            "keep<F : : F -> F\nkeep value = value\ntype Next = Next\n",
            SynchronizationBoundary::EquationalGlobalColon,
            ":",
            1,
        ),
        (
            "operational missing kind",
            "fn keep<F :(value : F) -> F {\nvalue\n}\ntype Next = Next\n",
            SynchronizationBoundary::OperationalParameterOpeningParen,
            "(",
            1,
        ),
        (
            "implementation missing kind",
            "impl<F : Functor<F> {\n}\ntype Next = Next\n",
            SynchronizationBoundary::ImplementationInterfaceHead,
            "Functor",
            1,
        ),
        (
            "implementation missing kind before qualified head",
            "impl<F : Library.Functor<F> {\n}\ntype Next = Next\n",
            SynchronizationBoundary::ImplementationInterfaceHead,
            "Library",
            1,
        ),
        (
            "nominal missing arrow codomain",
            "type Bad<F : Type -> = Bad\ntype Next = Next\n",
            SynchronizationBoundary::TypeDeclarationEqual,
            "=",
            2,
        ),
        (
            "equational missing arrow codomain",
            "keep<F : Type -> : F -> F\nkeep value = value\ntype Next = Next\n",
            SynchronizationBoundary::EquationalGlobalColon,
            ":",
            1,
        ),
        (
            "operational missing arrow codomain",
            "fn keep<F : Type ->(value : F) -> F {\nvalue\n}\ntype Next = Next\n",
            SynchronizationBoundary::OperationalParameterOpeningParen,
            "(",
            1,
        ),
        (
            "implementation missing arrow codomain",
            "impl<F : Type -> Functor<F> {\n}\ntype Next = Next\n",
            SynchronizationBoundary::ImplementationInterfaceHead,
            "Functor",
            1,
        ),
    ];

    for (label, text, expected_boundary, owner_text, type_declarations) in cases {
        let source = SourceFile::new(format!("{label}.ash"), text)
            .expect("owner-boundary source should fit");
        let tree = parse(lex(&source).expect("owner-boundary source should lex"));

        assert_complete_balanced_events(&tree);
        let [kind, terminator] = tree.parse_diagnostics() else {
            panic!(
                "{label}: expected only the causal kind and list diagnostics: {:?}",
                tree.parse_diagnostics()
            );
        };
        assert_eq!(kind.reason, ParseReason::ExpectedForm, "{label}");
        assert_eq!(kind.expected.as_deref(), Some("a kind"), "{label}");
        assert_eq!(terminator.reason, ParseReason::ExpectedForm, "{label}");
        assert_eq!(terminator.expected.as_deref(), Some(">"), "{label}");
        for diagnostic in [kind, terminator] {
            assert_eq!(
                spanned_text(&source, diagnostic.primary.span()),
                owner_text,
                "{label}"
            );
            assert!(
                matches!(
                    diagnostic.context.as_slice(),
                    [ParseContext::Synchronization { boundary, span }]
                        if *boundary == expected_boundary
                            && spanned_text(&source, *span) == owner_text
                ),
                "{label}: unexpected owner context: {:?}",
                diagnostic.context
            );
        }
        assert_eq!(
            count_nodes(&tree, NodeKind::TypeDeclaration),
            type_declarations,
            "{label}: the following declaration must remain independent"
        );
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent),
            "{label}"
        );
    }
}

#[test]
fn missing_type_parameter_closers_stop_declarations_at_line_end_or_eof() {
    let cases = [
        (
            "nominal line end",
            "type Bad<F\ntype Next = Next\n",
            "\n",
            2,
        ),
        ("equational line end", "keep<F\ntype Next = Next\n", "\n", 1),
        (
            "operational line end",
            "fn keep<F\ntype Next = Next\n",
            "\n",
            1,
        ),
        (
            "implementation line end",
            "impl<F\ntype Next = Next\n",
            "\n",
            1,
        ),
        ("nominal eof", "type Bad<F", "", 1),
        ("equational eof", "keep<F", "", 0),
        ("operational eof", "fn keep<F", "", 0),
        ("implementation eof", "impl<F", "", 0),
    ];

    for (label, text, boundary_text, type_declarations) in cases {
        let source = SourceFile::new(format!("{label}.ash"), text)
            .expect("missing-closer source should fit");
        let tree = parse(lex(&source).expect("missing-closer source should lex"));

        assert_complete_balanced_events(&tree);
        let [diagnostic] = tree.parse_diagnostics() else {
            panic!(
                "{label}: expected one missing-list-closer diagnostic: {:?}",
                tree.parse_diagnostics()
            );
        };
        assert_eq!(diagnostic.reason, ParseReason::ExpectedForm, "{label}");
        assert_eq!(diagnostic.expected.as_deref(), Some(">"), "{label}");
        assert_eq!(
            spanned_text(&source, diagnostic.primary.span()),
            boundary_text,
            "{label}"
        );
        let expected_boundary = if boundary_text.is_empty() {
            SynchronizationBoundary::EndOfFile
        } else {
            SynchronizationBoundary::LogicalLineEnd
        };
        assert!(
            matches!(
                diagnostic.context.as_slice(),
                [ParseContext::Synchronization { boundary, span }]
                    if *boundary == expected_boundary
                        && spanned_text(&source, *span) == boundary_text
            ),
            "{label}: unexpected termination context: {:?}",
            diagnostic.context
        );
        assert_eq!(
            count_nodes(&tree, NodeKind::TypeDeclaration),
            type_declarations,
            "{label}"
        );
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent),
            "{label}"
        );
    }
}

#[test]
fn direct_owner_after_complete_parameters_reports_only_the_missing_greater() {
    let cases = [
        (
            "nominal",
            "type Bad<F = Bad\ntype Next = Next\n",
            SynchronizationBoundary::TypeDeclarationEqual,
            "=",
            2,
        ),
        (
            "equational",
            "keep<F : Type : F -> F\nkeep value = value\ntype Next = Next\n",
            SynchronizationBoundary::EquationalGlobalColon,
            ":",
            1,
        ),
        (
            "operational",
            "fn keep<F(value : F) -> F {\nvalue\n}\ntype Next = Next\n",
            SynchronizationBoundary::OperationalParameterOpeningParen,
            "(",
            1,
        ),
        (
            "implementation",
            "impl<F Functor<F> {\n}\ntype Next = Next\n",
            SynchronizationBoundary::ImplementationInterfaceHead,
            "Functor",
            1,
        ),
    ];

    for (label, text, expected_boundary, owner_text, type_declarations) in cases {
        let source = SourceFile::new(format!("direct-{label}-owner.ash"), text)
            .expect("direct-owner source should fit");
        let tree = parse(lex(&source).expect("direct-owner source should lex"));

        assert_complete_balanced_events(&tree);
        let [diagnostic] = tree.parse_diagnostics() else {
            panic!(
                "{label}: expected one missing-list-closer diagnostic: {:?}",
                tree.parse_diagnostics()
            );
        };
        assert_eq!(diagnostic.reason, ParseReason::ExpectedForm, "{label}");
        assert_eq!(diagnostic.expected.as_deref(), Some(">"), "{label}");
        assert_eq!(
            spanned_text(&source, diagnostic.primary.span()),
            owner_text,
            "{label}"
        );
        assert!(matches!(
            diagnostic.context.as_slice(),
            [ParseContext::Synchronization { boundary, span }]
                if *boundary == expected_boundary
                    && spanned_text(&source, *span) == owner_text
        ));
        assert_eq!(
            count_nodes(&tree, NodeKind::TypeDeclaration),
            type_declarations,
            "{label}"
        );
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent),
            "{label}"
        );
    }
}

#[test]
fn implementation_type_named_heads_own_direct_and_scanned_list_recovery() {
    let cases = [
        (
            "direct unqualified",
            "impl<F Type<F> {\n}\ntype Next = Next\n",
            "Type",
            "Type",
        ),
        (
            "direct qualified",
            "impl<F Type.Functor<F> {\n}\ntype Next = Next\n",
            "Type",
            "Type",
        ),
        (
            "scanned unqualified",
            "impl<F junk Type<F> {\n}\ntype Next = Next\n",
            "junk",
            "Type",
        ),
        (
            "scanned qualified",
            "impl<F junk Type.Functor<F> {\n}\ntype Next = Next\n",
            "junk",
            "Type",
        ),
    ];

    for (label, text, primary_text, synchronization_text) in cases {
        let source = SourceFile::new(format!("implementation-Type-owner-{label}.ash"), text)
            .expect("Type-named owner source should fit");
        let tree = parse(lex(&source).expect("Type-named owner source should lex"));

        assert_complete_balanced_events(&tree);
        let [diagnostic] = tree.parse_diagnostics() else {
            panic!(
                "{label}: expected one missing-list-closer diagnostic: {:?}",
                tree.parse_diagnostics()
            );
        };
        assert_eq!(diagnostic.reason, ParseReason::ExpectedForm, "{label}");
        assert_eq!(diagnostic.expected.as_deref(), Some(">"), "{label}");
        assert_eq!(
            spanned_text(&source, diagnostic.primary.span()),
            primary_text,
            "{label}"
        );
        assert!(matches!(
            diagnostic.context.as_slice(),
            [ParseContext::Synchronization {
                boundary: SynchronizationBoundary::ImplementationInterfaceHead,
                span,
            }] if spanned_text(&source, *span) == synchronization_text
        ));
        assert_eq!(count_nodes(&tree, NodeKind::TypeDeclaration), 1, "{label}");
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent),
            "{label}"
        );
    }
}

#[test]
fn interface_parameter_closer_reports_greater_at_body_or_eof() {
    let cases = [
        (
            "body",
            "interface Bad<F {\nmethod : F\n}\ntype Next = Next\n",
            "{",
            SynchronizationBoundary::InterfaceBodyOpeningBrace,
            1,
        ),
        (
            "eof",
            "interface Bad<F",
            "",
            SynchronizationBoundary::EndOfFile,
            0,
        ),
    ];

    for (label, text, boundary_text, expected_boundary, type_declarations) in cases {
        let source = SourceFile::new(format!("interface-missing-greater-{label}.ash"), text)
            .expect("interface source should fit");
        let tree = parse(lex(&source).expect("interface source should lex"));

        assert_complete_balanced_events(&tree);
        let [diagnostic] = tree.parse_diagnostics() else {
            panic!(
                "{label}: expected one missing interface closer diagnostic: {:?}",
                tree.parse_diagnostics()
            );
        };
        assert_eq!(diagnostic.reason, ParseReason::ExpectedForm, "{label}");
        assert_eq!(diagnostic.expected.as_deref(), Some(">"), "{label}");
        assert_eq!(
            spanned_text(&source, diagnostic.primary.span()),
            boundary_text,
            "{label}"
        );
        assert!(matches!(
            diagnostic.context.as_slice(),
            [ParseContext::Synchronization { boundary, span }]
                if *boundary == expected_boundary
                    && spanned_text(&source, *span) == boundary_text
        ));
        assert_eq!(
            count_nodes(&tree, NodeKind::TypeDeclaration),
            type_declarations,
            "{label}"
        );
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent),
            "{label}"
        );
    }
}

#[test]
fn implementation_invalid_kind_atoms_recover_at_the_parameter_closer() {
    let cases = [
        ("atom", "impl<F : Foo> Functor<F> {\n}\ntype Next = Next\n"),
        (
            "arrow codomain",
            "impl<F : Type -> Foo> Functor<F> {\n}\ntype Next = Next\n",
        ),
    ];

    for (label, text) in cases {
        let source = SourceFile::new(format!("implementation-invalid-kind-{label}.ash"), text)
            .expect("implementation kind source should fit");
        let tree = parse(lex(&source).expect("implementation kind source should lex"));

        assert_complete_balanced_events(&tree);
        let [diagnostic] = tree.parse_diagnostics() else {
            panic!(
                "{label}: expected one causal kind diagnostic: {:?}",
                tree.parse_diagnostics()
            );
        };
        assert_eq!(diagnostic.reason, ParseReason::ExpectedForm, "{label}");
        assert_eq!(diagnostic.expected.as_deref(), Some("a kind"), "{label}");
        assert_eq!(
            spanned_text(&source, diagnostic.primary.span()),
            "Foo",
            "{label}"
        );
        assert!(matches!(
            diagnostic.context.as_slice(),
            [ParseContext::Synchronization {
                boundary: SynchronizationBoundary::TypeParameterListClosing,
                span,
            }] if spanned_text(&source, *span) == ">"
        ));
        assert_eq!(count_nodes(&tree, NodeKind::TypeDeclaration), 1, "{label}");
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent),
            "{label}"
        );
    }
}

#[test]
fn interface_parameter_recovery_owns_kind_list_and_body_boundaries() {
    let cases = [
        (
            "missing kind",
            "interface Bad<F : {\nmethod : F\n}\ntype Next = Next\n",
            vec!["a kind", ">"],
            "{",
            SynchronizationBoundary::InterfaceBodyOpeningBrace,
        ),
        (
            "missing arrow codomain",
            "interface Bad<F : Type -> {\nmethod : F\n}\ntype Next = Next\n",
            vec!["a kind", ">"],
            "{",
            SynchronizationBoundary::InterfaceBodyOpeningBrace,
        ),
        (
            "missing closer at line end",
            "interface Bad<F\ntype Next = Next\n",
            vec![">"],
            "\n",
            SynchronizationBoundary::LogicalLineEnd,
        ),
        (
            "scan to body",
            "interface Bad<F junk {\nmethod : F\n}\ntype Next = Next\n",
            vec![">"],
            "junk",
            SynchronizationBoundary::InterfaceBodyOpeningBrace,
        ),
    ];

    for (label, text, expected_forms, primary_text, expected_boundary) in cases {
        let source = SourceFile::new(format!("interface-recovery-{label}.ash"), text)
            .expect("interface recovery source should fit");
        let tree = parse(lex(&source).expect("interface recovery source should lex"));

        assert_complete_balanced_events(&tree);
        assert_eq!(
            tree.parse_diagnostics().len(),
            expected_forms.len(),
            "{label}: recovery must not cascade: {:?}",
            tree.parse_diagnostics()
        );
        for (diagnostic, expected_form) in tree.parse_diagnostics().iter().zip(expected_forms) {
            assert_eq!(diagnostic.reason, ParseReason::ExpectedForm, "{label}");
            assert_eq!(
                diagnostic.expected.as_deref(),
                Some(expected_form),
                "{label}"
            );
            assert_eq!(
                spanned_text(&source, diagnostic.primary.span()),
                primary_text,
                "{label}"
            );
            let synchronization_text =
                if expected_boundary == SynchronizationBoundary::InterfaceBodyOpeningBrace {
                    "{"
                } else {
                    "\n"
                };
            assert!(
                matches!(
                    diagnostic.context.as_slice(),
                    [ParseContext::Synchronization { boundary, span }]
                        if *boundary == expected_boundary
                            && spanned_text(&source, *span) == synchronization_text
                ),
                "{label}: unexpected synchronization: {:?}",
                diagnostic.context
            );
        }
        assert_eq!(
            count_nodes(&tree, NodeKind::TypeDeclaration),
            1,
            "{label}: the following declaration must remain independent"
        );
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent),
            "{label}"
        );
    }
}

#[test]
fn missing_type_parameter_terminator_names_and_owns_the_header_boundary() {
    let cases = [
        (
            "nominal",
            "type Bad<F junk = Bad\ntype Next = Next\n",
            SynchronizationBoundary::TypeDeclarationEqual,
            "=",
            "parsing resumes at this nominal declaration equals sign",
        ),
        (
            "equational global",
            "keep<F junk : F -> F\nkeep value = value\ntype Next = Next\n",
            SynchronizationBoundary::EquationalGlobalColon,
            ":",
            "parsing resumes at this equational global colon",
        ),
        (
            "operational global",
            "fn keep<F junk(value : F) -> F {\nvalue\n}\ntype Next = Next\n",
            SynchronizationBoundary::OperationalParameterOpeningParen,
            "(",
            "parsing resumes at this operational parameter opening parenthesis",
        ),
        (
            "implementation",
            "impl<F junk Functor<F> {\n}\ntype Next = Next\n",
            SynchronizationBoundary::ImplementationInterfaceHead,
            "Functor",
            "parsing resumes at this implementation interface head",
        ),
    ];

    for (label, text, expected_boundary, synchronization, related_message) in cases {
        let source = SourceFile::new(format!("missing-{label}-terminator.ash"), text)
            .expect("missing terminator source should fit");
        let tree = parse(lex(&source).expect("missing terminator source should lex"));

        assert_complete_balanced_events(&tree);
        let [diagnostic] = tree.parse_diagnostics() else {
            panic!(
                "{label}: expected one missing-terminator diagnostic: {:?}",
                tree.parse_diagnostics()
            );
        };
        assert_eq!(diagnostic.reason, ParseReason::ExpectedForm, "{label}");
        assert_eq!(diagnostic.expected.as_deref(), Some(">"), "{label}");
        assert_eq!(
            spanned_text(&source, diagnostic.primary.span()),
            "junk",
            "{label}"
        );
        let [ParseContext::Synchronization { boundary, span }] = diagnostic.context.as_slice()
        else {
            panic!("{label}: the missing terminator must retain its owning boundary");
        };
        assert_eq!(*boundary, expected_boundary, "{label}");
        assert_eq!(spanned_text(&source, *span), synchronization, "{label}");
        assert_eq!(diagnostic.related.len(), 1, "{label}");
        assert_eq!(diagnostic.related[0].message(), related_message, "{label}");
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent),
            "{label}"
        );
    }
}

#[test]
fn legacy_headers_remain_distinct_from_present_explicit_lists() {
    let text = "type Box<A> = Box(A)\n\
interface Read<A> {\n\
read : A -> Int\n\
}\n\
value : A -> A\n\
value item = item\n\
fn operational(item : A) -> A {\n\
item\n\
}\n\
impl Read<Box<A>> {\n\
read (Box(item)) = 0\n\
}\n";
    let source =
        SourceFile::new("legacy-kinds-syntax.ash", text).expect("legacy syntax source should fit");
    let tree = parse(lex(&source).expect("legacy syntax source should lex"));
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).expect("legacy headers should still project");

    assert_eq!(module.type_declarations[0].parameters[0].kind, None);
    assert_eq!(module.interfaces[0].parameter.kind, None);
    let SurfaceDefinitionKind::Equational(equational) = &module.definitions[0].kind else {
        panic!("expected an equational global");
    };
    assert_eq!(equational.interface.type_parameters, None);
    let SurfaceDefinitionKind::InlineOperational(operational) = &module.definitions[1].kind else {
        panic!("expected an operational global");
    };
    assert_eq!(operational.header.type_parameters, None);
    assert_eq!(module.implementations[0].type_parameters, None);
}

#[test]
fn kind_arrows_share_the_structural_depth_budget() {
    let source_at = SourceFile::new(
        "kind-depth-at.ash",
        format!(
            "type K<F : {}Type> = K\n",
            "Type -> ".repeat(STRUCTURAL_DEPTH_LIMIT)
        ),
    )
    .expect("the at-limit kind source should fit");
    let at = parse(lex(&source_at).expect("the at-limit kind source should lex"));
    assert_eq!(at.resource_failure(), None);
    project_module(&source_at, &at).expect("the at-limit kind source should project");

    let source_over = SourceFile::new(
        "kind-depth-over.ash",
        format!(
            "type K<F : {}Type> = K\n",
            "Type -> ".repeat(STRUCTURAL_DEPTH_LIMIT + 1)
        ),
    )
    .expect("the over-limit kind source should fit");
    let over = parse(lex(&source_over).expect("the over-limit kind source should lex"));
    assert_eq!(
        over.resource_failure(),
        Some(ResourceFailure::StructuralDepth {
            limit: STRUCTURAL_DEPTH_LIMIT
        })
    );
    assert_complete_balanced_events(&over);
}
