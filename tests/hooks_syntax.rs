use ash::{
    lexer::{TokenKind, lex},
    parser::{
        ConcreteElement, NodeKind, ResourceFailure, STRUCTURAL_DEPTH_LIMIT, parse, project_module,
    },
    source::{SourceFile, Span},
    surface::{
        SurfaceDefinitionKind, SurfaceExpr, SurfaceExprKind, SurfaceModule, SurfaceReference,
    },
};

fn parses(expression: &str) -> bool {
    let source = SourceFile::new(
        "hooks-syntax.ash",
        format!("main : Unit -> Int\nmain () = {expression}\n"),
    )
    .unwrap();
    let tree = parse(lex(&source).unwrap());
    tree.lexical_diagnostics().is_empty()
        && tree.parse_diagnostics().is_empty()
        && project_module(&source, &tree).is_ok()
}

fn project(expression: &str) -> (SourceFile, SurfaceModule) {
    let source = SourceFile::new(
        "hooks-syntax.ash",
        format!("main : Unit -> Int\nmain () = {expression}\n"),
    )
    .unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(tree.lexical_diagnostics().is_empty());
    assert!(tree.parse_diagnostics().is_empty(), "{expression}");
    let module = project_module(&source, &tree).unwrap();
    (source, module)
}

fn body(module: &SurfaceModule) -> &SurfaceExpr {
    let SurfaceDefinitionKind::Equational(main) = &module.definitions[0].kind else {
        panic!("equational main")
    };
    &main.equations[0].body
}

fn text_at(source: &SourceFile, span: Span) -> &str {
    assert_eq!(span.source(), source.id());
    &source.text()[span.range().start() as usize..span.range().end() as usize]
}

#[test]
fn primary_positions_and_parenthesized_transformers_preserve_grouping() {
    for expression in [
        "1 + hook Adjust {\n3\n}",
        "hook Adjust {\n3\n} * 2",
        "1 + register Adjust increment {\n3\n}",
        "register Adjust increment {\n3\n} 2",
        "perform Adjust.publish hook Adjust {\n3\n}",
        "register Adjust (factory 1) {\n3\n}",
        "register Adjust (fn(value) {\nvalue\n}) {\n3\n}",
        "register Adjust hook Adjust {\nincrement\n} {\n3\n}",
        "register Adjust register Adjust increment {\nincrement\n} {\n3\n}",
        "hook Api.Adjust<Int> {\nregister Api.Adjust<Int> increment {\n3\n}\n}",
    ] {
        assert!(parses(expression), "{expression}");
    }
    let (_, module) = project("f hook Adjust {\n3\n} + register Adjust increment {\n4\n}");
    let SurfaceExprKind::Add(add) = &body(&module).kind else {
        panic!("addition encloses both primary operands")
    };
    let SurfaceExprKind::Apply(apply) = &add.left.kind else {
        panic!("application binds before addition")
    };
    assert!(matches!(apply.argument.kind, SurfaceExprKind::Hook(_)));
    assert!(matches!(add.right.kind, SurfaceExprKind::Registration(_)));
}

#[test]
fn projection_preserves_targets_arguments_and_initializer_before_owned_body() {
    let expression = "hook Api.Adjust<Int, Bool> {\nregister Api.Adjust<Int, Bool> (factory 1) {\nlet saved = 3\nsaved\n}\n}";
    let (source, module) = project(expression);
    assert_eq!(text_at(&source, body(&module).span), expression);
    let SurfaceExprKind::Hook(hook) = &body(&module).kind else {
        panic!("hook carrier")
    };
    assert_eq!(text_at(&source, hook.effect.span), "Api.Adjust<Int, Bool>");
    assert_eq!(hook.effect.arguments.len(), 2);
    assert_eq!(text_at(&source, hook.effect.arguments[0].span), "Int");
    assert_eq!(text_at(&source, hook.effect.arguments[1].span), "Bool");
    let SurfaceReference::Qualified(target) = &hook.effect.effect else {
        panic!("qualified target")
    };
    assert_eq!(text_at(&source, target.span), "Api.Adjust");
    let SurfaceExprKind::Registration(registration) = &hook.body.result.kind else {
        panic!("registration carrier")
    };
    assert_eq!(
        text_at(&source, registration.effect.span),
        "Api.Adjust<Int, Bool>"
    );
    assert_eq!(registration.effect.arguments.len(), 2);
    assert!(matches!(
        registration.transformer.kind,
        SurfaceExprKind::Apply(_)
    ));
    assert_eq!(
        text_at(&source, registration.transformer.span),
        "(factory 1)"
    );
    assert_eq!(registration.body.declarations.len(), 1);
    assert!(registration.transformer.span.range().end() < registration.body.span.range().start());
    assert_eq!(
        registration.body.span.range().end(),
        hook.body.result.span.range().end()
    );
    assert_eq!(
        hook.body.span.range().end(),
        body(&module).span.range().end()
    );
}

#[test]
fn malformed_targets_transformers_and_bodies_fail_projection() {
    for expression in [
        "hook {\n3\n}",
        "hook adjust {\n3\n}",
        "hook Api.adjust {\n3\n}",
        "hook api.Adjust {\n3\n}",
        "hook Adjust<>{\n3\n}",
        "hook Adjust<Int,>{\n3\n}",
        "hook Adjust",
        "hook Adjust 3",
        "hook Adjust {\n}",
        "hook Adjust {\n3",
        "register {\n3\n}",
        "register adjust increment {\n3\n}",
        "register Adjust {\n3\n}",
        "register Adjust increment",
        "register Adjust increment 3",
        "register Adjust increment {\n}",
        "register Adjust increment {\n3",
        "register Adjust factory 1 {\n3\n}",
        "register Adjust 1 + 2 {\n3\n}",
        "register Adjust fn(value) {\nvalue\n} {\n3\n}",
    ] {
        assert!(!parses(expression), "{expression}");
    }
}

#[test]
fn hook_and_register_are_reserved_but_publish_remains_an_identifier() {
    let source = SourceFile::new("keywords.ash", "hook register publish\n").unwrap();
    let tree = parse(lex(&source).unwrap());
    assert_eq!(tree.tokens()[0].kind, TokenKind::Hook);
    assert_eq!(tree.tokens()[1].kind, TokenKind::Register);
    assert_eq!(
        tree.tokens()[2].kind,
        TokenKind::Identifier("publish".into())
    );
    for keyword in ["hook", "register"] {
        assert!(!parses(&format!("{{\nlet {keyword} = 3\n{keyword}\n}}")));
        assert!(!parses(&format!("fn({keyword}) {{\n3\n}}")));
    }
    for expression in [
        "{\nlet publish = 3\npublish\n}",
        "perform Adjust.publish 3",
        "1 + 2 * 3",
        "f 3",
    ] {
        assert!(parses(expression), "{expression}");
    }
}

fn nested_body(prefix: &str, count: usize) -> String {
    format!(
        "{}3{}",
        format!("{prefix} {{\n").repeat(count),
        "\n}".repeat(count)
    )
}

fn nested_initializer(count: usize) -> String {
    format!(
        "{}increment{}",
        "register Adjust ".repeat(count),
        " {\n3\n}".repeat(count)
    )
}

#[test]
fn bodies_and_initializer_chains_have_exact_structural_limits_and_fresh_retries() {
    for (at_limit, beyond_limit) in [
        (
            nested_body("hook Adjust", STRUCTURAL_DEPTH_LIMIT),
            nested_body("hook Adjust", STRUCTURAL_DEPTH_LIMIT + 1),
        ),
        (
            nested_body("register Adjust increment", STRUCTURAL_DEPTH_LIMIT / 2),
            nested_body("register Adjust increment", STRUCTURAL_DEPTH_LIMIT / 2 + 1),
        ),
        (
            nested_initializer(STRUCTURAL_DEPTH_LIMIT - 1),
            nested_initializer(STRUCTURAL_DEPTH_LIMIT),
        ),
    ] {
        assert!(parses(&at_limit));
        let source = SourceFile::new(
            "deep-hooks.ash",
            format!("main : Unit -> Int\nmain () = {beyond_limit}\n"),
        )
        .unwrap();
        for _ in 0..2 {
            let tree = parse(lex(&source).unwrap());
            assert_eq!(
                tree.resource_failure(),
                Some(ResourceFailure::StructuralDepth {
                    limit: STRUCTURAL_DEPTH_LIMIT
                })
            );
            assert!(project_module(&source, &tree).is_err());
            assert!(parses(&at_limit));
        }
    }
}

#[test]
fn iterative_concrete_walk_projection_and_bounded_surface_disposal_fit_a_small_stack() {
    // Parsing owns its recursive-descent budget. Move the accepted trees to a
    // small stack to exercise iterative concrete walking/projection and disposal.
    for expression in [
        nested_body("hook Adjust", STRUCTURAL_DEPTH_LIMIT),
        nested_initializer(STRUCTURAL_DEPTH_LIMIT - 1),
    ] {
        let source = SourceFile::new(
            "small-stack-hooks.ash",
            format!("main : Unit -> Int\nmain () = {expression}\n"),
        )
        .unwrap();
        let tree = parse(lex(&source).unwrap());
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let mut pending = vec![tree.root().unwrap()];
                let mut scopes = 0;
                while let Some(node) = pending.pop() {
                    scopes += usize::from(matches!(
                        node.kind,
                        NodeKind::HookExpression | NodeKind::RegistrationExpression
                    ));
                    for child in &node.children {
                        if let ConcreteElement::Node(child) = child {
                            pending.push(child);
                        }
                    }
                }
                assert!(scopes >= STRUCTURAL_DEPTH_LIMIT - 1);
                drop(project_module(&source, &tree).unwrap());
                drop(tree);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

#[test]
fn hook_and_registration_forms_parse_as_primary_expressions() {
    for expression in [
        "hook Adjust {\n3\n}",
        "register Adjust increment {\n3\n}",
        "f hook Adjust {\n3\n}",
        "f register Adjust increment {\n3\n}",
    ] {
        assert!(parses(expression), "{expression}");
    }
}
