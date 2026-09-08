use ash::{
    lexer::{TokenKind, lex},
    parser::{
        ConcreteElement, NodeKind, ResourceFailure, STRUCTURAL_DEPTH_LIMIT, parse, project_module,
    },
    source::{SourceFile, Span},
    surface::{SurfaceDefinitionKind, SurfaceExpr, SurfaceExprKind, SurfaceModule},
};

fn source(expression: &str) -> SourceFile {
    SourceFile::new(
        "cleanup.ash",
        format!("main : Unit -> Int\nmain () = {expression}\n"),
    )
    .unwrap()
}

fn parses(expression: &str) -> bool {
    let source = source(expression);
    let tree = parse(lex(&source).unwrap());
    tree.lexical_diagnostics().is_empty()
        && tree.parse_diagnostics().is_empty()
        && project_module(&source, &tree).is_ok()
}

fn project(expression: &str) -> (SourceFile, SurfaceModule) {
    let source = source(expression);
    let tree = parse(lex(&source).unwrap());
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
fn cleanup_action_and_body_parse_and_project() {
    let source = SourceFile::new(
        "cleanup.ash",
        "main : Unit -> Int\nmain () = cleanup (fn(ignored) {\n()\n}) {\n42\n}\n",
    )
    .unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    assert!(project_module(&source, &tree).is_ok());
}

#[test]
fn primary_positions_preserve_application_and_infix_precedence() {
    for expression in [
        "1 + cleanup action {\n42\n}",
        "cleanup action {\n42\n} * 2",
        "cleanup action {\n42\n} 2",
        "f cleanup action {\n42\n}",
        "perform Stop.stop cleanup action {\n42\n}",
    ] {
        assert!(parses(expression), "{expression}");
    }
    let (_, module) = project("f cleanup action {\n42\n} + cleanup other {\n3\n}");
    let SurfaceExprKind::Add(add) = &body(&module).kind else {
        panic!("addition")
    };
    let SurfaceExprKind::Apply(apply) = &add.left.kind else {
        panic!("application")
    };
    assert!(matches!(apply.argument.kind, SurfaceExprKind::Cleanup(_)));
    assert!(matches!(add.right.kind, SurfaceExprKind::Cleanup(_)));
}

#[test]
fn full_action_expressions_stop_before_the_owned_body() {
    for action in [
        "factory 1",
        "1 + 2 * 3",
        "(factory 1)",
        "fn(ignored) {\n()\n}",
        "(fn(ignored) {\n()\n})",
        "{\naction\n}",
        "({\naction\n})",
        "cleanup first {\nsecond\n}",
        "(cleanup first {\nsecond\n})",
        "hook Adjust {\naction\n}",
        "register Adjust transformer {\naction\n}",
        "resource cell<R> c = 0 {\naction\n}",
        "match value {\n_ => action\n}",
        "handle action with Stop {\nstop ignored => resume action\n}",
    ] {
        let expression = format!("cleanup {action} {{\nlet saved = 42\nsaved\n}}");
        let (source, module) = project(&expression);
        let SurfaceExprKind::Cleanup(cleanup) = &body(&module).kind else {
            panic!("cleanup carrier")
        };
        assert_eq!(text_at(&source, body(&module).span), expression);
        assert_eq!(text_at(&source, cleanup.action.span), action);
        assert_eq!(
            text_at(&source, cleanup.body.span),
            "{\nlet saved = 42\nsaved\n}"
        );
        assert_eq!(cleanup.body.declarations.len(), 1);
        assert!(cleanup.action.span.range().end() < cleanup.body.span.range().start());
        assert_eq!(
            cleanup.body.span.range().end(),
            body(&module).span.range().end()
        );
    }
}

#[test]
fn missing_actions_and_malformed_bodies_reject_projection() {
    for expression in [
        "cleanup",
        "cleanup {\n42\n}",
        "cleanup action",
        "cleanup action 42",
        "cleanup action {\n}",
        "cleanup action {\n42",
        "cleanup (action {\n42\n}",
        "cleanup 1 + {\n42\n}",
        "cleanup fn(ignored) {\n()\n}",
        "cleanup action { 42 }",
    ] {
        assert!(!parses(expression), "{expression}");
    }
}

#[test]
fn cleanup_is_reserved_without_reserving_related_identifiers() {
    let source = SourceFile::new("keywords.ash", "cleanup cleanup_action action\n").unwrap();
    let tree = parse(lex(&source).unwrap());
    assert_eq!(tree.tokens()[0].kind, TokenKind::Cleanup);
    assert_eq!(
        tree.tokens()[1].kind,
        TokenKind::Identifier("cleanup_action".into())
    );
    assert_eq!(
        tree.tokens()[2].kind,
        TokenKind::Identifier("action".into())
    );
    for expression in [
        "{\nlet cleanup = 42\ncleanup\n}",
        "fn(cleanup) {\n42\n}",
        "Api.cleanup",
    ] {
        assert!(!parses(expression), "{expression}");
    }
    assert!(parses("{\nlet cleanup_action = 42\ncleanup_action\n}"));
}

fn nested_body(count: usize) -> String {
    format!(
        "{}42{}",
        "cleanup action {\n".repeat(count),
        "\n}".repeat(count)
    )
}

fn nested_action(count: usize) -> String {
    format!(
        "{}action{}",
        "cleanup ".repeat(count),
        " {\n42\n}".repeat(count)
    )
}

#[test]
fn body_and_action_depth_limits_are_exact_with_fresh_retries() {
    for (at_limit, beyond_limit) in [
        (
            nested_body(STRUCTURAL_DEPTH_LIMIT / 2),
            nested_body(STRUCTURAL_DEPTH_LIMIT / 2 + 1),
        ),
        (
            nested_action(STRUCTURAL_DEPTH_LIMIT - 1),
            nested_action(STRUCTURAL_DEPTH_LIMIT),
        ),
    ] {
        assert!(parses(&at_limit));
        let source = source(&beyond_limit);
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
fn iterative_projection_and_bounded_disposal_fit_the_predecessor_small_stack() {
    for (expression, expected_scopes) in [
        (
            nested_body(STRUCTURAL_DEPTH_LIMIT / 2),
            STRUCTURAL_DEPTH_LIMIT / 2,
        ),
        (
            nested_action(STRUCTURAL_DEPTH_LIMIT - 1),
            STRUCTURAL_DEPTH_LIMIT - 1,
        ),
    ] {
        let source = source(&expression);
        let tree = parse(lex(&source).unwrap());
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let mut pending = vec![tree.root().unwrap()];
                let mut scopes = 0;
                while let Some(node) = pending.pop() {
                    scopes += usize::from(node.kind == NodeKind::CleanupExpression);
                    for child in &node.children {
                        if let ConcreteElement::Node(child) = child {
                            pending.push(child);
                        }
                    }
                }
                assert_eq!(scopes, expected_scopes);
                drop(project_module(&source, &tree).unwrap());
                drop(tree);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
