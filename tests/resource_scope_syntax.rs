use ash::{
    lexer::lex,
    parser::{parse, project_module},
    source::SourceFile,
};

fn parses(expression: &str) -> bool {
    let source = SourceFile::new(
        "resource-syntax.ash",
        format!("main : Unit -> Int\nmain () = {expression}\n"),
    )
    .unwrap();
    let tree = parse(lex(&source).unwrap());
    tree.lexical_diagnostics().is_empty()
        && tree.parse_diagnostics().is_empty()
        && project_module(&source, &tree).is_ok()
}

#[test]
fn acquisition_is_an_expression_with_a_primary_initializer_and_block_body() {
    for expression in [
        "resource cell<R> c = 41 {\nc\n}",
        "resource cell<R> c = (40 + 1) {\nc\n}",
        "resource cell<R> c = (resource cell<S> d = 41 {\n42\n}) {\nc\n}",
        "(resource cell<R> c = 41 {\n42\n}) + 1",
    ] {
        assert!(parses(expression), "{expression}");
    }
}

#[test]
fn malformed_acquisitions_reject_and_cell_remains_contextual() {
    for expression in [
        "resource other<R> c = 41 {\nc\n}",
        "resource cell<r> c = 41 {\nc\n}",
        "resource cell<R, S> c = 41 {\nc\n}",
        "resource cell<R : Type> c = 41 {\nc\n}",
        "resource cell<R> C = 41 {\n42\n}",
        "resource cell<R> _ = 41 {\n42\n}",
        "resource cell<R> c = 40 + 1 {\nc\n}",
        "resource cell<R> c = f 41 {\nc\n}",
        "resource cell<R> c = 41 42",
        "f resource cell<R> c = 41 {\nc\n}",
    ] {
        assert!(!parses(expression), "{expression}");
    }
    assert!(parses("{\nlet cell = 41\ncell\n}"));
    assert!(!parses("{\nlet resource = 41\nresource\n}"));
}

#[test]
fn projection_keeps_initializer_outside_the_owned_body() {
    use ash::surface::{SurfaceDefinitionKind, SurfaceExprKind};
    let text =
        "main : Unit -> Int\nmain () = resource cell<R> c = (40 + 1) {\nlet saved = c\nsaved\n}\n";
    let source = SourceFile::new("resource-syntax.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    let module = project_module(&source, &tree).unwrap();
    let SurfaceDefinitionKind::Equational(main) = &module.definitions[0].kind else {
        unreachable!()
    };
    let SurfaceExprKind::Resource(resource) = &main.equations[0].body.kind else {
        panic!("acquisition carrier")
    };
    assert_eq!(resource.identity.text, "R");
    assert_eq!(resource.handle.text, "c");
    assert!(matches!(resource.initializer.kind, SurfaceExprKind::Add(_)));
    assert_eq!(resource.body.declarations.len(), 1);
    assert!(resource.initializer.span.range().end() < resource.body.span.range().start());
    assert_eq!(
        resource.body.span.range().end(),
        main.equations[0].body.span.range().end()
    );
}

#[test]
fn deeply_nested_acquisitions_have_a_syntax_owned_limit_and_retry() {
    let mut expression = "42".to_owned();
    for _ in 0..ash::parser::STRUCTURAL_DEPTH_LIMIT + 1 {
        expression = format!("resource cell<R> c = 41 {{\n{expression}\n}}");
    }
    let source = SourceFile::new(
        "deep-resource.ash",
        format!("main : Unit -> Int\nmain () = {expression}\n"),
    )
    .unwrap();
    for _ in 0..2 {
        let tree = parse(lex(&source).unwrap());
        assert!(tree.resource_failure().is_some());
    }
    assert!(parses("resource cell<R> c = 41 {\n42\n}"));
}

#[test]
fn generic_cell_reuses_named_resource_grammar_and_primary_initializer() {
    for expression in [
        "resource Cell.Cell<R, Int> c = 41 {\n42\n}",
        "resource Access<R, (Int -> Int)> c = (make ()) {\n42\n}",
    ] {
        assert!(parses(expression), "{expression}");
    }
    assert!(!parses("resource Cell.Cell<R, Int> c = make () {\n42\n}"));
}
