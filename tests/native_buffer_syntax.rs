use ash::{
    lexer::lex,
    parser::{parse, project_module},
    source::SourceFile,
};

fn parses(expression: &str) -> bool {
    let source = SourceFile::new(
        "native-buffer-syntax.ash",
        format!("main : Unit -> Int\nmain () = {expression}\n"),
    )
    .unwrap();
    let tree = parse(lex(&source).unwrap());
    tree.lexical_diagnostics().is_empty()
        && tree.parse_diagnostics().is_empty()
        && project_module(&source, &tree).is_ok()
}

#[test]
fn native_buffer_acquisition_uses_the_existing_resource_shape() {
    for expression in [
        "resource Buffer.Buffer<R> b = 4 {\n42\n}",
        "resource Buffer.Buffer<R> b = (2 + 2) {\nb\n}",
        "resource Buffer.Buffer<R> b = 4 {\nresource cell<S> c = 42 {\nc\n}\n}",
    ] {
        assert!(parses(expression), "{expression}");
    }
}

#[test]
fn native_buffer_remains_contextual_and_cell_is_unchanged() {
    assert!(parses("{\nlet native_buffer = 42\nnative_buffer\n}"));
    assert!(parses("resource cell<R> c = 42 {\nc\n}"));
}

#[test]
fn projection_retains_cell_and_named_generic_cell_carriers() {
    use ash::surface::{SurfaceDefinitionKind, SurfaceExprKind, SurfaceResourceKind};

    for (designator, arguments) in [("cell", "R"), ("Cell.Cell", "R, Int")] {
        let source = SourceFile::new(
            "resource-kind.ash",
            format!("main : Unit -> Int\nmain () = resource {designator}<{arguments}> b = 4 {{\n42\n}}\n"),
        )
        .unwrap();
        let tree = parse(lex(&source).unwrap());
        let module = project_module(&source, &tree).unwrap();
        let SurfaceDefinitionKind::Equational(main) = &module.definitions[0].kind else {
            panic!("expected main equation")
        };
        match &main.equations[0].body.kind {
            SurfaceExprKind::Resource(resource) if designator == "cell" => {
                assert_eq!(resource.kind, SurfaceResourceKind::Cell);
                assert!(
                    resource.initializer.span.range().end() < resource.body.span.range().start()
                );
            }
            SurfaceExprKind::ProviderResource(resource) if designator == "Cell.Cell" => {
                assert!(
                    resource.initializer.span.range().end() < resource.body.span.range().start()
                );
            }
            _ => panic!("expected the exact integer/generic cell carrier"),
        }
    }
}

#[test]
fn malformed_native_buffer_acquisitions_reject() {
    for expression in [
        "resource Buffer.Buffer<r> b = 4 {\n42\n}",
        "resource Buffer.Buffer<R> _ = 4 {\n42\n}",
        "resource Buffer.Buffer<R> b = 2 + 2 {\n42\n}",
        "resource Buffer.Buffer<R> b = 4 42",
        "resource native_buffer<R> b = 4 {\n42\n}",
    ] {
        assert!(!parses(expression), "{expression}");
    }
}
