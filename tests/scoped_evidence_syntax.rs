use ash::{
    lexer::lex,
    parser::{ConcreteTree, Event, ProjectionError, parse, project_module},
    source::SourceFile,
    surface::{SurfaceDefinitionKind, SurfaceExprKind, SurfaceLocalDeclaration},
};

fn parse_source(text: &str) -> (SourceFile, ConcreteTree) {
    let source = SourceFile::new("scoped-evidence-syntax.ash", text)
        .expect("scoped evidence syntax source should fit");
    let lexed = lex(&source).expect("scoped evidence syntax should lex");
    assert!(lexed.diagnostics.is_empty(), "{:?}", lexed.diagnostics);
    let tree = parse(lexed);
    assert_eq!(tree.resource_failure(), None);
    assert!(
        tree.root().is_some(),
        "parsing should retain a concrete root"
    );
    let consumed = tree
        .events()
        .iter()
        .filter_map(|event| match event {
            Event::Token(index) => Some(*index),
            Event::Start(_) | Event::Finish | Event::Missing { .. } | Event::Error(_) => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(consumed, (0..tree.tokens().len()).collect::<Vec<_>>());
    (source, tree)
}

fn assert_syntax_rejection(text: &str) {
    let (source, tree) = parse_source(text);
    assert!(
        !tree.parse_diagnostics().is_empty(),
        "excluded syntax must produce a parser-owned diagnostic"
    );
    assert_eq!(
        project_module(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent),
        "parser recovery must prevent semantic projection"
    );
}

#[test]
fn sequential_evidence_projects_between_preceding_and_following_bindings() {
    let (source, tree) = parse_source(
        r#"interface Read<A> {
    read : A -> Int
}
main : Unit -> Int
main () = {
    newtype Token = Token(Int)
    let saved = Token(41)
    with Read<Token> {
        read (Token(value)) = value + 1
    }
    let answer = read(saved)
    answer
}
"#,
    );
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).expect("sequential evidence should project");
    assert!(module.implementations.is_empty());
    let SurfaceDefinitionKind::Equational(main) = &module.definitions[0].kind else {
        panic!("main should remain equational")
    };
    let SurfaceExprKind::Block(block) = &main.equations[0].body.kind else {
        panic!("main should retain its sequential block")
    };
    let [
        SurfaceLocalDeclaration::Newtype(_),
        SurfaceLocalDeclaration::Binding(_),
        SurfaceLocalDeclaration::Evidence(evidence),
        SurfaceLocalDeclaration::Binding(_),
    ] = block.declarations.as_slice()
    else {
        panic!("evidence must retain its exact sequential declaration position")
    };
    assert_eq!(evidence.application.interface.member().text, "Read");
    assert_eq!(evidence.application.arguments.len(), 1);
    let [equation] = evidence.equations.as_slice() else {
        panic!("one supplied equation should project")
    };
    assert_eq!(equation.name.text, "read");
    assert_eq!(equation.patterns.len(), 1);
    let SurfaceExprKind::Name(result) = &block.result.kind else {
        panic!("the following result must remain separate from the evidence declaration")
    };
    assert_eq!(result.member().text, "answer");
}

#[test]
fn evidence_is_not_a_module_declaration() {
    assert_syntax_rejection("with Read<Int> {\n    read value = value\n}\n");
}

#[test]
fn evidence_has_no_visibility_modifier() {
    assert_syntax_rejection(
        "main : Unit -> Int\nmain () = {\n    pub with Read<Int> {\n        read value = value\n    }\n    42\n}\n",
    );
}

#[test]
fn evidence_has_no_head_parameter_list() {
    assert_syntax_rejection(
        "main : Unit -> Int\nmain () = {\n    with<A> Read<A> {\n        read ignored = 42\n    }\n    42\n}\n",
    );
}

#[test]
fn evidence_has_no_prerequisite_clause() {
    assert_syntax_rejection(
        "main : Unit -> Int\nmain () = {\n    with Read<Int> where Read<Int> {\n        read value = value\n    }\n    42\n}\n",
    );
}

#[test]
fn evidence_cannot_occupy_a_recursive_group_member() {
    assert_syntax_rejection(
        "main : Unit -> Int\nmain () = {\n    let rec first : Unit -> Int = fn(ignored) {\n        42\n    }\n    and with Read<Int> {\n        read value = value\n    }\n    first()\n}\n",
    );
}
