use ash::{
    lexer::lex,
    parser::{Event, ProjectionError, parse, project_module},
    source::SourceFile,
    surface::{
        SurfaceDefinitionKind, SurfaceExprKind, SurfaceLocalDeclaration,
        SurfaceNominalDeclarationKind, SurfaceTypeKind, SurfaceTypeVisibility,
    },
};

fn project(text: &str) -> ash::surface::SurfaceModule {
    let source = SourceFile::new("local-newtypes-syntax.ash", text)
        .expect("the local newtype fixture should fit");
    let lexed = lex(&source).expect("the local newtype fixture should lex");
    assert!(lexed.diagnostics.is_empty(), "{:?}", lexed.diagnostics);
    let tree = parse(lexed);
    assert!(
        tree.parse_diagnostics().is_empty(),
        "unexpected parse diagnostics: {:?}",
        tree.parse_diagnostics()
    );
    project_module(&source, &tree).expect("valid local newtype syntax should project")
}

fn parse_tree(text: &str) -> (SourceFile, ash::parser::ConcreteTree) {
    let source = SourceFile::new("local-newtypes-syntax.ash", text)
        .expect("the local newtype fixture should fit");
    let tree = parse(lex(&source).expect("the local newtype fixture should lex"));
    (source, tree)
}

fn assert_token_complete(tree: &ash::parser::ConcreteTree) {
    let consumed = tree
        .events()
        .iter()
        .filter_map(|event| match event {
            Event::Token(index) => Some(*index),
            Event::Start(_) | Event::Finish | Event::Error(_) | Event::Missing { .. } => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(consumed, (0..tree.tokens().len()).collect::<Vec<_>>());
}

#[test]
fn local_newtype_projects_as_a_private_sequential_declaration() {
    let text = concat!(
        "main : Unit -> Int\n",
        "main () = {\n",
        "    newtype Offset = Offset(Int)\n",
        "    let value = Offset(42)\n",
        "    match value {\n",
        "        Offset(inner) => inner\n",
        "    }\n",
        "}\n",
    );
    let module = project(text);

    let SurfaceDefinitionKind::Equational(main) = &module.definitions[0].kind else {
        panic!("main should remain an equational definition")
    };
    let SurfaceExprKind::Block(block) = &main.equations[0].body.kind else {
        panic!("main should retain its block")
    };
    let [
        SurfaceLocalDeclaration::Newtype(newtype),
        SurfaceLocalDeclaration::Binding(_),
    ] = block.declarations.as_slice()
    else {
        panic!("the local newtype should precede the binding")
    };

    assert_eq!(
        newtype.declaration_kind,
        SurfaceNominalDeclarationKind::Newtype
    );
    assert_eq!(newtype.visibility, SurfaceTypeVisibility::Private);
    assert_eq!(newtype.name.text, "Offset");
    assert!(newtype.parameters.is_empty());
    assert_eq!(newtype.constructors.len(), 1);
    let constructor = &newtype.constructors[0];
    assert_eq!(constructor.name.text, "Offset");
    assert_eq!(constructor.fields.len(), 1);
    assert!(matches!(constructor.fields[0].kind, SurfaceTypeKind::Int));
    assert_eq!(
        newtype.span.range().start(),
        text.find("newtype").unwrap() as u32
    );
    assert_eq!(
        newtype.span.range().end(),
        (text.find("Offset(Int)").unwrap() + "Offset(Int)".len()) as u32
    );
}

#[test]
fn parameterized_local_newtype_precedes_following_binding() {
    let module = project(concat!(
        "main : Unit -> Int\n",
        "main () = {\n",
        "    newtype Box<A> = Box(A)\n",
        "    let result = 1\n",
        "    result\n",
        "}\n",
    ));

    let SurfaceDefinitionKind::Equational(main) = &module.definitions[0].kind else {
        panic!("main should remain an equational definition")
    };
    let SurfaceExprKind::Block(block) = &main.equations[0].body.kind else {
        panic!("main should retain its block")
    };
    let [
        SurfaceLocalDeclaration::Newtype(newtype),
        SurfaceLocalDeclaration::Binding(_),
    ] = block.declarations.as_slice()
    else {
        panic!("the parameterized declaration should precede the binding")
    };
    assert_eq!(newtype.parameters.len(), 1);
    assert_eq!(newtype.parameters[0].name.text, "A");
    assert!(newtype.parameters[0].kind.is_none());
    assert_eq!(newtype.constructors[0].fields.len(), 1);
}

#[test]
fn malformed_local_newtype_shape_recovers_without_losing_tokens() {
    let (source, tree) = parse_tree(concat!(
        "main : Unit -> Int\n",
        "main () = {\n",
        "    newtype Broken = Broken(Int, Bool)\n",
        "    let following = 1\n",
        "    following\n",
        "}\n",
    ));

    assert!(!tree.parse_diagnostics().is_empty());
    assert_token_complete(&tree);
    assert_eq!(
        project_module(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
}

#[test]
fn visibility_modifiers_remain_rejected_in_block_position() {
    for text in [
        concat!(
            "main : Unit -> Int\n",
            "main () = {\n",
            "    opaque newtype Hidden = Hidden(Int)\n",
            "    1\n",
            "}\n",
        ),
        concat!(
            "main : Unit -> Int\n",
            "main () = {\n",
            "    pub newtype Hidden = Hidden(Int)\n",
            "    1\n",
            "}\n",
        ),
        concat!(
            "main : Unit -> Int\n",
            "main () = {\n",
            "    pub opaque newtype Hidden = Hidden(Int)\n",
            "    1\n",
            "}\n",
        ),
    ] {
        let (source, tree) = parse_tree(text);
        assert!(!tree.parse_diagnostics().is_empty());
        assert_token_complete(&tree);
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::RecoveryNodesPresent)
        );
    }
}
