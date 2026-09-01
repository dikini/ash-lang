use ash::{
    lexer::lex,
    parser::{Event, ProjectionError, parse, project_module},
    source::SourceFile,
    surface::{SurfaceDefinitionKind, SurfaceExprKind, SurfaceKindKind, SurfaceTypeKind},
};

fn project(text: &str) -> ash::surface::SurfaceModule {
    let source =
        SourceFile::new("effects-syntax.ash", text).expect("the effect syntax fixture should fit");
    let lexed = lex(&source).expect("the effect syntax fixture should lex");
    assert!(lexed.diagnostics.is_empty(), "{:?}", lexed.diagnostics);
    let tree = parse(lexed);
    assert!(
        tree.parse_diagnostics().is_empty(),
        "unexpected parse diagnostics: {:?}",
        tree.parse_diagnostics()
    );
    project_module(&source, &tree).expect("valid effect syntax should project")
}

#[test]
fn malformed_effect_syntax_remains_token_complete_and_cannot_project() {
    let source = SourceFile::new(
        "malformed-effect.ash",
        "effect Broken {\nrequest Int -> Unit\n}\n",
    )
    .expect("the malformed fixture should fit");
    let tree = parse(lex(&source).expect("the malformed fixture should lex"));
    assert!(!tree.parse_diagnostics().is_empty());
    let consumed = tree
        .events()
        .iter()
        .filter_map(|event| match event {
            Event::Token(index) => Some(*index),
            Event::Start(_) | Event::Finish | Event::Error(_) | Event::Missing { .. } => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(consumed, (0..tree.tokens().len()).collect::<Vec<_>>());
    assert_eq!(
        project_module(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
}

#[test]
fn effect_declaration_and_computation_rows_project_explicitly() {
    let module = project(concat!(
        "pub effect Exchange<A : Type> {\n",
        "send : A -> Unit\n",
        "receive : Unit -> A\n",
        "}\n\n",
        "relay<R : EffectRow> : (Unit -> Int ! {Exchange<Int> | R}) -> Int ! {Exchange<Int> | R}\n",
        "relay action = action ()\n",
    ));

    let [effect] = module.effects.as_slice() else {
        panic!("one effect declaration should project")
    };
    assert!(effect.public);
    assert_eq!(effect.name.text, "Exchange");
    assert_eq!(effect.operations.len(), 2);
    assert_eq!(effect.operations[0].name.text, "send");
    assert_eq!(effect.operations[1].name.text, "receive");

    let SurfaceDefinitionKind::Equational(relay) = &module.definitions[0].kind else {
        panic!("relay should remain equational")
    };
    assert!(matches!(
        relay.interface.type_parameters.as_ref().unwrap()[0]
            .kind
            .as_ref()
            .unwrap()
            .kind,
        SurfaceKindKind::EffectRow
    ));
    let SurfaceTypeKind::Function(outer) = &relay.interface.annotation.kind else {
        panic!("relay should project its outer arrow")
    };
    let SurfaceTypeKind::Function(action) = &outer.domain.kind else {
        panic!("the grouped action should project as a function")
    };
    let action_row = action.effects.as_ref().expect("the action row is explicit");
    assert_eq!(action_row.effects[0].effect.member().text, "Exchange");
    assert_eq!(action_row.tail.as_ref().unwrap().text, "R");
    let result_row = outer.effects.as_ref().expect("the result row is explicit");
    assert_eq!(result_row.effects[0].arguments.len(), 1);
    assert_eq!(result_row.tail.as_ref().unwrap().text, "R");
}

#[test]
fn perform_handle_and_resume_project_with_their_stated_precedence() {
    let module = project(concat!(
        "effect Cell {\n",
        "read : Unit -> Int\n",
        "write : Int -> Unit\n",
        "}\n\n",
        "main : Unit -> Int\n",
        "main () = handle (perform Cell.read ()) with Cell {\n",
        "read ignored => resume 40 + 2\n",
        "write value => resume ()\n",
        "}\n",
    ));
    let SurfaceDefinitionKind::Equational(main) = &module.definitions[0].kind else {
        panic!("main should remain equational")
    };
    let body = &main.equations[0].body;
    let SurfaceExprKind::Handle(handler) = &body.kind else {
        panic!("main should project an explicit handler")
    };
    assert_eq!(handler.effect.effect.member().text, "Cell");
    assert_eq!(handler.clauses.len(), 2);
    assert!(matches!(handler.body.kind, SurfaceExprKind::Perform(_)));
    let SurfaceExprKind::Resume(resumed) = &handler.clauses[0].body.kind else {
        panic!("the first clause should project resume")
    };
    assert!(matches!(resumed.kind, SurfaceExprKind::Add(_)));
}
