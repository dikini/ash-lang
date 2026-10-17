use ash::{
    lexer::lex,
    parser::{parse, project_module},
    source::SourceFile,
};

const DEFINITION: &str = "pub resource Connection<R> {\ninput OpenConfig\nstate Native.ConnectionState<R>\nresult Provider.Scope<OpenError, CloseError, T> for <T>\nprovider ConnectionProvider<R>\neffect ConnectionOps<R>\ninterpret Native.Connection<R>\nacquire config => perform Native.Connection<R>.open config\nfinish state => perform Native.Connection<R>.close state\nhandlers state {\ndiagnostic db => resume (perform Native.Connection<R>.diagnostic state)\n}\n}\n";

const TYPED_ARENA: &str = include_str!("fixtures/provider-experiments/arena-typed/arena.ash");

const FAMILY: &str = "family<T> where Native.Layout<T> {\nprovider StorageProvider<R, T>\neffect StorageOps<R, T>\ninterpret Native.Storage<R, T>\nhandlers state {\nallocate operand => resume operand\nload operand => resume operand\n}\n}\n";

fn definition_with_family(family: &str) -> String {
    DEFINITION.replacen("acquire config", &format!("{family}acquire config"), 1)
}

#[test]
fn provider_declaration_reuses_type_effect_and_handler_syntax() {
    let source = SourceFile::new("provider.ash", DEFINITION).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).unwrap();
    assert!(module.resources[0].family.is_none());
}

#[test]
fn resource_type_instance_can_appear_in_nested_expression_positions() {
    let source = SourceFile::new("client.ash", "main : Unit -> Int\nmain () = resource Sqlite.Connection<C> db = config {\nresource Sqlite.Statement<S> stmt = (db, sql) {\n42\n}\n}\n").unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    assert!(project_module(&source, &tree).is_ok());
}

#[test]
fn missing_and_duplicate_provider_fields_are_rejected() {
    for source_text in [
        DEFINITION.replace("input OpenConfig\n", ""),
        DEFINITION.replace("input OpenConfig\n", "input OpenConfig\ninput OpenConfig\n"),
    ] {
        let source = SourceFile::new("bad-provider.ash", source_text).unwrap();
        let tree = parse(lex(&source).unwrap());
        assert!(!tree.parse_diagnostics().is_empty());
        assert!(project_module(&source, &tree).is_err());
    }
}

#[test]
fn resource_instances_parse_complete_written_arguments_before_definition_selection() {
    for arguments in ["", "C,", "{| Delta},"] {
        let source = SourceFile::new("bad-instance.ash", format!("main : Unit -> Int\nmain () = resource Lib.Connection<{arguments}> db = 0 {{\n    42\n}}\n")).unwrap();
        let tree = parse(lex(&source).unwrap());
        assert!(!tree.parse_diagnostics().is_empty(), "{arguments}");
        assert!(project_module(&source, &tree).is_err());
    }
    for arguments in [
        "C, D",
        "C, Int, { | Delta }",
        "Int",
        "C -> C",
        "{| Delta}, C",
    ] {
        let source = SourceFile::new(
            "retained-instance.ash",
            format!("main : Unit -> Int\nmain () = resource Lib.Connection<{arguments}> db = 0 {{\n    42\n}}\n"),
        ).unwrap();
        let tree = parse(lex(&source).unwrap());
        assert!(
            tree.parse_diagnostics().is_empty(),
            "{arguments}: {:?}",
            tree.parse_diagnostics()
        );
        assert!(project_module(&source, &tree).is_ok());
    }
}

#[test]
fn declaration_requires_one_answer_parameter_and_nonempty_handlers() {
    for text in [
        DEFINITION.replace("for <T>", "for <T, U>"),
        DEFINITION.replace(
            "diagnostic db => resume (perform Native.Connection<R>.diagnostic state)\n",
            "",
        ),
    ] {
        let source = SourceFile::new("bad-declaration.ash", text).unwrap();
        let tree = parse(lex(&source).unwrap());
        assert!(!tree.parse_diagnostics().is_empty());
        assert!(project_module(&source, &tree).is_err());
    }
}

#[test]
fn final_handler_and_declaration_braces_can_share_a_line() {
    let text = DEFINITION.replace("\n}\n}\n", "\n}}\n");
    let source = SourceFile::new("adjacent-braces.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    assert!(project_module(&source, &tree).is_ok());
}

#[test]
fn selected_typed_arena_module_parses_resource_family_templates() {
    let source = SourceFile::new("arena-typed/arena.ash", TYPED_ARENA).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).unwrap();
    let resource = &module.resources[0];
    let family = resource
        .family
        .as_ref()
        .expect("the family must survive projection");
    assert_eq!(family.parameter.name.text, "Payload");
    assert_eq!(resource.answer.name.text, "T");
    assert_ne!(family.parameter.name.span, resource.answer.name.span);
    let [requirement] = family.requirements.as_slice() else {
        panic!("the written layout requirement must survive projection");
    };
    assert_eq!(requirement.interface.member().text, "Layout");
    assert_eq!(requirement.interface.qualifier().unwrap().text, "Native");
    assert_eq!(family.provider.interface.member().text, "StorageProvider");
    assert_eq!(family.provided.effect.member().text, "StorageOps");
    assert_eq!(family.interpreted.effect.member().text, "Storage");
    assert_eq!(family.handlers_binder.text, "state");
    assert_eq!(
        family
            .handlers
            .iter()
            .map(|clause| clause.operation.text.as_str())
            .collect::<Vec<_>>(),
        ["allocate_checked", "load_checked"]
    );
    assert_eq!(family.span.source(), source.id());
    assert!(resource.span.range().start() < family.span.range().start());
    assert!(family.span.range().end() < resource.acquire.span.range().start());
}

#[test]
fn family_handlers_and_resource_declaration_accept_adjacent_closing_braces() {
    let family = FAMILY.replace("\n}\n}\n", "\n}}\n");
    let text = definition_with_family(&family).replace("\n}\n}\n", "\n}}\n");
    let source = SourceFile::new("adjacent-family-braces.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    assert!(project_module(&source, &tree).is_ok());
}

#[test]
fn resource_family_templates_require_a_requirement_one_payload_and_complete_group() {
    for (case, family) in [
        ("second family block", FAMILY.repeat(2)),
        (
            "missing requirement",
            FAMILY.replace(" where Native.Layout<T>", ""),
        ),
        (
            "multiple payloads",
            FAMILY.replace("family<T>", "family<T, U>"),
        ),
        (
            "missing provider",
            FAMILY.replace("provider StorageProvider<R, T>\n", ""),
        ),
        (
            "missing effect",
            FAMILY.replace("effect StorageOps<R, T>\n", ""),
        ),
        (
            "missing interpretation",
            FAMILY.replace("interpret Native.Storage<R, T>\n", ""),
        ),
        (
            "empty handlers",
            FAMILY.replace(
                "allocate operand => resume operand\nload operand => resume operand\n",
                "",
            ),
        ),
    ] {
        let source = SourceFile::new(case, definition_with_family(&family)).unwrap();
        let tree = parse(lex(&source).unwrap());
        assert!(!tree.parse_diagnostics().is_empty(), "{case}");
        assert!(project_module(&source, &tree).is_err(), "{case}");
    }
}
