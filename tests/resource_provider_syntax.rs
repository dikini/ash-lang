use ash::{
    lexer::lex,
    parser::{parse, project_module},
    source::SourceFile,
};

const DEFINITION: &str = "pub resource Connection<R> {\ninput OpenConfig\nstate Native.ConnectionState<R>\nresult Provider.Scope<OpenError, CloseError, T> for <T>\nprovider ConnectionProvider<R>\neffect ConnectionOps<R>\ninterpret Native.Connection<R>\nacquire config => perform Native.Connection<R>.open config\nfinish state => perform Native.Connection<R>.close state\nhandlers state {\ndiagnostic db => resume (perform Native.Connection<R>.diagnostic state)\n}\n}\n";

#[test]
fn provider_declaration_reuses_type_effect_and_handler_syntax() {
    let source = SourceFile::new("provider.ash", DEFINITION).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    assert!(project_module(&source, &tree).is_ok());
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
fn provider_instances_require_one_fresh_uppercase_identity_binder() {
    for arguments in ["Int", "C, D", "C -> C"] {
        let source = SourceFile::new("bad-instance.ash", format!("main : Unit -> Int\nmain () = resource Lib.Connection<{arguments}> db = 0 {{\n42\n}}\n")).unwrap();
        let tree = parse(lex(&source).unwrap());
        assert!(!tree.parse_diagnostics().is_empty(), "{arguments}");
        assert!(project_module(&source, &tree).is_err());
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
