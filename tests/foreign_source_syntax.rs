use ash::{
    lexer::lex,
    parser::{parse, project_module},
    source::SourceFile,
    surface::{SurfaceDeclarationIndex, SurfaceForeignMember, SurfaceTypeKind},
};

const POINTERS: &str = r#"import @builtin.foreign as F
pub foreign library Native {
    profile "x86_64-unknown-linux-gnu"
    symbol Echo : F.Address -> F.Address { name "echo" }
    symbol Mixed : (F.Address, Bytes) -> Unit { name "mixed" }
}
main : Unit -> Int
main () = 42
"#;

#[test]
fn foreign_pointer_library_parses_and_projects_with_ordinary_declarations() {
    for text in [
        POINTERS.to_owned(),
        POINTERS.replace("pub foreign", "foreign"),
    ] {
        let source = SourceFile::new("pointers.ash", text).unwrap();
        let tree = parse(lex(&source).unwrap());
        assert!(
            tree.lexical_diagnostics().is_empty(),
            "{:?}",
            tree.lexical_diagnostics()
        );
        assert!(
            tree.parse_diagnostics().is_empty(),
            "{:?}",
            tree.parse_diagnostics()
        );
        assert!(project_module(&source, &tree).is_ok());
    }
}

#[test]
fn projected_library_retains_member_order_type_structure_and_source_spans() {
    let source = SourceFile::new("ordered.ash", POINTERS).unwrap();
    let tree = parse(lex(&source).unwrap());
    let module = project_module(&source, &tree).unwrap();
    assert_eq!(
        module.declaration_order,
        vec![
            SurfaceDeclarationIndex::ForeignLibrary(0),
            SurfaceDeclarationIndex::Global(0)
        ]
    );
    let library = &module.foreign_libraries[0];
    assert!(library.public);
    assert_eq!(library.name.text, "Native");
    let [
        SurfaceForeignMember::Profile(profile),
        SurfaceForeignMember::Symbol(echo),
        SurfaceForeignMember::Symbol(mixed),
    ] = library.members.as_slice()
    else {
        panic!("profile and symbols must retain authored order");
    };
    assert_eq!(profile.target.value, "x86_64-unknown-linux-gnu");
    assert_eq!(
        (echo.name.text.as_str(), echo.native_name.value.as_str()),
        ("Echo", "echo")
    );
    assert_eq!(
        (mixed.name.text.as_str(), mixed.native_name.value.as_str()),
        ("Mixed", "mixed")
    );
    let SurfaceTypeKind::Function(function) = &mixed.ty.kind else {
        panic!("signature is a function")
    };
    let SurfaceTypeKind::Tuple(fields) = &function.domain.kind else {
        panic!("flat pointer arguments retain tuple structure")
    };
    assert_eq!(fields.len(), 2);
    assert!(matches!(&fields[0].kind, SurfaceTypeKind::Named(_)));
    assert!(matches!(&fields[1].kind, SurfaceTypeKind::Bytes));
    assert!(matches!(&function.codomain.kind, SurfaceTypeKind::Unit));
    for (span, expected) in [
        (library.name.span, "Native"),
        (profile.target.span, "\"x86_64-unknown-linux-gnu\""),
        (echo.name.span, "Echo"),
        (echo.ty.span, "F.Address -> F.Address"),
        (echo.native_name.span, "\"echo\""),
        (mixed.ty.span, "(F.Address, Bytes) -> Unit"),
        (fields[0].span, "F.Address"),
        (fields[1].span, "Bytes"),
    ] {
        assert_eq!(span.source(), source.id());
        let range = span.range();
        assert_eq!(
            &source.text()[range.start() as usize..range.end() as usize],
            expected
        );
    }
    for span in [library.span, profile.span, echo.span, mixed.span] {
        assert_eq!(span.source(), source.id());
        assert!(span.range().end() > span.range().start());
    }
}

#[test]
fn malformed_signature_and_link_name_syntax_cannot_project() {
    for text in [
        POINTERS.replace("Echo :", "Echo"),
        POINTERS.replace("Echo : F.Address -> F.Address", "Echo :"),
        POINTERS.replace("name \"echo\"", "\"echo\""),
        POINTERS.replace("name \"echo\"", "name"),
    ] {
        let source = SourceFile::new("bad-foreign.ash", text).unwrap();
        let tree = parse(lex(&source).unwrap());
        assert!(project_module(&source, &tree).is_err(), "{}", source.text());
    }
}

#[test]
fn zero_argument_void_call_and_adjacent_final_braces_parse() {
    let text = "foreign library Empty {\n    profile \"x86_64-unknown-linux-gnu\"\n    symbol Stop : Unit -> Unit { name \"stop\"}}\n";
    let source = SourceFile::new("zero-arguments.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    assert!(project_module(&source, &tree).is_ok());
}

#[test]
fn foreign_libraries_retain_interleaved_ordinary_declaration_order() {
    let text = "effect Before {\n    request : Unit -> Unit\n}\nforeign library First {\n    profile \"x86_64-unknown-linux-gnu\"\n    symbol Stop : Unit -> Unit { name \"stop\" }\n}\neffect After {\n    request : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = 42\n";
    let source = SourceFile::new("interleaved.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    let module = project_module(&source, &tree).unwrap();
    assert_eq!(
        module.declaration_order,
        vec![
            SurfaceDeclarationIndex::Effect(0),
            SurfaceDeclarationIndex::ForeignLibrary(0),
            SurfaceDeclarationIndex::Effect(1),
            SurfaceDeclarationIndex::Global(0)
        ]
    );
}

#[test]
fn foreign_words_remain_ordinary_identifiers_outside_declarations() {
    let text = "foreign : Int -> Int\nforeign library = library\nprofile : Unit -> Int\nprofile () = foreign(42)\n";
    let source = SourceFile::new("contextual.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(project_module(&source, &tree).is_ok());
}

#[test]
fn foreign_declaration_does_not_admit_negative_ordinary_expressions() {
    let source = SourceFile::new(
        "ordinary-negative.ash",
        "main : Unit -> Int\nmain () = -1\n",
    )
    .unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(project_module(&source, &tree).is_err());
}

#[test]
fn checked_remains_an_ordinary_identifier_outside_library_prefixes() {
    let source = SourceFile::new(
        "checked-name.ash",
        "checked : Int -> Int\nchecked value = value\nmain : Unit -> Int\nmain () = checked(42)\n",
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
