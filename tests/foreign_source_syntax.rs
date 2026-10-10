use ash::{
    lexer::lex,
    parser::{parse, project_module},
    source::SourceFile,
};

const SCALAR: &str = "pub foreign library Native {\n    profile \"x86_64-unknown-linux-gnu\"\n    repr CInt = signed(32)\n    const Zero : CInt = 0\n    const MinusOne : CInt = -1\n    symbol Abs<A, Delta : EffectRow> : Int -> Foreign.Call<Int> {\n        name \"abs\"\n        abi (CInt) -> CInt\n        operand 0 from 0 scalar\n        output result as scalar\n        outcome otherwise { readable result }\n    }\n}\nmain : Unit -> Int\nmain () = 42\n";

#[test]
fn foreign_scalar_library_parses_and_projects_with_ordinary_declarations() {
    let source = SourceFile::new("scalar.ash", SCALAR).unwrap();
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

const OWNER_ACCESS: &str = "foreign library Memory {\n    profile \"x86_64-unknown-linux-gnu\"\n    repr Size = size_t\n    repr Address = opaque\n    repr ByteAddress = bytes\n    repr Sentinel = function_address\n    sentinel Transient : Sentinel = all_bits_one\n    owner State<R, Outer> {\n        representation Address\n        owned R\n        retains Outer\n        teardown Free\n    }\n    access View<W, R> {\n        window W\n        owner State<R, Unit>\n        extent bytes\n        preserves Query, Length\n    }\n    symbol Allocate<R> : Int -> Foreign.Call<Int> {\n        name \"calloc\"\n        abi (Size, Size, out(pointer(Address))) -> pointer(Address)\n        operand 0 from 0 scalar\n        operand 1 from constant One\n        output 2 as owner(State<R, Unit>)\n        output result as view(View<W, R>, 0, 1.0)\n        outcome result nonnull and 2 nonnull { readable result, readable 2, initialized_bytes 2 from 0 }\n        outcome otherwise { unreadable result, unreadable 2 }\n    }\n    symbol Free<R> : State<R, Unit> -> Unit {\n        name \"free\"\n        abi (pointer(Address)) -> void\n        operand 0 from 0 current\n        outcome otherwise { consumed 0 }\n        retained_dependents block\n    }\n}\n";

#[test]
fn owner_access_symbols_and_outcomes_parse_through_shared_type_grammar() {
    let source = SourceFile::new("memory.ash", OWNER_ACCESS).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).unwrap();
    use ash::surface::{
        SurfaceForeignContract, SurfaceForeignMember, SurfaceForeignOutputRoleKind,
    };
    let allocate = module.foreign_libraries[0]
        .members
        .iter()
        .find_map(|member| match member {
            SurfaceForeignMember::Symbol(symbol) if symbol.name.text == "Allocate" => Some(symbol),
            _ => None,
        })
        .unwrap();
    assert!(allocate.abi_operands[2].output);
    let SurfaceForeignContract::Output { role, .. } = &allocate.contracts[3] else {
        panic!("view output role lost");
    };
    let SurfaceForeignOutputRoleKind::View { keys, .. } = &role.kind else {
        panic!("view keys lost");
    };
    assert_eq!(
        keys[1]
            .components
            .iter()
            .map(|part| part.magnitude.to_string())
            .collect::<Vec<_>>(),
        vec!["1", "0"]
    );
    let range = keys[1].span.range();
    assert_eq!(
        &source.text()[range.start() as usize..range.end() as usize],
        "1.0"
    );
}

#[test]
fn malformed_foreign_contract_syntax_cannot_project() {
    for text in [
        SCALAR.replace("operand 0 from 0 scalar", "operand 0 0 scalar"),
        SCALAR.replace("abi (CInt)", "abi (out())"),
        OWNER_ACCESS.replace("representation Address\n", ""),
        OWNER_ACCESS.replace("preserves Query, Length", "preserves"),
        OWNER_ACCESS.replace("owner State<R, Outer>", "owner State"),
        OWNER_ACCESS.replace("access View<W, R>", "access View"),
        OWNER_ACCESS.replace("out(pointer(Address))", "out(pointer(pointer(Address)))"),
        OWNER_ACCESS.replace("initialized_bytes 2 from 0", "initialized_bytes 2"),
    ] {
        let source = SourceFile::new("bad-foreign.ash", text).unwrap();
        let tree = parse(lex(&source).unwrap());
        assert!(project_module(&source, &tree).is_err(), "{}", source.text());
    }
}

#[test]
fn foreign_words_remain_ordinary_identifiers_outside_declarations() {
    let text = "foreign : Int -> Int\nforeign library = library\nprofile : Unit -> Int\nprofile () = foreign(42)\n";
    let source = SourceFile::new("contextual.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(project_module(&source, &tree).is_ok());
}

#[test]
fn projected_contract_retains_member_order_kinds_positions_and_spans() {
    use ash::surface::{
        SurfaceDeclarationIndex, SurfaceForeignContract, SurfaceForeignMember,
        SurfaceForeignNativePosition, SurfaceForeignOperandSource, SurfaceKindKind,
    };
    let source = SourceFile::new("ordered.ash", SCALAR).unwrap();
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
    let SurfaceForeignMember::Constant(negative) = &library.members[3] else {
        panic!("constant role lost");
    };
    assert!(negative.value.negative);
    assert_eq!(negative.value.magnitude.to_string(), "1");
    let SurfaceForeignMember::Symbol(symbol) = &library.members[4] else {
        panic!("symbol role lost");
    };
    assert_eq!(symbol.parameters[0].name.text, "A");
    assert_eq!(
        symbol.parameters[1].kind.as_ref().unwrap().kind,
        SurfaceKindKind::EffectRow
    );
    assert_eq!(symbol.native_name.value, "abs");
    let SurfaceForeignContract::Operand {
        position: SurfaceForeignNativePosition::Argument(native),
        source: SurfaceForeignOperandSource::Source { position, .. },
        ..
    } = &symbol.contracts[0]
    else {
        panic!("operand mapping lost");
    };
    assert_eq!(native.magnitude.to_string(), "0");
    assert_eq!(position.components[0].magnitude.to_string(), "0");
    for span in [
        library.span,
        negative.value.span,
        symbol.span,
        native.span,
        position.span,
    ] {
        assert_eq!(span.source(), source.id());
        assert!(span.range().end() > span.range().start());
    }
}

#[test]
fn copying_contract_roles_use_explicit_paths_and_qualified_references() {
    let text = "foreign library Queries {\n    profile \"x86_64-unknown-linux-gnu\"\n    symbol Query<W, R, Delta : EffectRow> : (Int, Bytes) -> Foreign.Call<Int> {\n        name \"query\"\n        abi (Abi.CInt, pointer(Abi.ByteAddress), pointer(Abi.Address), Abi.Sentinel) -> Abi.CInt\n        operand 0 from 0.1 scalar\n        operand 1 from 1 bytes(0.0) call_borrow\n        operand 2 from null\n        operand 3 from 0.2 sentinel\n        output result as extent_of(0.3, 0.1, 0.2)\n        outcome result == Abi.Zero { readable result, retained 0.3 }\n        outcome otherwise { readable result }\n    }\n    symbol Tail : Bytes -> Foreign.Call<Int> {\n        name \"tail\"\n        abi (pointer(Abi.ByteAddress)) -> pointer(Abi.ByteAddress)\n        operand 0 from 0 nul copy\n        output result as offset_into(0)\n        outcome result null { unreadable result }\n        outcome otherwise { readable result }\n    }\n    symbol Inspect<R> : Int -> Int {\n        name \"inspect\"\n        abi (pointer(Abi.Address), pointer(Abi.Address), pointer(Abi.ByteAddress)) -> Abi.CInt\n        operand 0 from 0 enclosing\n        operand 1 from 0 current\n        operand 2 from 0 view\n        output result as scalar\n        outcome otherwise { readable result }\n    }\n    access Message<W, R> {\n        window W\n        owner State<R>\n        extent nul\n        preserves Tail\n    }\n}\n";
    let source = SourceFile::new("copy-contract.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).unwrap();
    assert_eq!(module.foreign_libraries[0].members.len(), 5);
}

#[test]
fn zero_operand_void_call_and_adjacent_final_braces_parse() {
    let text = "foreign library Empty {\n    profile \"x86_64-unknown-linux-gnu\"\n    symbol Stop : Unit -> Foreign.Call<Unit> {\n        name \"stop\"\n        abi () -> void\n        outcome otherwise {}}}\n";
    let source = SourceFile::new("zero-operands.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
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
