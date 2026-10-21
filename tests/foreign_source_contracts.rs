use ash::{
    foreign::source_contract::{
        ForeignContractReason, PreparedAbiResult, PreparedScalarRepresentation,
        prepare_foreign_library,
    },
    lexer::lex,
    module::ModuleId,
    parser::{parse, project_module},
    source::SourceFile,
};

const SCALAR: &str = r#"foreign library C {
    profile "x86_64-unknown-linux-gnu"
    repr I32 = signed(32)
    const Ok : I32 = 0
    symbol Abs<T, Delta : EffectRow> : Int -> Foreign.Call<Int> {
        name "abs"
        abi (I32) -> I32
        operand 0 from 0 scalar
        output result as scalar
        outcome result == Ok { readable result }
        outcome otherwise { readable result }
    }
}
"#;

fn prepare(
    text: &str,
) -> Result<
    ash::foreign::source_contract::PreparedForeignLibrary,
    ash::foreign::source_contract::ForeignContractError,
> {
    let source = SourceFile::new("foreign-contract.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(tree.lexical_diagnostics().is_empty());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).unwrap();
    prepare_foreign_library(ModuleId::from(source.id()), &module.foreign_libraries[0])
}

#[test]
fn prepares_scalar_abi_without_granting_resolved_operation_authority() {
    let prepared = prepare(SCALAR).unwrap();
    assert_eq!(prepared.profile(), "x86_64-unknown-linux-gnu");
    let symbol = &prepared.symbols()[0];
    assert_eq!(symbol.native_name(), "abs");
    assert_eq!(symbol.parameters().len(), 2);
    assert_eq!(symbol.native_type_projection(), &[0]);
    assert_eq!(
        symbol.result(),
        PreparedAbiResult::Scalar(PreparedScalarRepresentation::Signed(32))
    );
    assert_eq!(symbol.operands().len(), 1);
    assert_eq!(
        symbol.origin().primary_span().source(),
        prepared.origin().primary_span().source()
    );
}

#[test]
fn prepares_sqlite_open_input_and_initialized_owner_output_contract() {
    let prepared = prepare(include_str!("../libraries/sqlite.ash"))
        .expect("the accepted SQLite call-borrow/out-owner contract is preparable");
    let open = prepared
        .symbols()
        .iter()
        .find(|symbol| symbol.name() == "Open")
        .unwrap();
    assert_eq!(open.native_name(), "sqlite3_open_v2");
    assert_eq!(
        open.result(),
        PreparedAbiResult::Scalar(PreparedScalarRepresentation::Signed(32))
    );
    assert_eq!(open.operands().len(), 4);
    assert!(open.owner_call().is_some());
}

#[test]
fn sqlite_owner_output_contract_rejects_incomplete_or_mismatched_roles() {
    let original = include_str!("../libraries/sqlite.ash");
    for (label, changed) in [
        (
            "missing owner role",
            original.replace("        output 1 as owner(ConnectionState<C>)\n", ""),
        ),
        (
            "missing scalar role",
            original.replace(
                "        output result as scalar\n        output 1",
                "        output 1",
            ),
        ),
        (
            "uninitialized owner",
            original.replace(
                "readable result, readable 1",
                "readable result, unreadable 1",
            ),
        ),
        (
            "missing owner readability",
            original.replace("readable result, readable 1", "readable result"),
        ),
        (
            "wrong output position",
            original.replace("output 1 as owner", "output 2 as owner"),
        ),
        (
            "output is also an input",
            original.replace(
                "        output 1 as owner",
                "        operand 1 from 0 nul call_borrow\n        output 1 as owner",
            ),
        ),
        (
            "wrong String leaf",
            original.replace("symbol Open<C> : String", "symbol Open<C> : Int"),
        ),
        (
            "scalar pointer role",
            original.replace("from 0 nul call_borrow", "from 0 scalar"),
        ),
        (
            "scalar null",
            original.replace(
                "operand 2 from constant ReadWriteCreate",
                "operand 2 from null",
            ),
        ),
        (
            "unowned output",
            original.replace("out(pointer(Address))", "pointer(Address)"),
        ),
    ] {
        assert!(prepare(&changed).is_err(), "{label}");
    }
}

#[test]
fn interleaved_rows_preserve_complete_parameter_order_and_type_projection() {
    let text = SCALAR.replace(
        "Abs<T, Delta : EffectRow>",
        "Abs<Before : EffectRow, T, Middle : EffectRow, U>",
    );
    let prepared = prepare(&text).unwrap();
    let symbol = &prepared.symbols()[0];
    assert_eq!(
        symbol
            .parameters()
            .iter()
            .map(|parameter| parameter.name())
            .collect::<Vec<_>>(),
        ["Before", "T", "Middle", "U"]
    );
    assert_eq!(
        symbol
            .parameters()
            .iter()
            .map(|parameter| parameter.kind())
            .collect::<Vec<_>>(),
        [
            &ash::types::Kind::EffectRow,
            &ash::types::Kind::Type,
            &ash::types::Kind::EffectRow,
            &ash::types::Kind::Type
        ]
    );
    assert_eq!(symbol.native_type_projection(), &[1, 3]);
}

#[test]
fn rejects_target_width_and_literal_range_before_bridge_planning() {
    for (text, reason) in [
        (
            SCALAR.replace("x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu"),
            ForeignContractReason::UnsupportedProfile,
        ),
        (
            SCALAR.replace("signed(32)", "signed(16)"),
            ForeignContractReason::UnsupportedRepresentation,
        ),
        (
            SCALAR.replace("const Ok : I32 = 0", "const Ok : I32 = 2147483648"),
            ForeignContractReason::ConstantRange,
        ),
        (
            SCALAR.replace("const Ok : I32 = 0", "const Ok : I32 = -2147483649"),
            ForeignContractReason::ConstantRange,
        ),
        (
            SCALAR.replace(
                "    repr I32",
                "    profile \"x86_64-unknown-linux-gnu\"\n    repr I32",
            ),
            ForeignContractReason::DuplicateProfile,
        ),
    ] {
        assert_eq!(prepare(&text).unwrap_err().reason(), reason, "{text}");
    }
    assert!(prepare(&SCALAR.replace("const Ok : I32 = 0", "const Ok : I32 = -2147483648")).is_ok());
}

#[test]
fn rejects_incomplete_mapping_invalid_source_paths_and_scalar_null() {
    for (text, reason) in [
        (
            SCALAR.replace("        operand 0 from 0 scalar\n", ""),
            ForeignContractReason::OperandCoverage,
        ),
        (
            SCALAR.replace(
                "operand 0 from 0 scalar",
                "operand 0 from 0 scalar\n        operand 0 from 0 scalar",
            ),
            ForeignContractReason::OperandCoverage,
        ),
        (
            SCALAR.replace("operand 0 from 0 scalar", "operand 1 from 0 scalar"),
            ForeignContractReason::OperandCoverage,
        ),
        (
            SCALAR.replace("operand 0 from 0 scalar", "operand result from 0 scalar"),
            ForeignContractReason::OperandCoverage,
        ),
        (
            SCALAR.replace("operand 0 from 0 scalar", "operand 0 from 1 scalar"),
            ForeignContractReason::SourcePosition,
        ),
        (
            SCALAR.replace("operand 0 from 0 scalar", "operand 0 from 0.0 scalar"),
            ForeignContractReason::SourcePosition,
        ),
        (
            SCALAR.replace("operand 0 from 0 scalar", "operand 0 from null"),
            ForeignContractReason::OperandRole,
        ),
        (
            SCALAR.replace("        output result as scalar\n", ""),
            ForeignContractReason::OutputCoverage,
        ),
        (
            SCALAR.replace("abi (I32)", "abi (void)"),
            ForeignContractReason::VoidPosition,
        ),
    ] {
        assert_eq!(prepare(&text).unwrap_err().reason(), reason, "{text}");
    }
}

#[test]
fn finite_outcomes_are_total_disjoint_and_always_read_scalar_results() {
    for (text, reason) in [
        (
            SCALAR.replace("        outcome otherwise { readable result }\n", ""),
            ForeignContractReason::OutcomeCoverage,
        ),
        (
            SCALAR.replace(
                "        outcome otherwise",
                "        outcome result == Ok { readable result }\n        outcome otherwise",
            ),
            ForeignContractReason::OverlappingOutcomes,
        ),
        (
            SCALAR.replace(
                "outcome otherwise { readable result }",
                "outcome otherwise { unreadable result }",
            ),
            ForeignContractReason::Readability,
        ),
        (
            SCALAR.replace(
                "outcome otherwise { readable result }",
                "outcome otherwise { }",
            ),
            ForeignContractReason::Readability,
        ),
    ] {
        assert_eq!(prepare(&text).unwrap_err().reason(), reason, "{text}");
    }
}

#[test]
fn duplicate_members_and_unsupported_pointer_contracts_do_not_partially_admit() {
    let duplicate = SCALAR.replace("    const Ok", "    repr I32 = signed(64)\n    const Ok");
    assert_eq!(
        prepare(&duplicate).unwrap_err().reason(),
        ForeignContractReason::DuplicateMember
    );
    let pointer = SCALAR.replace("abi (I32) -> I32", "abi (pointer(I32)) -> I32");
    assert_eq!(
        prepare(&pointer).unwrap_err().reason(),
        ForeignContractReason::UnimplementedContract
    );
    let higher_kind = SCALAR.replace(
        "Abs<T, Delta : EffectRow>",
        "Abs<F : Type -> Type, Delta : EffectRow>",
    );
    assert_eq!(
        prepare(&higher_kind).unwrap_err().reason(),
        ForeignContractReason::UnimplementedContract
    );
}

#[test]
fn nested_product_paths_and_full_unsigned_literals_preserve_the_authored_mapping() {
    let nested = SCALAR
        .replace(
            "Int -> Foreign.Call<Int>",
            "(Int, (Int, Int)) -> Foreign.Call<Int>",
        )
        .replace("operand 0 from 0 scalar", "operand 0 from 1.0 scalar");
    let prepared = prepare(&nested).unwrap();
    assert!(matches!(prepared.symbols()[0].operands()[0].source(),
        ash::foreign::source_contract::PreparedOperandSource::Source(path) if path == &[1, 0]));
    let unsigned = SCALAR
        .replace("signed(32)", "unsigned(64)")
        .replace(
            "const Ok : I32 = 0",
            "const Ok : I32 = 18446744073709551615",
        )
        .replace("operand 0 from 0 scalar", "operand 0 from constant Ok");
    assert_eq!(
        prepare(&unsigned).unwrap().constants()[0].value().magnitude,
        u64::MAX
    );
    assert_eq!(
        prepare(&unsigned.replace("18446744073709551615", "18446744073709551616"))
            .unwrap_err()
            .reason(),
        ForeignContractReason::ConstantRange
    );
}

#[test]
fn zero_argument_scalar_symbols_have_no_fabricated_unit_abi_operand() {
    let text = r#"foreign library C {
    profile "x86_64-unknown-linux-gnu"
    repr I32 = signed(32)
    symbol Pid : Unit -> Foreign.Call<Int> {
        name "getpid"
        abi () -> I32
        output result as scalar
        outcome otherwise { readable result }
    }
}
"#;
    let prepared = prepare(text).unwrap();
    assert!(prepared.symbols()[0].operands().is_empty());
    assert_eq!(
        prepared.symbols()[0].result(),
        PreparedAbiResult::Scalar(PreparedScalarRepresentation::Signed(32))
    );
}

#[test]
fn void_abi_result_prepares_with_empty_outcome_facts() {
    let text = r#"foreign library C {
    profile "x86_64-unknown-linux-gnu"
    symbol Notify : Unit -> Foreign.Call<Unit> {
        name "notify"
        abi () -> void
        outcome otherwise { }
    }
}
"#;
    let prepared = prepare(text).unwrap();
    assert!(prepared.symbols()[0].operands().is_empty());
    assert_eq!(prepared.symbols()[0].result(), PreparedAbiResult::Void);
    assert_eq!(
        prepare(&text.replace(
            "outcome otherwise { }",
            "outcome otherwise { readable result }"
        ))
        .unwrap_err()
        .reason(),
        ForeignContractReason::Readability
    );
}

#[test]
fn checked_library_cannot_enter_legacy_abi_preparation() {
    let text = SCALAR.replace("foreign library", "foreign checked library");
    let error = prepare(&text).expect_err("checked intent must not grant legacy executable facts");
    assert_eq!(error.reason(), ForeignContractReason::UnimplementedContract);
    assert_eq!(error.span().range().end() - error.span().range().start(), 7);
}
