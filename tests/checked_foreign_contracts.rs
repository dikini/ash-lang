use ash::{
    lexer::lex,
    parser::{parse, project_module},
    source::SourceFile,
};

const CHECKED: &str = r#"pub foreign checked library Native {
    profile "x86_64-unknown-linux-gnu"
    assumption Behavior "The native implementation obeys its declared call contract."
    repr CInt = signed(32)
    symbol Abs<A, H, Delta : EffectRow> : Int -> Foreign.CheckedCall<Int> {
        name "abs"
        abi (CInt) -> CInt
        host H
        assumes {Behavior}
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
}
"#;

#[test]
fn checked_contract_metadata_parses_without_changing_full_parameter_order() {
    let source = SourceFile::new("checked-contract.ash", CHECKED).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).unwrap();
    assert!(module.foreign_libraries[0].checked.is_some());
    let symbol = module.foreign_libraries[0]
        .members
        .iter()
        .find_map(|member| {
            if let ash::surface::SurfaceForeignMember::Symbol(symbol) = member {
                Some(symbol)
            } else {
                None
            }
        })
        .unwrap();
    assert_eq!(
        symbol
            .parameters
            .iter()
            .map(|parameter| parameter.name.text.as_str())
            .collect::<Vec<_>>(),
        ["A", "H", "Delta"]
    );
}

#[test]
fn checked_metadata_cannot_be_ignored_by_legacy_preparation() {
    let text = CHECKED.replace("foreign checked library", "foreign library");
    let source = SourceFile::new("legacy-with-checked-metadata.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).unwrap();
    let error = ash::foreign::source_contract::prepare_foreign_library(
        ash::module::ModuleId::from(source.id()),
        &module.foreign_libraries[0],
    )
    .expect_err("legacy preparation must not erase checked metadata");
    assert_eq!(
        error.reason(),
        ash::foreign::source_contract::ForeignContractReason::UnimplementedContract
    );
}

fn prepare_checked(
    text: &str,
) -> Result<
    ash::foreign::source_contract::PreparedForeignLibrary,
    ash::foreign::source_contract::ForeignContractError,
> {
    let source = SourceFile::new("checked-preparation.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).unwrap();
    ash::foreign::source_contract::prepare_checked_foreign_library(
        ash::module::ModuleId::from(source.id()),
        &module.foreign_libraries[0],
    )
}

#[test]
fn checked_preparation_keeps_exact_host_and_assumption_member_coordinates() {
    let library = prepare_checked(CHECKED).unwrap();
    let facts = library.checked_contract().unwrap();
    assert_eq!(facts.assumptions()[0].member_index(), 1);
    assert_eq!(facts.assumptions()[0].name(), "Behavior");
    assert_eq!(facts.symbols()[0].member_index(), 3);
    assert_eq!(facts.symbols()[0].host_parameter(), 1);
    assert_eq!(facts.symbols()[0].assumption_members(), &[1]);
    assert_eq!(library.symbols()[0].parameters().len(), 3);
    assert_eq!(library.symbols()[0].native_type_projection(), &[0, 1]);
}

#[test]
fn an_empty_authored_assumption_set_cannot_erase_native_assumption_floors() {
    use ash::foreign::source_contract::CheckedNativeAssumption;
    let library = prepare_checked(&CHECKED.replace("assumes {Behavior}", "assumes {}")).unwrap();
    let facts = &library.checked_contract().unwrap().symbols()[0];
    assert!(facts.assumption_members().is_empty());
    assert!(
        facts
            .minimum_assumptions()
            .contains(&CheckedNativeAssumption::CompilerAndRuntimeIntegrity)
    );
    assert!(
        facts
            .minimum_assumptions()
            .contains(&CheckedNativeAssumption::AuthorizedBuildCorrespondence)
    );
    assert!(
        facts
            .minimum_assumptions()
            .contains(&CheckedNativeAssumption::NativeAbiAndOutcomeTruth)
    );
}

#[test]
fn checked_host_selection_requires_one_actual_type_formal() {
    use ash::foreign::source_contract::ForeignContractReason;
    for text in [
        CHECKED.replace("host H\n", ""),
        CHECKED.replace("host H", "host H\n        host H"),
        CHECKED.replace("host H", "host Delta"),
        CHECKED.replace("host H", "host Missing"),
    ] {
        assert_eq!(
            prepare_checked(&text).unwrap_err().reason(),
            ForeignContractReason::InvalidCheckedContract
        );
    }
}

#[test]
fn assumption_references_require_the_original_local_library_members() {
    use ash::foreign::source_contract::ForeignContractReason;
    for text in [
        CHECKED.replace("assumes {Behavior}", "assumes {Unknown}"),
        CHECKED.replace("assumes {Behavior}", "assumes {Other.Behavior}"),
        CHECKED.replace("assumes {Behavior}", "assumes {Behavior, Behavior}"),
        CHECKED.replace(
            "assumes {Behavior}",
            "assumes {Behavior}\n        assumes {}",
        ),
        CHECKED.replace("assumes {Behavior}", ""),
    ] {
        assert_eq!(
            prepare_checked(&text).unwrap_err().reason(),
            ForeignContractReason::InvalidCheckedContract
        );
    }
    let original = prepare_checked(CHECKED).unwrap();
    let qualified =
        prepare_checked(&CHECKED.replace("assumes {Behavior}", "assumes {Native.Behavior}"))
            .unwrap();
    assert_eq!(
        original.checked_contract().unwrap().symbols()[0].assumption_members(),
        qualified.checked_contract().unwrap().symbols()[0].assumption_members()
    );
}

const CHECKED_OWNER: &str = r#"foreign checked library Memory {
    profile "x86_64-unknown-linux-gnu"
    assumption Ownership "Native ownership follows the declared transitions."
    repr Address = opaque
    owner State<H, R> {
        representation Address
        owned R
        host H
        teardown Free
    }
    symbol Allocate<H, R> : Unit -> Foreign.CheckedCall<Foreign.Output<Foreign.Nullable<State<H, R>>>> {
        name "allocate"
        abi () -> pointer(Address)
        host H
        assumes {Ownership}
        output result as owner(State<H, R>)
        outcome result nonnull { readable result }
        outcome otherwise { readable result }
    }
    symbol Free<H, R> : State<H, R> -> Foreign.CheckedCall<Foreign.Disposition<Unit>> {
        name "free"
        abi (pointer(Address)) -> void
        host H
        assumes {Ownership}
        operand 0 from 0 current
        retained_dependents block
        outcome otherwise { consumed 0 }
    }
}
"#;

#[test]
fn checked_owners_and_symbols_must_share_the_exact_host_argument() {
    use ash::foreign::source_contract::{CheckedNativeAssumption, ForeignContractReason};
    let library = prepare_checked(CHECKED_OWNER).unwrap();
    assert_eq!(
        library.checked_contract().unwrap().owners()[0].host_parameter(),
        0
    );
    let finish = &library.checked_contract().unwrap().symbols()[1];
    assert!(
        finish
            .minimum_assumptions()
            .contains(&CheckedNativeAssumption::NativeOwnerLifetimeAndDisposition)
    );
    for text in [
        CHECKED_OWNER.replace("host H", "host R"),
        CHECKED_OWNER.replace(
            "output result as owner(State<H, R>)",
            "output result as owner(State<R, H>)",
        ),
        CHECKED_OWNER.replace(
            "symbol Free<H, R> : State<H, R>",
            "symbol Free<H, R> : State<R, H>",
        ),
    ] {
        assert_eq!(
            prepare_checked(&text).unwrap_err().reason(),
            ForeignContractReason::InvalidCheckedContract
        );
    }
}

#[test]
fn initialized_output_and_input_copy_floors_survive_empty_authored_sets() {
    use ash::foreign::source_contract::CheckedNativeAssumption::*;
    let owner = CHECKED_OWNER
        .replace(
            "    assumption Ownership \"Native ownership follows the declared transitions.\"\n",
            "",
        )
        .replace("assumes {Ownership}", "assumes {}")
        .replace(
            "repr Address = opaque",
            "repr Size = size_t\n    repr Address = bytes",
        )
        .replace("Unit ->", "Int ->")
        .replace(
            "abi () -> pointer(Address)",
            "abi (Size) -> pointer(Address)\n        operand 0 from 0 scalar",
        )
        .replace(
            "readable result }",
            "readable result, initialized_bytes result from 0 }",
        )
        .replacen(
            "outcome otherwise { readable result, initialized_bytes result from 0 }",
            "outcome otherwise { readable result }",
            1,
        );
    let library = prepare_checked(&owner).unwrap();
    let acquisition = &library.checked_contract().unwrap().symbols()[0];
    assert!(acquisition.assumption_members().is_empty());
    assert!(
        acquisition
            .minimum_assumptions()
            .contains(&NativeOutputIntervalValidity)
    );
    assert!(
        acquisition
            .minimum_assumptions()
            .contains(&NativeAliasingAndNonInterference)
    );
    let hash = r#"    symbol Hash<H, R> : (State<H, R>, Bytes, Int) -> Foreign.CheckedCall<Int> {
        name "hash_bytes"
        abi (pointer(Address), pointer(Address), Size) -> Size
        host H
        assumes {}
        operand 0 from 0 current
        operand 1 from 1 bytes(2) copy
        operand 2 from 2 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
"#;
    let copy = owner.replace("    symbol Free", &format!("{hash}    symbol Free"));
    for (text, has_copy) in [
        (&copy, true),
        (
            &copy.replace("bytes(2) copy", "bytes(2) call_borrow"),
            false,
        ),
    ] {
        let library = prepare_checked(text).unwrap();
        let hash = &library.checked_contract().unwrap().symbols()[1];
        assert!(hash.assumption_members().is_empty());
        for required in [
            NativeInputIntervalValidity,
            NativeInputNonRetention,
            NativeAliasingAndNonInterference,
            SerializedNativeAccess,
        ] {
            assert!(hash.minimum_assumptions().contains(&required));
        }
        assert_eq!(
            hash.minimum_assumptions()
                .contains(&NativeIndependentInputCopy),
            has_copy
        );
    }
}

#[test]
fn legacy_refuses_each_checked_metadata_role_and_passive_preparation_requires_opt_in() {
    use ash::foreign::source_contract::{ForeignContractReason, prepare_foreign_library};
    let scalar_without_assumption = CHECKED
        .replace("    assumption Behavior \"The native implementation obeys its declared call contract.\"\n", "")
        .replace("assumes {Behavior}", "assumes {}");
    for text in [
        scalar_without_assumption.replace("        assumes {}\n", ""),
        scalar_without_assumption.replace("        host H\n", ""),
        CHECKED_OWNER
            .replace(
                "    assumption Ownership \"Native ownership follows the declared transitions.\"\n",
                "",
            )
            .replace("        host H\n        assumes {Ownership}\n", ""),
    ] {
        let source = SourceFile::new(
            "legacy-role-refusal.ash",
            text.replace("foreign checked library", "foreign library"),
        )
        .unwrap();
        let module = project_module(&source, &parse(lex(&source).unwrap())).unwrap();
        assert_eq!(
            prepare_foreign_library(
                ash::module::ModuleId::from(source.id()),
                &module.foreign_libraries[0]
            )
            .unwrap_err()
            .reason(),
            ForeignContractReason::UnimplementedContract
        );
    }
    assert_eq!(
        prepare_checked(&CHECKED.replace("foreign checked library", "foreign library"))
            .unwrap_err()
            .reason(),
        ForeignContractReason::InvalidCheckedContract
    );
}
