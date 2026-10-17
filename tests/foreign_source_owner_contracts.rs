use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    foreign::source_contract::{
        ForeignContractError, ForeignContractReason, PreparedAbiResult,
        PreparedAddressRepresentation, PreparedForeignCall, PreparedForeignLibrary,
        PreparedOperandSource, PreparedOwnerArgument, PreparedOwnerCall, PreparedRepresentation,
        PreparedScalarRepresentation, prepare_foreign_library,
    },
    lexer::lex,
    module::{ModuleId, ModuleRoots, load_module_graph},
    parser::{parse, project_module},
    resolve::{DependencyExports, ResolveModuleError, ResolveReason, resolve_module},
    source::{SourceFile, Span},
    types::Kind,
};

// These are passive preparation facts. Their names and source result shapes do
// not authenticate owner nominals, result codecs, resources or native execution.
const BYTES: &str = r#"pub foreign library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
    repr Byte = bytes
    owner State<Before : EffectRow, R, After : EffectRow> {
        representation Byte
        owned R
        teardown Free
    }
    symbol Allocate<After : EffectRow, R, Before : EffectRow> : (Int, Int) -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<{| Before}, R, {| After}>>>> {
        name "calloc"
        abi (Size, Size) -> pointer(Byte)
        operand 0 from 0 scalar
        operand 1 from 1 scalar
        output result as owner(State<{| Before}, R, {| After}>)
        outcome result nonnull { readable result, initialized_bytes result from 0 }
        outcome otherwise { readable result }
    }
    symbol Free<Before : EffectRow, R, After : EffectRow> : (Int, State<{| Before}, R, {| After}>) -> Foreign.Call<Foreign.Disposition<Unit>> {
        name "free"
        abi (pointer(Byte)) -> void
        operand 0 from 1 current
        retained_dependents block
        outcome otherwise { consumed 1 }
    }
}
"#;

const ADDRESS_ONLY: &str = r#"foreign library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Byte = bytes
}
"#;

const SCALAR_SYMBOL: &str = r#"    symbol Notify : Unit -> Foreign.Call<Unit> {
        name "notify"
        abi () -> void
        outcome otherwise {}
    }
"#;

fn prepare(text: &str) -> Result<PreparedForeignLibrary, ForeignContractError> {
    let source = SourceFile::new("source-owner-contract.ash", text).unwrap();
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

fn written(text: &str, span: Span) -> &str {
    let range = span.range();
    &text[range.start() as usize..range.end() as usize]
}

static IDS: AtomicU64 = AtomicU64::new(0);

struct Source(PathBuf);

impl Source {
    fn new(text: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "ash-source-owner-contract-{}-{}.ash",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::write(&path, text).unwrap();
        Self(path)
    }
}

impl Drop for Source {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

#[test]
fn byte_owner_preparation_retains_tagged_arguments_and_original_member_coordinates() {
    let prepared = prepare(BYTES).unwrap();
    assert!(prepared.public());
    assert_eq!(prepared.owners().len(), 1);
    let owner = &prepared.owners()[0];
    assert_eq!(owner.name(), "State");
    assert_eq!(owner.member_index(), 3);
    assert_eq!(owner.owned_parameter(), 1);
    assert_eq!(owner.representation(), PreparedAddressRepresentation::Bytes);
    assert_eq!(owner.teardown_member(), 5);
    assert_eq!(written(BYTES, owner.representation_span()), "Byte");
    assert_eq!(written(BYTES, owner.owned_span()), "R");
    assert_eq!(written(BYTES, owner.teardown_span()), "Free");
    assert_eq!(
        owner
            .parameters()
            .iter()
            .map(|parameter| (parameter.name(), parameter.kind()))
            .collect::<Vec<_>>(),
        [
            ("Before", &Kind::EffectRow),
            ("R", &Kind::Type),
            ("After", &Kind::EffectRow),
        ]
    );
    assert_eq!(prepared.representations()[0].member_index(), 1);
    assert_eq!(prepared.representations()[1].member_index(), 2);
    assert_eq!(
        prepared.representations()[1].representation(),
        PreparedRepresentation::Address(PreparedAddressRepresentation::Bytes)
    );

    let acquire = &prepared.symbols()[0];
    assert_eq!(acquire.member_index(), 4);
    assert_eq!(acquire.native_name(), "calloc");
    assert_eq!(acquire.native_type_projection(), &[1]);
    assert_eq!(
        acquire.result(),
        PreparedAbiResult::Address(PreparedAddressRepresentation::Bytes)
    );
    assert_eq!(acquire.operands().len(), 2);
    for (index, operand) in acquire.operands().iter().enumerate() {
        assert_eq!(
            operand.representation(),
            PreparedRepresentation::Scalar(PreparedScalarRepresentation::SizeT)
        );
        assert!(
            matches!(operand.source(), PreparedOperandSource::Source(path) if path == &[index])
        );
    }
    let PreparedForeignCall::Owner(PreparedOwnerCall::Acquire {
        application,
        first_nonnull,
        initialized_bytes,
        ..
    }) = acquire.call()
    else {
        panic!("acquisition must retain owner preparation");
    };
    assert_eq!(application.owner(), 0);
    assert_eq!(
        application.arguments(),
        &[
            PreparedOwnerArgument::EffectRow(2),
            PreparedOwnerArgument::Type(1),
            PreparedOwnerArgument::EffectRow(0),
        ]
    );
    assert!(*first_nonnull);
    let initialized = initialized_bytes.as_ref().unwrap();
    assert_eq!(initialized.extent(), &[0]);
    assert_eq!(
        written(BYTES, initialized.span()),
        "initialized_bytes result from 0"
    );

    let teardown = &prepared.symbols()[1];
    assert_eq!(teardown.member_index(), owner.teardown_member());
    assert_eq!(teardown.result(), PreparedAbiResult::Void);
    assert_eq!(
        teardown.operands()[0].representation(),
        PreparedRepresentation::Address(PreparedAddressRepresentation::Bytes)
    );
    assert!(
        matches!(teardown.operands()[0].source(), PreparedOperandSource::Current(path) if path == &[1])
    );
    let PreparedForeignCall::Owner(PreparedOwnerCall::Teardown {
        application,
        current_operand,
        ..
    }) = teardown.call()
    else {
        panic!("teardown must retain owner preparation");
    };
    assert_eq!(*current_operand, 0);
    assert_eq!(application.owner(), 0);
    assert_eq!(
        application.arguments(),
        &[
            PreparedOwnerArgument::EffectRow(0),
            PreparedOwnerArgument::Type(1),
            PreparedOwnerArgument::EffectRow(2),
        ]
    );
}

#[test]
fn opaque_owner_preparation_requires_no_byte_extent_while_byte_owners_do() {
    let text = BYTES
        .replace("repr Byte = bytes", "repr Byte = opaque")
        .replace(", initialized_bytes result from 0", "");
    let prepared = prepare(&text).unwrap();
    assert_eq!(
        prepared.owners()[0].representation(),
        PreparedAddressRepresentation::Opaque
    );
    assert_eq!(
        prepared.symbols()[0].result(),
        PreparedAbiResult::Address(PreparedAddressRepresentation::Opaque)
    );
    assert!(matches!(
        prepared.symbols()[0].call(),
        PreparedForeignCall::Owner(PreparedOwnerCall::Acquire {
            initialized_bytes: None,
            ..
        })
    ));
    assert_eq!(
        prepare(&BYTES.replace(", initialized_bytes result from 0", ""))
            .unwrap_err()
            .reason(),
        ForeignContractReason::Readability
    );
}

#[test]
fn malformed_owner_applications_teardowns_and_outcomes_publish_no_preparation() {
    for (text, reason) in [
        (
            BYTES.replace("        owned R", "        owned Before"),
            ForeignContractReason::InvalidParameters,
        ),
        (
            BYTES.replace(
                "output result as owner(State<{| Before}, R, {| After}>)",
                "output result as owner(State<Before, R, {| After}>)",
            ),
            ForeignContractReason::UnimplementedContract,
        ),
        (
            BYTES.replace(
                "output result as owner(State<{| Before}, R, {| After}>)",
                "output result as owner(State<{| Before}, R>)",
            ),
            ForeignContractReason::InvalidParameters,
        ),
        (
            BYTES.replace("        teardown Free", "        teardown Missing"),
            ForeignContractReason::UnknownMember,
        ),
        (
            BYTES.replace("        teardown Free", "        teardown Allocate"),
            ForeignContractReason::OperandRole,
        ),
        (
            BYTES.replace(
                "outcome otherwise { consumed 1 }",
                "outcome otherwise { consumed 0 }",
            ),
            ForeignContractReason::OperandRole,
        ),
        (
            BYTES.replace("        retained_dependents block\n", ""),
            ForeignContractReason::OutcomeCoverage,
        ),
        (
            BYTES.replace("        outcome otherwise { readable result }\n", ""),
            ForeignContractReason::UnimplementedContract,
        ),
        (
            BYTES.replace(
                "outcome otherwise { readable result }",
                "outcome otherwise {}",
            ),
            ForeignContractReason::Readability,
        ),
    ] {
        assert_eq!(prepare(&text).unwrap_err().reason(), reason, "{text}");
    }
}

#[test]
fn public_source_resolution_preserves_owner_rows_and_refuses_invalid_ordinary_types() {
    let with_scalar = BYTES.replace(
        "    owner State",
        &format!("{SCALAR_SYMBOL}    owner State"),
    );
    let prepared = prepare(&with_scalar).unwrap();
    assert!(matches!(
        prepared.symbols()[0].call(),
        PreparedForeignCall::Scalar { .. }
    ));
    assert_eq!(prepared.owners().len(), 1);
    assert!(prepare(ADDRESS_ONLY).unwrap().symbols().is_empty());
    let ordinary_row = format!(
        "{BYTES}\ntype Ordinary<T> = Payload(T)\n\ninvalid : Ordinary<{{}}> -> Unit\ninvalid ignored = ()\n"
    );

    for (text, expected) in [
        (BYTES, None),
        (with_scalar.as_str(), None),
        (ADDRESS_ONLY, Some(ResolveReason::ForeignContract)),
        (ordinary_row.as_str(), Some(ResolveReason::TypeKind)),
    ] {
        let source_text = format!("import @builtin.foreign as Foreign\n{text}");
        let source = Source::new(&source_text);
        let graph = load_module_graph(&source.0, &ModuleRoots::empty()).unwrap();
        let mut checked: Vec<ash::resolved::CheckedModule> = Vec::new();
        for dependency in &graph.modules()[..graph.modules().len() - 1] {
            let dependencies = dependency
                .dependencies()
                .iter()
                .map(|edge| {
                    DependencyExports::new(
                        edge,
                        checked
                            .iter()
                            .find(|module| module.module() == edge.target())
                            .unwrap()
                            .exports(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module(dependency, &dependencies).unwrap();
            checked.push(ash::elaborate::check_module(resolved).unwrap());
        }
        let loaded = graph.modules().last().unwrap();
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                DependencyExports::new(
                    edge,
                    checked
                        .iter()
                        .find(|module| module.module() == edge.target())
                        .unwrap()
                        .exports(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(loaded, &dependencies);
        let Some(expected) = expected else {
            ash::elaborate::check_module(resolved.unwrap()).unwrap();
            continue;
        };
        let Err(ResolveModuleError::Resolution(failure)) = resolved else {
            panic!("invalid ordinary Type or unowned address must fail at source resolution");
        };
        assert_eq!(failure.reason, expected, "{text}: {failure:?}");
        assert_eq!(
            failure.primary.span().source(),
            loaded.surface().foreign_libraries[0].span.source()
        );
        if expected == ResolveReason::TypeKind {
            assert_eq!(written(&source_text, failure.primary.span()), "{}");
        }
    }
}
