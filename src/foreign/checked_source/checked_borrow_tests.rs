//! Real source originals and paid scalar checked Borrow rebinding.

use super::*;
use crate::{
    module::{ModuleGraph, ModuleRoots},
    resolve::{DependencyExports, ResolveModuleError, ResolveReason},
    resolved::{CheckedModule, ResolvedModule},
};
use std::sync::atomic::{AtomicU64, Ordering};

const SOURCE: &str = include_str!("../../../tests/fixtures/checked-scalar-borrow/owner.ash");

struct FixtureDirectory(std::path::PathBuf);

impl FixtureDirectory {
    fn new() -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        for _ in 0..1024 {
            let path = std::env::temp_dir().join(format!(
                "ash-checked-borrow-binding-{}-{}",
                std::process::id(),
                IDS.fetch_add(1, Ordering::Relaxed),
            ));
            match std::fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("cannot create private fixture directory: {error}"),
            }
        }
        panic!("fixture directory namespace exhausted without acquiring a directory");
    }
}

impl Drop for FixtureDirectory {
    fn drop(&mut self) {
        // Delete only the directory this guard created. Cleanup also runs on
        // source-write or graph-load panic, never on an AlreadyExists candidate.
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn graph(source: &str) -> ModuleGraph {
    let directory = FixtureDirectory::new();
    let entry = directory.0.join("owner.ash");
    std::fs::write(&entry, source).unwrap();
    crate::module::load_module_graph(&entry, &ModuleRoots::empty())
        .expect("real checked Borrow source parses before binding controls")
}

fn resolve(graph: &ModuleGraph) -> Result<ResolvedModule, ResolveModuleError> {
    let mut checked = Vec::<CheckedModule>::new();
    for loaded in graph.modules() {
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
        let resolved = crate::resolve::resolve_checked_foreign_module(loaded, &dependencies)?;
        if loaded.id() == graph.entry() {
            return Ok(resolved);
        }
        checked.push(
            crate::elaborate::check_module(resolved)
                .expect("genuine builtin dependency checks before root binding"),
        );
    }
    unreachable!("graph has an entry")
}

// Genuine source setup precedes measured context/binding work. These ledgers
// follow the driver's source/rewrite policy, not an enlarged Core/image budget.
fn checked_modules(graph: &ModuleGraph) -> Vec<CheckedModule> {
    let (mut checking, bytes) = crate::compiler_work::source_work(graph).unwrap();
    let limit = checking.limit();
    checking
        .finish_sizing(crate::calibration::limit(
            limit,
            crate::calibration::DiagnosticOwner::Structural,
        ))
        .unwrap();
    let rewrite = crate::calibration::limit(
        crate::compiler_work::rewrite_total(bytes).unwrap(),
        crate::calibration::DiagnosticOwner::Structural,
    );
    let mut coverage = crate::pattern::UsefulnessBudget::default();
    let mut constraints = crate::interface::InterfaceConstraintBudget::default();
    let mut availability = crate::elaborate::ProviderCodeAvailability::default();
    let mut checked = Vec::<CheckedModule>::new();
    for loaded in graph.modules() {
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
        let resolved = crate::resolve::resolve_checked_foreign_module(loaded, &dependencies)
            .expect("actual builtin and Borrow producer resolve before complete registry setup");
        let module =
            crate::elaborate::check_module_with_budget_and_provider_codes_and_rewrite_work(
                resolved,
                &availability,
                &mut checking,
                &mut coverage,
                &mut constraints,
                Some(TypeWorkBudget::with_limit(rewrite)),
            )
            .expect("actual source/summary checking precedes full-registry rebinding controls");
        if let Some(code) = module.provider_code() {
            availability
                .retain(module.module(), code, &mut checking)
                .unwrap();
        }
        if let Some(code) = module.source_resource_code() {
            availability
                .retain_source(module.module(), code, &mut checking)
                .unwrap();
        }
        checked.push(module);
    }
    checked
}

struct Fixture {
    registry: Arc<ResolvedRegistry>,
    original: Arc<CheckedForeignSymbol>,
    owners: Vec<Arc<super::super::source_owner::CheckedForeignOwner>>,
}

impl Fixture {
    fn new() -> Self {
        let graph = graph(SOURCE);
        let checked = checked_modules(&graph);
        let registry = Arc::new(
            ResolvedRegistry::combine_checked(
                &checked,
                &mut TypeWorkBudget::default(),
                &mut crate::interface::InterfaceConstraintBudget::default(),
            )
            .expect("genuine completed builtin/producer modules supply the complete registry"),
        );
        let effect = registry
            .effects()
            .iter()
            .find(|effect| effect.id.module() == graph.entry() && effect.spelling == "Read")
            .unwrap();
        let original = Arc::clone(
            registry
                .native_symbol(OperationId::new(effect.id, 0))
                .unwrap(),
        );
        assert!(matches!(
            original.symbol().owner_call(),
            Some(super::super::source_contract::PreparedOwnerCall::Borrow {
                current_operand: 0,
                ..
            })
        ));
        let owners = vec![Arc::clone(original.owner().unwrap())];
        Self {
            registry,
            original,
            owners,
        }
    }

    fn effect(&self) -> &ResolvedEffectDeclaration {
        self.registry.effect(self.original.effect()).unwrap()
    }

    fn bind(
        &self,
        effect: &ResolvedEffectDeclaration,
        work: &mut TypeWorkBudget,
    ) -> Result<CheckedForeignSymbol, ForeignAdmissionError> {
        // Canonical rebinding receives the actual registered reference. A
        // hostile clone is registered in a separate consuming view, retaining
        // original codec/owner/native brands and all identity-position tables.
        // This is fixture preparation, not an uncharged production registry clone.
        let view = if self
            .registry
            .effect(effect.id)
            .is_some_and(|registered| std::ptr::eq(registered, effect))
        {
            None
        } else {
            let mut effects = self.registry.effects().to_vec();
            let position = effects
                .iter()
                .position(|stored| stored.id == effect.id)
                .unwrap();
            effects[position] = effect.clone();
            Some(
                self.registry
                    .as_ref()
                    .clone()
                    .replace_effects_for_core_test(effects),
            )
        };
        let registry = view.as_ref().unwrap_or(self.registry.as_ref());
        let effect = registry.effect(effect.id).unwrap();
        let codec = self.original.call_codec();
        let context = ForeignBindingContext::new(
            registry,
            codec.module(),
            codec.source(),
            codec.ids(),
            work,
        )?
        .with_owners(&self.owners, work)?;
        bind_checked_foreign_symbol(
            self.original.library(),
            Arc::clone(self.original.prepared()),
            self.original.symbol_index(),
            effect,
            &context,
            work,
        )
    }
}

fn assert_semantic_refusal(result: Result<CheckedForeignSymbol, ForeignAdmissionError>) {
    let error = result.expect_err("changed original correspondence must refuse");
    assert!(
        matches!(
            error.reason(),
            ForeignAdmissionReason::InvalidLibrary
                | ForeignAdmissionReason::InvalidOperation
                | ForeignAdmissionReason::InvalidParameters
                | ForeignAdmissionReason::InvalidSignature
        ),
        "actual semantic refusal: {error:?}"
    );
}

#[test]
fn checked_borrow_binding_has_exact_prefixed_spent_and_fresh_work() {
    let fixture = Fixture::new();
    let effect = fixture.effect();
    let mut measured = TypeWorkBudget::default();
    let bound = fixture.bind(effect, &mut measured).unwrap();
    assert!(Arc::ptr_eq(bound.prepared(), fixture.original.prepared()));
    assert!(Arc::ptr_eq(
        bound.owner().unwrap(),
        fixture.original.owner().unwrap()
    ));
    assert_eq!(bound.parameter_ids(), fixture.original.parameter_ids());
    assert_eq!(bound.operation(), fixture.original.operation());
    let required = measured.used();
    assert!(required > 7);
    for prefix in [0, 7] {
        let mut short = TypeWorkBudget::with_limit(prefix + required - 1);
        short.charge(prefix).unwrap();
        assert_eq!(
            fixture.bind(effect, &mut short).unwrap_err().reason(),
            ForeignAdmissionReason::WorkExhausted
        );
        assert!(
            Arc::ptr_eq(
                fixture.registry.native_symbol(bound.operation()).unwrap(),
                &fixture.original
            ),
            "refusal cannot publish a replacement original"
        );
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(prefix + required);
            exact.charge(prefix).unwrap();
            let retry = fixture.bind(effect, &mut exact).unwrap();
            assert_eq!(exact.used(), prefix + required);
            assert!(Arc::ptr_eq(retry.owner().unwrap(), bound.owner().unwrap()));
            assert_eq!(
                fixture.bind(effect, &mut exact).unwrap_err().reason(),
                ForeignAdmissionReason::WorkExhausted
            );
        }
    }
    fixture
        .bind(effect, &mut TypeWorkBudget::default())
        .unwrap();
}

#[test]
fn checked_borrow_binding_rejects_parameter_operation_and_origin_substitution() {
    let fixture = Fixture::new();
    let canonical = fixture.effect();
    fixture
        .bind(canonical, &mut TypeWorkBudget::default())
        .unwrap();
    let mutations: &[fn(&mut ResolvedEffectDeclaration)] = &[
        |effect| effect.parameters.swap(0, 1),
        |effect| effect.parameters[0].id = effect.parameters[1].id,
        |effect| effect.parameters[0].kind = Kind::EffectRow,
        |effect| effect.parameters[0].origin = effect.parameters[1].origin.clone(),
        |effect| effect.operations[0].annotation.origin = effect.parameters[0].origin.clone(),
        |effect| effect.operations[0].origin = effect.parameters[0].origin.clone(),
        |effect| effect.operations[0].id = OperationId::new(effect.id, 1),
        |effect| {
            let mut operations = effect.operations.to_vec();
            let mut extra = operations[0].clone();
            extra.id = OperationId::new(effect.id, 1);
            operations.push(extra);
            effect.operations = operations.into_boxed_slice();
        },
    ];
    for (index, mutation) in mutations.iter().enumerate() {
        let mut effect: ResolvedEffectDeclaration = canonical.clone();
        mutation(&mut effect);
        let result = fixture.bind(&effect, &mut TypeWorkBudget::default());
        assert!(result.is_err(), "mutation {index} must refuse");
        assert_semantic_refusal(result);
        fixture
            .bind(canonical, &mut TypeWorkBudget::default())
            .unwrap();
    }
    // A genuine different source supplies a donor origin, never a trusted fact.
    let donor = crate::source::SourceFile::new("borrow-origin-donor.ash", "()").unwrap();
    let donor_span = donor
        .span(crate::source::ByteRange::new(0, 2).unwrap())
        .unwrap();
    let mut effect: ResolvedEffectDeclaration = canonical.clone();
    effect.origin = Origin::Source(donor_span);
    assert_semantic_refusal(fixture.bind(&effect, &mut TypeWorkBudget::default()));
}

#[test]
fn checked_borrow_binding_rejects_wrong_host_and_owned_signature_actuals() {
    let fixture = Fixture::new();
    let canonical = fixture.effect();
    fixture
        .bind(canonical, &mut TypeWorkBudget::default())
        .unwrap();
    for replacement in [Type::Int, Type::Variable(canonical.parameters[1].id)] {
        let mut effect: ResolvedEffectDeclaration = canonical.clone();
        let Type::Function(domain, _) = &mut effect.operations[0].annotation.ty else {
            panic!("actual original Read outer arrow");
        };
        let Type::ForeignOwnerApply(_, arguments) = domain.as_mut() else {
            panic!("actual original Read exact State full vector");
        };
        assert_eq!(arguments.len(), 2);
        arguments[0] = crate::types::KindedArgument::TypeArg(replacement);
        assert_semantic_refusal(fixture.bind(&effect, &mut TypeWorkBudget::default()));
    }
    let mut effect: ResolvedEffectDeclaration = canonical.clone();
    let Type::Function(domain, _) = &mut effect.operations[0].annotation.ty else {
        unreachable!()
    };
    let Type::ForeignOwnerApply(_, arguments) = domain.as_mut() else {
        unreachable!()
    };
    arguments.swap(0, 1);
    assert_semantic_refusal(fixture.bind(&effect, &mut TypeWorkBudget::default()));
}

#[test]
fn checked_borrow_extra_scalar_operand_prepares_but_does_not_bind() {
    let fixture = Fixture::new();
    fixture
        .bind(fixture.effect(), &mut TypeWorkBudget::default())
        .unwrap();
    let source = SOURCE.replace(
        "symbol Read<H, R> : State<H, R> -> Foreign.CheckedCall<Int>",
        "symbol Read<H, R> : (State<H, R>, Int) -> Foreign.CheckedCall<Int>",
    ).replace(
        "name \"ash_owner_read\"\n        abi (pointer(Address)) -> CInt",
        "name \"ash_owner_read\"\n        abi (pointer(Address), CInt) -> CInt",
    ).replace(
        "name \"ash_owner_read\"\n        abi (pointer(Address), CInt) -> CInt\n        host H\n        assumes { Callee }\n        operand 0 from 0 current",
        "name \"ash_owner_read\"\n        abi (pointer(Address), CInt) -> CInt\n        host H\n        assumes { Callee }\n        operand 0 from 0 current\n        operand 1 from 1 scalar",
    );
    assert_ne!(source, SOURCE);
    let graph = graph(&source);
    let loaded = graph.module(graph.entry()).unwrap();
    let prepared = super::super::source_contract::prepare_checked_foreign_library(
        loaded.id(),
        &loaded.surface().foreign_libraries[0],
    )
    .expect("genuine extra-scalar Current Borrow prepares before subset binding refusal");
    let read = prepared
        .symbols()
        .iter()
        .find(|symbol| symbol.name() == "Read")
        .unwrap();
    assert_eq!(read.operands().len(), 2);
    assert!(matches!(
        read.owner_call(),
        Some(super::super::source_contract::PreparedOwnerCall::Borrow { .. })
    ));
    match resolve(&graph) {
        Err(ResolveModuleError::Resolution(error)) => {
            assert_eq!(error.reason, ResolveReason::ForeignContract)
        }
        other => panic!(
            "unsupported extra operand must refuse at actual checked binding, not body checking: {other:?}"
        ),
    }
}

#[test]
fn checked_borrow_nested_current_domain_prepares_but_does_not_bind() {
    let fixture = Fixture::new();
    fixture
        .bind(fixture.effect(), &mut TypeWorkBudget::default())
        .unwrap();
    let from = "symbol Read<H, R> : State<H, R> -> Foreign.CheckedCall<Int>";
    assert_eq!(SOURCE.matches(from).count(), 1);
    let source = SOURCE.replace(
        from,
        "symbol Read<H, R> : (State<H, R>, Unit) -> Foreign.CheckedCall<Int>",
    );
    let graph = graph(&source);
    let loaded = graph.module(graph.entry()).unwrap();
    let prepared = super::super::source_contract::prepare_checked_foreign_library(
        loaded.id(),
        &loaded.surface().foreign_libraries[0],
    )
    .expect("genuine tuple-domain Current Borrow prepares before direct-State subset refusal");
    let read = prepared
        .symbols()
        .iter()
        .find(|symbol| symbol.name() == "Read")
        .unwrap();
    assert_eq!(read.operands().len(), 1);
    assert!(matches!(
        read.owner_call(),
        Some(super::super::source_contract::PreparedOwnerCall::Borrow {
            current_operand: 0,
            ..
        })
    ));
    match resolve(&graph) {
        Err(ResolveModuleError::Resolution(error)) => {
            assert_eq!(error.reason, ResolveReason::ForeignContract)
        }
        other => panic!(
            "prepared nested Current must refuse at the actual direct-State binding gate: {other:?}"
        ),
    }
}
