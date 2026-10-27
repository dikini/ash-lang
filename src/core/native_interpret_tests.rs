//! Independent admission regressions for the owner-free Core boundary.

use std::{
    path::PathBuf,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

use super::check_ordinary_effect_modules_with_budget_for_test;
use super::validate::validate_effect_modules_with_work;
use crate::{
    core::{
        EffectCoreBuilder, EffectExprKind, EffectOperation, NativeInterpretation,
        UnvalidatedEffectProgram, ValidatedEffectProgram, transform,
    },
    foreign::checked_source::{CheckedForeignSymbol, ForeignBindingContext, bind_foreign_symbol},
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::{CheckedModule, ResolvedRegistry},
    source::Origin,
    types::{
        EffectId, EffectInstance, EffectRow, KindedArgument, Type, TypeVariableId, TypeWorkBudget,
    },
};

const SOURCE: &str = r#"import @builtin.foreign as Foreign
import @builtin.bytes as B
pub foreign library C {
    profile "x86_64-unknown-linux-gnu"
    symbol Make : Unit -> Foreign.Address { name "fixture_make" }
    symbol Stop : Unit -> Unit { name "fixture_stop" }
    symbol Echo : Foreign.Address -> Foreign.Address { name "fixture_echo" }
    symbol EchoBytes : Bytes -> Foreign.Address { name "fixture_echo_bytes" }
}
pub effect Ordinary<Rows : EffectRow, T> {
    call : T -> T
}
"#;

struct Directory(PathBuf);
impl Drop for Directory {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

struct Fixture {
    graph: ModuleGraph,
    registry: Arc<ResolvedRegistry>,
    make: Arc<CheckedForeignSymbol>,
    stop: Arc<CheckedForeignSymbol>,
    echo: Arc<CheckedForeignSymbol>,
    bytes: Arc<CheckedForeignSymbol>,
    ordinary: EffectId,
}
impl Fixture {
    fn new() -> Self {
        static IDS: AtomicU64 = AtomicU64::new(0);
        let directory = loop {
            let id = IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "ash-native-interpret-core-{}-{id}",
                std::process::id(),
            ));
            match std::fs::create_dir(&path) {
                Ok(()) => break Directory(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("native Core fixture: {error}"),
            }
        };
        let entry = directory.0.join("entry.ash");
        std::fs::write(&entry, SOURCE).unwrap();
        let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
        let mut checked: Vec<CheckedModule> = Vec::new();
        for loaded in graph.modules() {
            let dependencies: Vec<_> = loaded
                .dependencies()
                .iter()
                .map(|edge| {
                    let dependency = checked
                        .iter()
                        .find(|module| module.module() == edge.target())
                        .expect("dependencies precede source users");
                    DependencyExports::new(edge, dependency.exports()).unwrap()
                })
                .collect();
            checked.push(
                crate::elaborate::check_module(resolve_module(loaded, &dependencies).unwrap())
                    .unwrap(),
            );
        }
        let exports = checked
            .iter()
            .find(|module| module.module() == graph.entry())
            .unwrap()
            .exports();
        let make = Arc::clone(
            exports
                .effect("Make")
                .unwrap()
                .native_contract
                .as_ref()
                .unwrap(),
        );
        let stop = Arc::clone(
            exports
                .effect("Stop")
                .unwrap()
                .native_contract
                .as_ref()
                .unwrap(),
        );
        let echo = Arc::clone(
            exports
                .effect("Echo")
                .unwrap()
                .native_contract
                .as_ref()
                .unwrap(),
        );
        let bytes = Arc::clone(
            exports
                .effect("EchoBytes")
                .unwrap()
                .native_contract
                .as_ref()
                .unwrap(),
        );
        let ordinary = exports.effect("Ordinary").unwrap().id;
        let defining = checked
            .iter()
            .find(|module| module.module() == graph.entry())
            .unwrap();
        let effects = defining.effects().to_vec();
        assert_eq!(
            effects.len(),
            5,
            "the standalone donor retains all original declarations"
        );
        let parameters = effects
            .iter()
            .flat_map(|effect| effect.parameters.iter().cloned())
            .collect();
        let foreign = checked
            .iter()
            .find(|module| module.module().is_builtin_foreign())
            .expect("the actual defining Foreign module remains checked");
        let address = foreign
            .registry()
            .nominals()
            .iter()
            .find(|nominal| nominal.spelling == "Address")
            .expect("the original Foreign.Address declaration remains canonical");
        assert!(
            foreign
                .registry()
                .nominal_parameters(address.id)
                .unwrap()
                .is_empty()
        );
        let abstracts = vec![(
            address.id,
            address.spelling.clone(),
            crate::types::Kind::Type,
            address.origin.primary_span(),
        )];
        let mut work = TypeWorkBudget::default();
        let mut registry = ResolvedRegistry::default()
            .with_effects_with_budget(effects, &mut work)
            .unwrap()
            .with_image_kind_facts(parameters, abstracts, &mut work)
            .unwrap();
        for symbol in [&make, &stop, &echo, &bytes] {
            registry
                .retain_native_symbol(Arc::clone(symbol), &mut work)
                .unwrap();
        }
        let registry = Arc::new(registry);
        Self {
            graph,
            registry,
            make,
            stop,
            echo,
            bytes,
            ordinary,
        }
    }

    fn instance(&self, unit: bool) -> EffectInstance {
        EffectInstance::new(
            if unit {
                self.stop.effect()
            } else {
                self.make.effect()
            },
            Box::new([]),
        )
    }

    fn program(&self, unit: bool) -> UnvalidatedEffectProgram {
        self.program_with_checked_declarations(unit, true)
    }

    fn program_with_checked_declarations(
        &self,
        unit: bool,
        include_checked: bool,
    ) -> UnvalidatedEffectProgram {
        let mut program = self.program_for(if unit { &self.stop } else { &self.make });
        if !include_checked {
            program.registry = Arc::new(ResolvedRegistry::default());
        }
        program
    }

    fn program_for(&self, symbol: &Arc<CheckedForeignSymbol>) -> UnvalidatedEffectProgram {
        let origin = Origin::Source(
            self.graph
                .module(self.graph.entry())
                .unwrap()
                .source()
                .span(crate::source::ByteRange::new(0, 1).unwrap())
                .unwrap(),
        );
        let Type::Function(domain, result) = symbol.source_signature() else {
            panic!("signature");
        };
        let mut builder = EffectCoreBuilder::with_effect_registry(Arc::clone(&self.registry));
        let operand = match domain.as_ref() {
            Type::Unit => builder.unit(Type::Unit, origin.clone()).unwrap(),
            Type::Bytes | Type::Nominal(_) => {
                let (operation, module) = if domain.as_ref() == &Type::Bytes {
                    (
                        crate::core::packed::Intrinsic::BytesEmpty,
                        self.graph
                            .modules()
                            .iter()
                            .find(|module| module.id().is_builtin_bytes())
                            .unwrap()
                            .id(),
                    )
                } else {
                    (
                        crate::core::packed::Intrinsic::AddressNull,
                        self.graph
                            .modules()
                            .iter()
                            .find(|module| module.id().is_builtin_foreign())
                            .unwrap()
                            .id(),
                    )
                };
                let callable = builder
                    .intrinsic(
                        operation,
                        module,
                        Type::Function(Box::new(Type::Unit), domain.clone()),
                        origin.clone(),
                    )
                    .unwrap();
                let unit = builder.unit(Type::Unit, origin.clone()).unwrap();
                builder
                    .application(callable, unit, domain.as_ref().clone(), origin.clone())
                    .unwrap()
            }
            _ => panic!("fixture operand"),
        };
        let instance = EffectInstance::new(symbol.effect(), Box::new([]));
        let request = builder
            .request(
                instance.clone(),
                symbol.operation(),
                operand,
                result.as_ref().clone(),
                EffectRow::singleton(instance.clone()),
                origin.clone(),
            )
            .unwrap();
        let root = builder
            .native_interpret(
                request,
                Box::new([NativeInterpretation::new(instance, Arc::clone(symbol))]),
                result.as_ref().clone(),
                EffectRow::empty(),
                origin,
            )
            .unwrap();
        builder.finish(root).unwrap()
    }

    fn program_with_unordered_instances(&self) -> UnvalidatedEffectProgram {
        let mut program = self.program(false);
        let root = program.root.index().unwrap();
        let EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) =
            &mut program.nodes[root].kind
        else {
            panic!("boundary");
        };
        boundary.interpretations = Box::new([
            NativeInterpretation::new(self.instance(true), Arc::clone(&self.stop)),
            NativeInterpretation::new(
                EffectInstance::new(self.bytes.effect(), Box::new([])),
                Arc::clone(&self.bytes),
            ),
            NativeInterpretation::new(self.instance(false), Arc::clone(&self.make)),
        ]);
        program
    }

    fn validate(
        &self,
        program: UnvalidatedEffectProgram,
    ) -> Result<ValidatedEffectProgram, super::ValidationError> {
        let sources: Vec<_> = self
            .graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect();
        let modules: Vec<_> = self
            .graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect();
        validate_effect_modules_with_work(
            program,
            &sources,
            &modules,
            &mut TypeWorkBudget::default(),
        )
    }

    fn donor(&self) -> Arc<CheckedForeignSymbol> {
        let mut work = TypeWorkBudget::default();
        let context = ForeignBindingContext::new(&self.registry);
        Arc::new(
            bind_foreign_symbol(
                self.make.library(),
                Arc::clone(self.make.prepared()),
                self.make.symbol_index(),
                self.registry.effect(self.make.effect()).unwrap(),
                &context,
                &mut work,
            )
            .unwrap(),
        )
    }
}

#[test]
fn native_interpret_accepts_address_bytes_and_void_and_revalidates_transform() {
    let fixture = Fixture::new();
    for (program, symbol) in [
        (fixture.program(false), &fixture.make),
        (fixture.program(true), &fixture.stop),
        (fixture.program_for(&fixture.echo), &fixture.echo),
        (fixture.program_for(&fixture.bytes), &fixture.bytes),
        (fixture.program_with_unordered_instances(), &fixture.stop),
    ] {
        let checked = fixture.validate(program).unwrap();
        let EffectExprKind::Operation(EffectOperation::NativeInterpret(original)) =
            &checked.node(checked.root()).unwrap().kind
        else {
            panic!("validated boundary retained");
        };
        let rebuilt = transform::identity_effect_traversal(&checked).unwrap();
        let EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) =
            &rebuilt.nodes[rebuilt.root.index().unwrap()].kind
        else {
            panic!("boundary retained");
        };
        assert!(Arc::ptr_eq(boundary.interpretations()[0].symbol(), symbol));
        assert_eq!(
            original.interpretations().len(),
            boundary.interpretations().len()
        );
        for (before, after) in original
            .interpretations()
            .iter()
            .zip(boundary.interpretations())
        {
            assert_eq!(before.effect(), after.effect());
            assert!(Arc::ptr_eq(before.symbol(), after.symbol()));
        }
        fixture.validate(rebuilt).unwrap();
    }
}

#[test]
fn native_interpret_requires_original_registered_declarations() {
    let fixture = Fixture::new();
    fixture
        .validate(fixture.program(false))
        .expect("original declarations independently admit the native boundary");
    let incomplete = fixture.program_with_checked_declarations(false, false);
    assert!(!Arc::ptr_eq(&incomplete.registry, &fixture.registry));
    assert!(
        fixture.validate(incomplete).is_err(),
        "a checked symbol cannot authorize a forest without its original registry declarations"
    );
}

#[test]
fn native_bindings_require_exact_symbols_and_unique_registration() {
    use crate::foreign::source_runtime::{
        NativeArgument, NativeCallError, NativeReply, SourceNativeBindings,
        admit_source_native_program,
    };
    fn callback(arguments: &[NativeArgument]) -> Result<NativeReply, NativeCallError> {
        if !arguments.is_empty() {
            return Err(NativeCallError);
        }
        Ok(NativeReply::Address(core::ptr::null_mut()))
    }
    let fixture = Fixture::new();
    let program = fixture.validate(fixture.program(false)).unwrap();
    let mut bindings = SourceNativeBindings::default();
    assert!(
        bindings
            .insert(
                Arc::clone(&fixture.make),
                callback,
                &mut TypeWorkBudget::with_limit(0)
            )
            .is_err()
    );
    assert!(
        bindings.invoke(&fixture.make, &[]).is_err(),
        "refused registration leaves no callback"
    );
    bindings
        .insert(
            Arc::clone(&fixture.make),
            callback,
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
    assert!(
        bindings
            .insert(
                Arc::clone(&fixture.make),
                callback,
                &mut TypeWorkBudget::default()
            )
            .is_err()
    );
    assert_eq!(
        bindings.invoke(&fixture.make, &[]).unwrap(),
        NativeReply::Address(core::ptr::null_mut())
    );
    assert!(bindings.invoke(&fixture.donor(), &[]).is_err());
    admit_source_native_program(&program, &bindings, &mut TypeWorkBudget::default()).unwrap();
    let mut foreign = SourceNativeBindings::default();
    foreign
        .insert(fixture.donor(), callback, &mut TypeWorkBudget::default())
        .unwrap();
    assert!(
        admit_source_native_program(&program, &foreign, &mut TypeWorkBudget::default()).is_err()
    );
}

#[derive(Clone, Copy, Debug)]
enum Mutation {
    Ordinary,
    OtherSymbol,
    SameOperationDonor,
    Duplicate,
    MissingInterpretation,
    ExtraActual,
    WrongTag,
    WrongKind,
    UnboundType,
    UnboundRow,
    ForeignBody,
    CyclicBody,
    WrongResult,
    HiddenBodyRow,
    UnlistedRow,
    MalformedRow,
}

#[test]
fn native_interpret_independently_rejects_malformed_sets_actuals_and_rows() {
    let fixture = Fixture::new();
    let donor = fixture.donor();
    assert_eq!(donor.operation(), fixture.make.operation());
    assert!(!Arc::ptr_eq(&donor, &fixture.make));
    for mutation in [
        Mutation::Ordinary,
        Mutation::OtherSymbol,
        Mutation::SameOperationDonor,
        Mutation::Duplicate,
        Mutation::MissingInterpretation,
        Mutation::ExtraActual,
        Mutation::WrongTag,
        Mutation::WrongKind,
        Mutation::UnboundType,
        Mutation::UnboundRow,
        Mutation::ForeignBody,
        Mutation::CyclicBody,
        Mutation::WrongResult,
        Mutation::HiddenBodyRow,
        Mutation::UnlistedRow,
        Mutation::MalformedRow,
    ] {
        let mut program = fixture.program(false);
        let root = program.root.index().unwrap();
        let EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) =
            &mut program.nodes[root].kind
        else {
            panic!("boundary");
        };
        match mutation {
            Mutation::Ordinary => {
                boundary.interpretations[0].effect = EffectInstance::new_kinded(
                    fixture.ordinary,
                    Box::new([
                        KindedArgument::RowArg(EffectRow::empty()),
                        KindedArgument::TypeArg(Type::Int),
                    ]),
                )
            }
            Mutation::OtherSymbol => boundary.interpretations[0].symbol = Arc::clone(&fixture.stop),
            Mutation::SameOperationDonor => boundary.interpretations[0].symbol = Arc::clone(&donor),
            Mutation::Duplicate => {
                boundary.interpretations = Box::new([
                    NativeInterpretation::new(fixture.instance(false), Arc::clone(&fixture.make)),
                    NativeInterpretation::new(fixture.instance(true), Arc::clone(&fixture.stop)),
                    NativeInterpretation::new(fixture.instance(false), Arc::clone(&fixture.make)),
                ])
            }
            Mutation::MissingInterpretation => boundary.interpretations = Box::new([]),
            Mutation::ExtraActual => {
                boundary.interpretations[0].effect =
                    EffectInstance::new(fixture.make.effect(), Box::new([Type::Int]));
            }
            Mutation::WrongTag => {
                boundary.interpretations[0].effect = EffectInstance::new_kinded(
                    fixture.make.effect(),
                    Box::new([KindedArgument::RowArg(EffectRow::empty())]),
                );
            }
            Mutation::WrongKind | Mutation::UnboundType => {
                let actual = if matches!(mutation, Mutation::WrongKind) {
                    fixture
                        .registry
                        .effect(fixture.ordinary)
                        .unwrap()
                        .parameters[0]
                        .id
                } else {
                    TypeVariableId::generated(0)
                };
                boundary.interpretations[0].effect =
                    EffectInstance::new(fixture.make.effect(), Box::new([Type::Variable(actual)]));
            }
            Mutation::UnboundRow => {
                boundary.interpretations[0].effect = EffectInstance::new_kinded(
                    fixture.make.effect(),
                    Box::new([KindedArgument::RowArg(EffectRow::open(
                        crate::types::EffectRowVariable::Rigid(TypeVariableId::generated(1)),
                        Box::new([]),
                    ))]),
                );
            }
            Mutation::ForeignBody => boundary.body = fixture.program(true).root,
            Mutation::CyclicBody => boundary.body = program.root,
            Mutation::WrongResult => program.nodes[root].ty = Type::Unit,
            Mutation::HiddenBodyRow => {
                let body = boundary.body.index().unwrap();
                program.nodes[body].effects = EffectRow::empty();
            }
            Mutation::UnlistedRow => boundary.interpretations = Box::new([]),
            Mutation::MalformedRow => {
                program.nodes[root].effects = EffectRow::open(
                    crate::types::EffectRowVariable::Inference(
                        crate::types::InferenceVariableId::new(0),
                    ),
                    Box::new([]),
                );
            }
        }
        assert!(fixture.validate(program).is_err(), "{mutation:?}");
    }
}

#[test]
fn native_interpret_full_validation_has_exact_one_short_and_fresh_work_cuts() {
    let fixture = Fixture::new();
    // Finalizer payload admission must debit the same phase ledger as its
    // staging, including failed operations, rather than the builder allowance.
    let entry = || {
        let span = fixture
            .graph
            .module(fixture.graph.entry())
            .unwrap()
            .source()
            .span(crate::source::ByteRange::new(0, 1).unwrap())
            .unwrap();
        let origin = Origin::Source(span);
        let report = Type::Unit;
        let mut builder = EffectCoreBuilder::with_effect_registry(Arc::clone(&fixture.registry));
        let operand = builder.unit(Type::Unit, origin.clone()).unwrap();
        let request = builder
            .request(
                fixture.instance(true),
                fixture.stop.operation(),
                operand,
                report,
                EffectRow::singleton(fixture.instance(true)),
                origin,
            )
            .unwrap();
        (builder, request, span)
    };
    let (mut builder, body, span) = entry();
    let builder_work = builder.type_work.used();
    let mut measured_entry = TypeWorkBudget::default();
    assert!(
        builder
            .prepare_owner_free_native_entry(body, span, &mut measured_entry)
            .is_ok()
    );
    assert_eq!(
        builder.type_work.used(),
        builder_work,
        "finalization must borrow the caller ledger"
    );
    let entry_cost = measured_entry.used();
    assert!(entry_cost > 0);
    for limit in [entry_cost - 1, entry_cost] {
        for _ in 0..2 {
            let (mut builder, body, span) = entry();
            let builder_work = builder.type_work.used();
            let mut work = TypeWorkBudget::with_limit(limit);
            let result = builder.prepare_owner_free_native_entry(body, span, &mut work);
            assert_eq!(
                builder.type_work.used(),
                builder_work,
                "success and failure must return the caller ledger"
            );
            if limit == entry_cost {
                assert!(result.is_ok());
                assert_eq!(work.used(), entry_cost);
            } else {
                assert!(matches!(
                    result,
                    Err(crate::core::effect::NativeEntryBuildFailure::Build(
                        crate::core::BuildError::TypeWorkExceeded
                    ))
                ));
            }
        }
    }
    let sources: Vec<_> = fixture
        .graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect();
    let modules: Vec<_> = fixture
        .graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect();
    for program in [
        fixture.program(false),
        fixture.program_with_unordered_instances(),
    ] {
        let mut measured = TypeWorkBudget::default();
        check_ordinary_effect_modules_with_budget_for_test(
            &program,
            &sources,
            &modules,
            &mut measured,
        )
        .unwrap();
        let cost = measured.used();
        assert!(cost > 0);
        for limit in [cost - 1, cost] {
            for _ in 0..2 {
                let mut work = TypeWorkBudget::with_limit(limit);
                let result = check_ordinary_effect_modules_with_budget_for_test(
                    &program, &sources, &modules, &mut work,
                );
                if limit == cost {
                    result.unwrap();
                    assert_eq!(work.used(), cost);
                } else {
                    assert_eq!(
                        result.unwrap_err().reason(),
                        super::ValidationReason::Resource
                    );
                }
            }
        }
    }
}

#[test]
fn native_interpret_subtracts_only_listed_exact_instances() {
    let fixture = Fixture::new();
    let other = || fixture.instance(true);
    let ordinary = || {
        EffectInstance::new_kinded(
            fixture.ordinary,
            Box::new([
                KindedArgument::RowArg(EffectRow::empty()),
                KindedArgument::TypeArg(Type::Int),
            ]),
        )
    };
    let body = EffectRow::closed(Box::new([fixture.instance(false), other(), ordinary()]));
    let set = [NativeInterpretation::new(
        fixture.instance(false),
        Arc::clone(&fixture.make),
    )];
    let outward = crate::core::effect::native_interpret_outward_row(
        &body,
        &set,
        &mut TypeWorkBudget::default(),
    )
    .unwrap();
    assert_eq!(outward, EffectRow::closed(Box::new([other(), ordinary()])));
    let unused = [NativeInterpretation::new(
        EffectInstance::new(fixture.echo.effect(), Box::new([])),
        Arc::clone(&fixture.echo),
    )];
    assert_eq!(
        crate::core::effect::native_interpret_outward_row(
            &body,
            &unused,
            &mut TypeWorkBudget::default()
        )
        .unwrap(),
        body
    );
}
