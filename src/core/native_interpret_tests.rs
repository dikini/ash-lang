//! Independent admission regressions for the owner-free Core boundary.

use std::{
    path::PathBuf,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

use super::{
    check_ordinary_effect_modules_with_budget_for_test, validate_effect_modules_with_work,
};
use crate::{
    core::{
        EffectCoreBuilder, EffectExprKind, EffectOperation, NativeInterpretation,
        UnvalidatedEffectProgram, ValidatedEffectProgram, transform,
    },
    foreign::checked_source::{CheckedForeignSymbol, ForeignBindingContext, bind_foreign_symbol},
    integer::Integer,
    interface::InterfaceConstraintBudget,
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::{CheckedModule, ResolvedRegistry},
    source::Origin,
    types::{EffectId, EffectInstance, EffectRow, KindedArgument, Type, TypeWorkBudget},
};

const SOURCE: &str = r#"import @builtin.foreign as Foreign
pub foreign library C {
    profile "x86_64-unknown-linux-gnu"
    repr CInt = signed(32)
    symbol Abs<Before : EffectRow, T, After : EffectRow> : Int -> Foreign.Call<Int> {
        name "abs"
        abi (CInt) -> CInt
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol Stop : Unit -> Foreign.Call<Unit> {
        name "stop"
        abi () -> void
        outcome otherwise {}
    }
}
pub effect Ordinary {
    call : Int -> Int
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
    scalar: Arc<CheckedForeignSymbol>,
    stop: Arc<CheckedForeignSymbol>,
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
        let scalar = Arc::clone(
            exports
                .effect("Abs")
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
        let ordinary = exports.effect("Ordinary").unwrap().id;
        let registry = Arc::new(
            ResolvedRegistry::combine_checked(
                &checked,
                &mut TypeWorkBudget::default(),
                &mut InterfaceConstraintBudget::default(),
            )
            .unwrap(),
        );
        Self {
            graph,
            registry,
            scalar,
            stop,
            ordinary,
        }
    }

    fn instance(&self, unit: bool) -> EffectInstance {
        if unit {
            return EffectInstance::new(self.stop.effect(), Box::new([]));
        }
        EffectInstance::new_kinded(
            self.scalar.effect(),
            Box::new([
                KindedArgument::RowArg(EffectRow::empty()),
                KindedArgument::TypeArg(Type::Int),
                KindedArgument::RowArg(EffectRow::empty()),
            ]),
        )
    }

    fn program(&self, unit: bool) -> UnvalidatedEffectProgram {
        let symbol = if unit { &self.stop } else { &self.scalar };
        let origin = Origin::Source(
            self.graph
                .module(self.graph.entry())
                .unwrap()
                .source()
                .span(crate::source::ByteRange::new(0, 1).unwrap())
                .unwrap(),
        );
        let report = Type::Application(
            Box::new(Type::Nominal(symbol.call_codec().ids().call)),
            Box::new(if unit { Type::Unit } else { Type::Int }),
        );
        let mut builder = EffectCoreBuilder::with_effect_registry(Arc::clone(&self.registry));
        // The imported common module now also defines two sealed generic byte
        // declarations. Keep their actual globals in this independently built
        // forest so every retained original parameter row remains consumed.
        let declarations = self
            .registry
            .scalar_preflights()
            .filter_map(|(_, fact)| {
                fact.role()
                    .byte_parameter(fact.module())
                    .map(|parameter| (fact, parameter))
            })
            .collect::<Vec<_>>();
        builder
            .reserve_resolved_binders(declarations.iter().map(|(fact, _)| fact.function()))
            .unwrap();
        let mut members = Vec::new();
        for (fact, parameter) in declarations {
            let operation = match fact.role() {
                crate::foreign::scalar_preflight::ForeignScalarPreflightRole::ByteRead => {
                    crate::core::packed::Intrinsic::ForeignByteRead {
                        function: fact.function(),
                    }
                }
                crate::foreign::scalar_preflight::ForeignScalarPreflightRole::ByteWrite => {
                    crate::core::packed::Intrinsic::ForeignByteWrite {
                        function: fact.function(),
                    }
                }
                _ => unreachable!(),
            };
            let intrinsic = builder
                .intrinsic(
                    operation,
                    fact.module(),
                    fact.signature().clone(),
                    fact.origin().clone(),
                )
                .unwrap();
            let abstracted = builder
                .type_abstraction(
                    vec![(parameter, crate::types::Kind::Type)],
                    intrinsic,
                    fact.core_signature().clone(),
                    fact.origin().clone(),
                )
                .unwrap();
            let binder = builder
                .resolved_binder(
                    fact.function(),
                    fact.core_signature().clone(),
                    fact.origin().clone(),
                )
                .unwrap();
            members.push((binder, abstracted));
        }
        let operand = if unit {
            builder.unit(Type::Unit, origin.clone()).unwrap()
        } else {
            builder
                .integer(
                    Integer::parse_decimal("1").unwrap(),
                    Type::Int,
                    origin.clone(),
                )
                .unwrap()
        };
        let operand = builder
            .recursive_binding(
                members,
                operand,
                if unit { Type::Unit } else { Type::Int },
                origin.clone(),
            )
            .unwrap();
        let request = builder
            .request(
                self.instance(unit),
                symbol.operation(),
                operand,
                report.clone(),
                EffectRow::singleton(self.instance(unit)),
                origin.clone(),
            )
            .unwrap();
        let root = builder
            .native_interpret(
                request,
                Box::new([NativeInterpretation::new(
                    self.instance(unit),
                    Arc::clone(symbol),
                )]),
                report,
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
        let other = |ty| {
            NativeInterpretation::new(
                EffectInstance::new_kinded(
                    self.scalar.effect(),
                    Box::new([
                        KindedArgument::RowArg(EffectRow::empty()),
                        KindedArgument::TypeArg(ty),
                        KindedArgument::RowArg(EffectRow::empty()),
                    ]),
                ),
                Arc::clone(&self.scalar),
            )
        };
        boundary.interpretations = Box::new([
            NativeInterpretation::new(self.instance(true), Arc::clone(&self.stop)),
            other(Type::Unit),
            other(Type::Int),
            other(Type::Bool),
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
        let codec = self.scalar.call_codec();
        let mut work = TypeWorkBudget::default();
        let context = ForeignBindingContext::new(
            &self.registry,
            codec.module(),
            codec.source(),
            codec.ids(),
            &mut work,
        )
        .unwrap();
        Arc::new(
            bind_foreign_symbol(
                self.scalar.library(),
                Arc::clone(self.scalar.prepared()),
                self.scalar.symbol_index(),
                self.registry.effect(self.scalar.effect()).unwrap(),
                &context,
                &mut work,
            )
            .unwrap(),
        )
    }
}

#[test]
fn native_interpret_accepts_scalar_and_zero_argument_void_and_revalidates_transform() {
    let fixture = Fixture::new();
    for (program, symbol) in [
        (fixture.program(false), &fixture.scalar),
        (fixture.program(true), &fixture.stop),
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

#[derive(Clone, Copy, Debug)]
enum Mutation {
    Ordinary,
    OtherSymbol,
    SameOperationDonor,
    Duplicate,
    MissingActual,
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
    assert_eq!(donor.operation(), fixture.scalar.operation());
    assert!(!Arc::ptr_eq(&donor, &fixture.scalar));
    for mutation in [
        Mutation::Ordinary,
        Mutation::OtherSymbol,
        Mutation::SameOperationDonor,
        Mutation::Duplicate,
        Mutation::MissingActual,
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
                boundary.interpretations[0].effect =
                    EffectInstance::new(fixture.ordinary, Box::new([]))
            }
            Mutation::OtherSymbol => boundary.interpretations[0].symbol = Arc::clone(&fixture.stop),
            Mutation::SameOperationDonor => boundary.interpretations[0].symbol = Arc::clone(&donor),
            Mutation::Duplicate => {
                boundary.interpretations = Box::new([
                    NativeInterpretation::new(fixture.instance(false), Arc::clone(&fixture.scalar)),
                    NativeInterpretation::new(fixture.instance(true), Arc::clone(&fixture.stop)),
                    NativeInterpretation::new(fixture.instance(false), Arc::clone(&fixture.scalar)),
                ])
            }
            Mutation::MissingActual => {
                boundary.interpretations[0].effect =
                    EffectInstance::new(fixture.scalar.effect(), Box::new([]))
            }
            Mutation::ExtraActual => {
                boundary.interpretations[0].effect = EffectInstance::new_kinded(
                    fixture.scalar.effect(),
                    Box::new([
                        KindedArgument::RowArg(EffectRow::empty()),
                        KindedArgument::TypeArg(Type::Int),
                        KindedArgument::RowArg(EffectRow::empty()),
                        KindedArgument::TypeArg(Type::Unit),
                    ]),
                );
            }
            Mutation::WrongTag => {
                boundary.interpretations[0].effect = EffectInstance::new_kinded(
                    fixture.scalar.effect(),
                    Box::new([
                        KindedArgument::TypeArg(Type::Int),
                        KindedArgument::TypeArg(Type::Int),
                        KindedArgument::RowArg(EffectRow::empty()),
                    ]),
                )
            }
            Mutation::WrongKind | Mutation::UnboundType => {
                let actual = if matches!(mutation, Mutation::WrongKind) {
                    Type::Nominal(fixture.scalar.call_codec().ids().call)
                } else {
                    Type::Variable(fixture.scalar.parameter_ids()[1])
                };
                boundary.interpretations[0].effect = EffectInstance::new_kinded(
                    fixture.scalar.effect(),
                    Box::new([
                        KindedArgument::RowArg(EffectRow::empty()),
                        KindedArgument::TypeArg(actual),
                        KindedArgument::RowArg(EffectRow::empty()),
                    ]),
                );
            }
            Mutation::UnboundRow => {
                boundary.interpretations[0].effect = EffectInstance::new_kinded(
                    fixture.scalar.effect(),
                    Box::new([
                        KindedArgument::RowArg(EffectRow::open(
                            crate::types::EffectRowVariable::Rigid(
                                fixture.scalar.parameter_ids()[0],
                            ),
                            Box::new([]),
                        )),
                        KindedArgument::TypeArg(Type::Int),
                        KindedArgument::RowArg(EffectRow::empty()),
                    ]),
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
        let report = Type::Application(
            Box::new(Type::Nominal(fixture.stop.call_codec().ids().call)),
            Box::new(Type::Unit),
        );
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
    let other = || {
        EffectInstance::new_kinded(
            fixture.scalar.effect(),
            Box::new([
                KindedArgument::RowArg(EffectRow::empty()),
                KindedArgument::TypeArg(Type::Bool),
                KindedArgument::RowArg(EffectRow::empty()),
            ]),
        )
    };
    let body = EffectRow::closed(Box::new([
        fixture.instance(false),
        other(),
        EffectInstance::new(fixture.ordinary, Box::new([])),
    ]));
    let set = [NativeInterpretation::new(
        fixture.instance(false),
        Arc::clone(&fixture.scalar),
    )];
    let outward = crate::core::effect::native_interpret_outward_row(
        &body,
        &set,
        &mut TypeWorkBudget::default(),
    )
    .unwrap();
    assert_eq!(
        outward,
        EffectRow::closed(Box::new([
            other(),
            EffectInstance::new(fixture.ordinary, Box::new([]))
        ]))
    );
    let unused = [NativeInterpretation::new(
        fixture.instance(true),
        Arc::clone(&fixture.stop),
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
