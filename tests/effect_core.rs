use std::sync::Arc;

use ash::{
    core::{
        CoreMatchArm, CorePattern, CorePatternKind, EffectClause, EffectCoreBuilder,
        EffectExprKind, EffectOperation, HandlerId, Primitive, ResumeUse, ValidationReason,
        transform::{fold_effect_literal_primitives, identity_effect_traversal},
        validate_effect, validate_effect_modules,
    },
    driver::{RunConfiguration, run_path},
    elaborate::{EffectElaborator, check_module, link_modules},
    evidence_validation::validate_interface_evidence,
    integer::Integer,
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::{CheckedModule, ResolvedRegistry, ResumeId},
    source::{ByteRange, Origin, SourceFile},
    types::{ComputationType, EffectId, EffectInstance, EffectRow, OperationId, Type},
};

fn check_graph(graph: &ModuleGraph) -> Vec<CheckedModule> {
    let mut checked = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|dependency: &&CheckedModule| dependency.module() == edge.target())
                    .expect("effect dependencies should precede their importer");
                DependencyExports::new(edge, dependency.exports())
                    .expect("effect dependency summary should authenticate")
            })
            .collect::<Vec<_>>();
        checked.push(
            check_module(resolve_module(module, &dependencies).expect("module should resolve"))
                .expect("module should check"),
        );
    }
    checked
}

fn checked_registry() -> (Arc<ResolvedRegistry>, SourceFile, EffectId, OperationId) {
    let text = "effect Cell {\nread : Unit -> Int\n}\n\nmain : Unit -> Int\nmain () = handle (perform Cell.read ()) with Cell {\nread ignored => resume 42\n}\n";
    let path = std::env::temp_dir().join(format!(
        "ash-effect-core-{}-{}.ash",
        std::process::id(),
        SourceFile::new("identity", "")
            .expect("source identity")
            .id()
            .value()
    ));
    std::fs::write(&path, text).expect("effect Core fixture should be writable");
    let graph = load_module_graph(&path, &ModuleRoots::empty()).expect("fixture should load");
    let module = graph
        .module(graph.entry())
        .expect("entry module should remain loaded");
    let source = module.source().clone();
    let checked = check_module(resolve_module(module, &[]).expect("fixture should resolve"))
        .expect("fixture should check");
    let registry = Arc::clone(checked.registry());
    let effect = checked.effects()[0].id;
    let operation = checked.effects()[0].operations[0].id;
    let _ = std::fs::remove_file(path);
    (registry, source, effect, operation)
}

#[test]
fn effect_abstraction_rejects_unproved_aggregate_and_handled_computation() {
    use ash::types::{Kind, TypeVariableId};
    let (registry, source, effect, operation) = checked_registry();
    let origin = Origin::Source(source.span(ByteRange::new(0, 6).unwrap()).unwrap());
    for handled in [false, true] {
        let mut builder = EffectCoreBuilder::with_effect_registry(Arc::clone(&registry));
        let unit = builder.unit(Type::Unit, origin.clone()).unwrap();
        let (body, ty) = if handled {
            let instance = EffectInstance::new(effect, Box::new([]));
            let request = builder
                .request(
                    instance.clone(),
                    operation,
                    unit,
                    Type::Int,
                    EffectRow::singleton(instance.clone()),
                    origin.clone(),
                )
                .unwrap();
            let answer = builder
                .integer(
                    Integer::parse_decimal("42").unwrap(),
                    Type::Int,
                    origin.clone(),
                )
                .unwrap();
            let resume = builder
                .resume(
                    HandlerId::new(0),
                    ResumeId::new(0),
                    ResumeUse::Consumed,
                    answer,
                    Type::Int,
                    EffectRow::empty(),
                    origin.clone(),
                )
                .unwrap();
            let clause = EffectClause::new(
                operation,
                ResumeId::new(0),
                CoreMatchArm::new(
                    CorePattern::new(Type::Unit, origin.clone(), CorePatternKind::Wildcard),
                    resume,
                    origin.clone(),
                ),
            );
            (
                builder
                    .handler(
                        HandlerId::new(0),
                        request,
                        instance,
                        vec![clause],
                        Type::Int,
                        EffectRow::empty(),
                        origin.clone(),
                    )
                    .unwrap(),
                Type::Int,
            )
        } else {
            let ty = Type::Tuple(Box::new([Type::Unit, Type::Unit]));
            (
                builder
                    .tuple(vec![unit, unit], ty.clone(), origin.clone())
                    .unwrap(),
                ty,
            )
        };
        let parameter = TypeVariableId::generated(900);
        let abstraction = builder
            .type_abstraction(
                vec![(parameter, Kind::Type)],
                body,
                Type::Forall(Box::new([(parameter, Kind::Type)]), Box::new(ty)),
                origin.clone(),
            )
            .unwrap();
        let error = validate_effect(builder.finish(abstraction).unwrap(), &[&source])
            .expect_err("an empty effect row does not prove inert construction");
        assert_eq!(error.reason(), ValidationReason::TypeOperation);
    }
}

#[test]
fn discard_core_checks_owners_types_rows_and_exact_once_before_safety() {
    let (registry, source, effect, operation) = checked_registry();
    let origin = Origin::Source(source.span(ByteRange::new(0, 6).unwrap()).unwrap());
    for (case, expected) in [
        ("canonical", None),
        ("wrong-owner", Some(ValidationReason::Resume)),
        ("wrong-handler", Some(ValidationReason::Resume)),
        ("available", Some(ValidationReason::Resume)),
        ("wrong-type", Some(ValidationReason::Resume)),
        ("wrong-row", Some(ValidationReason::Resume)),
        ("double", Some(ValidationReason::Resume)),
        ("outside", Some(ValidationReason::Resume)),
        ("closure", Some(ValidationReason::Resume)),
    ] {
        let mut builder = EffectCoreBuilder::with_effect_registry(Arc::clone(&registry));
        let instance = EffectInstance::new(effect, Box::new([]));
        let discard_type = if case == "wrong-type" {
            Type::Bool
        } else {
            Type::Unit
        };
        let discard = builder
            .discard(
                HandlerId::new(u32::from(case == "wrong-handler")),
                ResumeId::new(u32::from(case == "wrong-owner")),
                if case == "available" {
                    ResumeUse::Available
                } else {
                    ResumeUse::Consumed
                },
                discard_type.clone(),
                if case == "wrong-row" {
                    EffectRow::singleton(instance.clone())
                } else {
                    EffectRow::empty()
                },
                origin.clone(),
            )
            .expect("discard carrier");
        let root = if case == "outside" {
            discard
        } else {
            let operand = builder.unit(Type::Unit, origin.clone()).unwrap();
            let requested = builder
                .request(
                    instance.clone(),
                    operation,
                    operand,
                    Type::Int,
                    EffectRow::singleton(instance.clone()),
                    origin.clone(),
                )
                .unwrap();
            let result = builder
                .integer(
                    Integer::parse_decimal("42").unwrap(),
                    Type::Int,
                    origin.clone(),
                )
                .unwrap();
            let (initializer, initializer_type) = if case == "closure" {
                let parameter = builder.binder(Type::Unit, origin.clone()).unwrap();
                let ty = Type::Function(Box::new(Type::Unit), Box::new(Type::Unit));
                (
                    builder
                        .function(parameter, discard, ty.clone(), origin.clone())
                        .unwrap(),
                    ty,
                )
            } else {
                (discard, discard_type)
            };
            let binder = builder.binder(initializer_type, origin.clone()).unwrap();
            let mut body = builder
                .binding(binder, initializer, result, Type::Int, origin.clone())
                .unwrap();
            if case == "double" {
                let binder = builder.binder(Type::Unit, origin.clone()).unwrap();
                body = builder
                    .binding(binder, discard, body, Type::Int, origin.clone())
                    .unwrap();
            }
            let clause = EffectClause::new(
                operation,
                ResumeId::new(0),
                CoreMatchArm::new(
                    CorePattern::new(Type::Unit, origin.clone(), CorePatternKind::Wildcard),
                    body,
                    origin.clone(),
                ),
            );
            builder
                .handler(
                    HandlerId::new(0),
                    requested,
                    instance,
                    vec![clause],
                    Type::Int,
                    if case == "wrong-row" {
                        EffectRow::singleton(EffectInstance::new(effect, Box::new([])))
                    } else {
                        EffectRow::empty()
                    },
                    origin.clone(),
                )
                .unwrap()
        };
        let result = validate_effect(builder.finish(root).unwrap(), &[&source]);
        let Some(expected) = expected else {
            result.expect("direct captured segment is discardable");
            continue;
        };
        let error = result.expect_err("discard requires structural validity and capture proof");
        assert_eq!(error.reason(), expected, "{case}: {error:?}");
    }
}

#[test]
fn checked_source_lowers_to_explicit_effect_core() {
    let directory = std::env::temp_dir().join(format!(
        "ash-effect-core-lowering-{}-{}",
        std::process::id(),
        SourceFile::new("lowering-identity", "")
            .expect("source identity")
            .id()
            .value()
    ));
    std::fs::create_dir(&directory).expect("effect Core fixture directory should be writable");
    let base = directory.join("base.ash");
    let facade = directory.join("facade.ash");
    let path = directory.join("entry.ash");
    std::fs::write(
        &base,
        concat!(
            "pub type Option<A> =\nNone\n| Some(A)\n\n",
            "pub effect Build<F : Type -> Type> {\nmake : (Int, Int) -> F<Int>\n}\n\n",
        ),
    )
    .expect("effect API fixture should be writable");
    std::fs::write(&facade, "pub import base (Option, None, Some, Build)\n")
        .expect("effect facade fixture should be writable");
    std::fs::write(
        &path,
        concat!(
            "import facade (Option, None, Some, Build)\n\n",
            "interface Identity<A> {\nidentity : A -> A\n}\n\n",
            "impl Identity<Int> {\nidentity value = value\n}\n\n",
            "relay<R : EffectRow, A> : (Unit -> A ! { | R }) -> A ! { | R }\n",
            "relay action = action ()\n\n",
            "build_action : Unit -> Option<Int> ! {Build<Option>}\n",
            "build_action () = perform Build<Option>.make (identity 40, 2)\n\n",
            "build : Unit -> Option<Int> ! {Build<Option>}\n",
            "build () = relay(build_action)\n\n",
            "main : Unit -> Option<Int>\n",
            "main () = handle (build ()) with Build<Option> {\n",
            "make (left, right) => {\n",
            "let resumed = resume Some(left + right)\n",
            "resumed\n}\n}\n",
        ),
    )
    .expect("effect Core fixture should be writable");
    let graph = load_module_graph(&path, &ModuleRoots::empty()).expect("fixture should load");
    let checked = check_graph(&graph);
    let effect = checked
        .iter()
        .find_map(|module| module.effects().first().map(|effect| effect.id))
        .expect("fixture should retain its effect declaration");
    let linked = link_modules(checked, graph.entry()).expect("fixture should link");
    assert!(linked.registry().effect(effect).is_some());
    let linked = validate_interface_evidence(linked).expect("evidence should authenticate");
    let mut elaborator =
        EffectElaborator::for_module_program(&linked).expect("builder should start");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("checked effects should lower");
    let unchecked = elaborator
        .finish(typed.node)
        .expect("effect arena should finish");
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let module_sources = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let program = validate_effect_modules(unchecked, &sources, &module_sources)
        .expect("lowered effect Core should validate with its module relation");
    let program = validate_effect_modules(
        identity_effect_traversal(&program).expect("row-aware identity transform"),
        &sources,
        &module_sources,
    )
    .expect("row-aware identity output should revalidate");
    let program = validate_effect_modules(
        fold_effect_literal_primitives(&program).expect("row-aware fold transform"),
        &sources,
        &module_sources,
    )
    .expect("row-aware fold output should revalidate");
    let mut pending = vec![program.root()];
    let mut seen = std::collections::HashSet::new();
    let mut operations = [0_usize; 3];
    while let Some(id) = pending.pop() {
        if !seen.insert(id) {
            continue;
        }
        let node = program.node(id).expect("reachable effect Core node");
        if let EffectExprKind::Operation(operation) = &node.kind {
            match operation {
                EffectOperation::Request(_) => operations[0] += 1,
                EffectOperation::Handler(_) => operations[1] += 1,
                EffectOperation::Resume(_) => operations[2] += 1,
                EffectOperation::Discard(_) => panic!("resume-only fixture cannot contain discard"),
                EffectOperation::Resource(_) => {
                    panic!("resume-only fixture cannot contain resource")
                }
                EffectOperation::Registration(_) => {
                    panic!("resume-only fixture cannot contain registration")
                }
                EffectOperation::Cleanup(_) => panic!("resume-only fixture cannot contain cleanup"),
            }
        }
        pending.extend((0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)));
    }
    assert_eq!(operations, [1, 1, 1]);
    let observation = run_path(RunConfiguration {
        entry: path.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("effect Core should execute through the shared machine");
    assert_eq!(observation.value_display(), "Some(42)");
    std::fs::write(
        &path,
        "import facade (Build)\n\nmain : Unit -> Int\nmain () = 42\n",
    )
    .expect("locality fixture should be writable");
    assert_eq!(
        run_path(RunConfiguration {
            entry: path,
            roots: ModuleRoots::empty(),
        })
        .expect("an unused effect declaration must stay on the pure path")
        .value_display(),
        "42"
    );
    let type_only = directory.join("type-only.ash");
    std::fs::write(
        &type_only,
        concat!(
            "import facade (Option, Build)\n\n",
            "interface Consumer<A> {\n",
            "accept : (Unit -> A ! {Build<Option>}) -> Unit\n",
            "}\n\n",
            "main : Unit -> Int\nmain () = 42\n",
        ),
    )
    .expect("type-only effect pressure fixture should be writable");
    assert_eq!(
        run_path(RunConfiguration {
            entry: type_only,
            roots: ModuleRoots::empty(),
        })
        .expect("type-only effect pressure must select executable Effect Core")
        .value_display(),
        "42"
    );
    let _ = std::fs::remove_dir_all(directory);
}

#[derive(Clone, Copy)]
struct Corruption {
    effect: EffectId,
    operation: OperationId,
    request_input_has_effect: bool,
    handler_output_has_effect: bool,
    resume_owner: ResumeId,
    resume_use: ResumeUse,
    resume_handler: HandlerId,
    resume_result_is_bool: bool,
    resume_output_has_effect: bool,
    duplicate_outer_handler: bool,
    resume_shape: ResumeShape,
}

#[derive(Clone, Copy)]
enum ResumeShape {
    Direct,
    ClauseRequest,
    ClosureEscape,
    BranchZero,
    BranchTwo,
    SharedOutside,
    NestedResumeValue,
    NestedHandlerBody,
    NestedBoundary,
}

fn unchecked_program(
    registry: Arc<ResolvedRegistry>,
    source: &SourceFile,
    canonical_effect: EffectId,
    corruption: Corruption,
) -> ash::core::UnvalidatedEffectProgram {
    let end = u32::try_from(source.text().len()).expect("fixture length should fit");
    let origin = Origin::Source(
        source
            .span(ByteRange::new(0, end).expect("ordered range"))
            .expect("range should belong to source"),
    );
    let canonical_instance = EffectInstance::new(canonical_effect, Box::new([]));
    let claimed_instance = EffectInstance::new(corruption.effect, Box::new([]));
    let requested_row = if corruption.request_input_has_effect {
        EffectRow::empty()
    } else {
        EffectRow::singleton(claimed_instance.clone())
    };
    let handler_output = if corruption.handler_output_has_effect {
        EffectRow::singleton(canonical_instance.clone())
    } else {
        EffectRow::empty()
    };
    let handler = HandlerId::new(0);
    let owner = ResumeId::new(0);
    let mut builder = EffectCoreBuilder::with_effect_registry(registry);
    let operand = builder
        .unit(Type::Unit, origin.clone())
        .expect("unit operand");
    let request = builder
        .request(
            claimed_instance,
            corruption.operation,
            operand,
            Type::Int,
            requested_row.clone(),
            origin.clone(),
        )
        .expect("unchecked request");
    let parameter = builder
        .binder(Type::Unit, origin.clone())
        .expect("request binder");
    let function = builder
        .function(
            parameter,
            request,
            Type::function_computation(Type::Unit, ComputationType::new(Type::Int, requested_row)),
            origin.clone(),
        )
        .expect("effectful request function");
    let handled_body = builder
        .application(function, operand, Type::Int, origin.clone())
        .expect("effectful application");
    let resumed_left = builder
        .integer(
            Integer::parse_decimal("40").expect("integer literal"),
            Type::Int,
            origin.clone(),
        )
        .expect("left resume value");
    let resumed_right = builder
        .integer(
            Integer::parse_decimal("2").expect("integer literal"),
            Type::Int,
            origin.clone(),
        )
        .expect("right resume value");
    let resumed_value = builder
        .primitive(
            Primitive::Add,
            resumed_left,
            resumed_right,
            Type::Int,
            origin.clone(),
        )
        .expect("resume value");
    let resume_value = if matches!(corruption.resume_shape, ResumeShape::NestedResumeValue) {
        builder
            .resume(
                corruption.resume_handler,
                corruption.resume_owner,
                corruption.resume_use,
                resumed_value,
                Type::Int,
                handler_output.clone(),
                origin.clone(),
            )
            .expect("nested resume value")
    } else {
        resumed_value
    };
    let resume_effects = if corruption.resume_output_has_effect {
        EffectRow::singleton(canonical_instance.clone())
    } else {
        handler_output.clone()
    };
    let resume = builder
        .resume(
            corruption.resume_handler,
            corruption.resume_owner,
            corruption.resume_use,
            resume_value,
            if corruption.resume_result_is_bool {
                Type::Bool
            } else {
                Type::Int
            },
            resume_effects,
            origin.clone(),
        )
        .expect("unchecked resume");
    let clause_body = match corruption.resume_shape {
        ResumeShape::Direct | ResumeShape::SharedOutside | ResumeShape::NestedResumeValue => resume,
        ResumeShape::ClauseRequest => {
            let sequencing = builder
                .binder(Type::Int, origin.clone())
                .expect("clause request sequencing binder");
            builder
                .binding(sequencing, handled_body, resume, Type::Int, origin.clone())
                .expect("clause request before resume")
        }
        ResumeShape::ClosureEscape => {
            let parameter = builder
                .binder(Type::Int, origin.clone())
                .expect("closure binder");
            let closure = builder
                .function(
                    parameter,
                    resume,
                    Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
                    origin.clone(),
                )
                .expect("escaping closure");
            let ignored = builder
                .binder(
                    Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
                    origin.clone(),
                )
                .expect("closure binding");
            let result = builder
                .integer(
                    Integer::parse_decimal("0").unwrap(),
                    Type::Int,
                    origin.clone(),
                )
                .unwrap();
            builder
                .binding(ignored, closure, result, Type::Int, origin.clone())
                .unwrap()
        }
        ResumeShape::BranchZero => {
            let scrutinee = builder.boolean(true, Type::Bool, origin.clone()).unwrap();
            let zero = builder
                .integer(
                    Integer::parse_decimal("0").unwrap(),
                    Type::Int,
                    origin.clone(),
                )
                .unwrap();
            let arms = vec![
                CoreMatchArm::new(
                    CorePattern::new(Type::Bool, origin.clone(), CorePatternKind::Boolean(true)),
                    resume,
                    origin.clone(),
                ),
                CoreMatchArm::new(
                    CorePattern::new(Type::Bool, origin.clone(), CorePatternKind::Boolean(false)),
                    zero,
                    origin.clone(),
                ),
            ];
            builder
                .match_expression(scrutinee, arms, Type::Int, origin.clone())
                .unwrap()
        }
        ResumeShape::BranchTwo => {
            let first = builder
                .binder(Type::Int, origin.clone())
                .expect("resume binding");
            builder
                .binding(first, resume, resume, Type::Int, origin.clone())
                .unwrap()
        }
        ResumeShape::NestedHandlerBody => {
            let sequencing = builder
                .binder(Type::Int, origin.clone())
                .expect("inner body sequencing binder");
            let inner_handled_body = builder
                .binding(sequencing, handled_body, resume, Type::Int, origin.clone())
                .expect("outer resume in nested handler body");
            let inner_value = builder
                .integer(
                    Integer::parse_decimal("42").unwrap(),
                    Type::Int,
                    origin.clone(),
                )
                .unwrap();
            let inner_resume = builder
                .resume(
                    HandlerId::new(1),
                    ResumeId::new(1),
                    ResumeUse::Consumed,
                    inner_value,
                    Type::Int,
                    EffectRow::empty(),
                    origin.clone(),
                )
                .unwrap();
            let inner_clause = EffectClause::new(
                corruption.operation,
                ResumeId::new(1),
                CoreMatchArm::new(
                    CorePattern::new(Type::Unit, origin.clone(), CorePatternKind::Wildcard),
                    inner_resume,
                    origin.clone(),
                ),
            );
            builder
                .handler(
                    HandlerId::new(1),
                    inner_handled_body,
                    canonical_instance.clone(),
                    vec![inner_clause],
                    Type::Int,
                    EffectRow::empty(),
                    origin.clone(),
                )
                .unwrap()
        }
        ResumeShape::NestedBoundary => {
            let inner_resume = builder
                .resume(
                    HandlerId::new(1),
                    ResumeId::new(1),
                    ResumeUse::Consumed,
                    resumed_value,
                    Type::Int,
                    EffectRow::empty(),
                    origin.clone(),
                )
                .unwrap();
            let ignored = builder
                .binder(Type::Int, origin.clone())
                .expect("outer resume binding");
            let inner_body = builder
                .binding(ignored, resume, inner_resume, Type::Int, origin.clone())
                .unwrap();
            let inner_clause = EffectClause::new(
                corruption.operation,
                ResumeId::new(1),
                CoreMatchArm::new(
                    CorePattern::new(Type::Unit, origin.clone(), CorePatternKind::Wildcard),
                    inner_body,
                    origin.clone(),
                ),
            );
            builder
                .handler(
                    HandlerId::new(1),
                    handled_body,
                    canonical_instance.clone(),
                    vec![inner_clause],
                    Type::Int,
                    EffectRow::empty(),
                    origin.clone(),
                )
                .unwrap()
        }
    };
    let clause = EffectClause::new(
        corruption.operation,
        owner,
        CoreMatchArm::new(
            CorePattern::new(Type::Unit, origin.clone(), CorePatternKind::Wildcard),
            clause_body,
            origin.clone(),
        ),
    );
    let inner = builder
        .handler(
            handler,
            handled_body,
            canonical_instance.clone(),
            vec![clause],
            Type::Int,
            handler_output,
            origin.clone(),
        )
        .expect("unchecked handler");
    let root = if corruption.handler_output_has_effect {
        let outer_value = builder
            .integer(
                Integer::parse_decimal("42").expect("outer resume value"),
                Type::Int,
                origin.clone(),
            )
            .expect("outer resume value node");
        let outer_resume = builder
            .resume(
                if corruption.duplicate_outer_handler {
                    HandlerId::new(0)
                } else {
                    HandlerId::new(1)
                },
                ResumeId::new(1),
                ResumeUse::Consumed,
                outer_value,
                Type::Int,
                EffectRow::empty(),
                origin.clone(),
            )
            .expect("outer resume");
        let outer_clause = EffectClause::new(
            corruption.operation,
            ResumeId::new(1),
            CoreMatchArm::new(
                CorePattern::new(Type::Unit, origin.clone(), CorePatternKind::Wildcard),
                outer_resume,
                origin.clone(),
            ),
        );
        builder
            .handler(
                HandlerId::new(1),
                inner,
                canonical_instance,
                vec![outer_clause],
                Type::Int,
                EffectRow::empty(),
                origin,
            )
            .expect("outer handler")
    } else if matches!(corruption.resume_shape, ResumeShape::SharedOutside) {
        let binder = builder
            .binder(Type::Int, origin.clone())
            .expect("shared resume binder");
        builder
            .binding(binder, inner, resume, Type::Int, origin)
            .expect("resume shared inside and outside its clause")
    } else {
        inner
    };
    builder.finish(root).expect("effect Core root")
}

#[test]
fn effect_core_rejects_forged_handler_row_and_resume_owner() {
    let (registry, source, effect, operation) = checked_registry();
    let canonical = Corruption {
        effect,
        operation,
        request_input_has_effect: false,
        handler_output_has_effect: false,
        resume_owner: ResumeId::new(0),
        resume_use: ResumeUse::Consumed,
        resume_handler: HandlerId::new(0),
        resume_result_is_bool: false,
        resume_output_has_effect: false,
        duplicate_outer_handler: false,
        resume_shape: ResumeShape::Direct,
    };

    validate_effect(
        unchecked_program(Arc::clone(&registry), &source, effect, canonical),
        &[&source],
    )
    .expect("canonical effect Core should validate");

    let error = validate_effect(
        unchecked_program(
            Arc::clone(&registry),
            &source,
            effect,
            Corruption {
                handler_output_has_effect: true,
                ..canonical
            },
        ),
        &[&source],
    )
    .expect_err("a stored resume row cannot justify its handler output");
    assert_eq!(error.reason(), ValidationReason::EffectRow);

    validate_effect(
        unchecked_program(
            Arc::clone(&registry),
            &source,
            effect,
            Corruption {
                handler_output_has_effect: true,
                resume_shape: ResumeShape::ClauseRequest,
                ..canonical
            },
        ),
        &[&source],
    )
    .expect("a clause may directly introduce its handler output effect");

    let foreign_effect = EffectId::new(effect.module(), effect.declaration() + 1);
    let corruptions = [
        Corruption {
            effect: foreign_effect,
            ..canonical
        },
        Corruption {
            operation: OperationId::new(effect, operation.operation() + 1),
            ..canonical
        },
        Corruption {
            request_input_has_effect: true,
            ..canonical
        },
        Corruption {
            resume_owner: ResumeId::new(1),
            ..canonical
        },
        Corruption {
            resume_use: ResumeUse::Available,
            ..canonical
        },
        Corruption {
            resume_handler: HandlerId::new(1),
            ..canonical
        },
        Corruption {
            resume_result_is_bool: true,
            ..canonical
        },
        Corruption {
            resume_output_has_effect: true,
            ..canonical
        },
        Corruption {
            handler_output_has_effect: true,
            duplicate_outer_handler: true,
            ..canonical
        },
    ];
    for corrupted in corruptions {
        let error = validate_effect(
            unchecked_program(Arc::clone(&registry), &source, effect, corrupted),
            &[&source],
        )
        .expect_err("each independent effect Core corruption should be rejected");
        assert!(matches!(
            error.reason(),
            ValidationReason::EffectIdentity
                | ValidationReason::EffectRow
                | ValidationReason::Resume
                | ValidationReason::Handler
        ));
    }
}

#[test]
fn effect_core_rejects_resume_escape_and_path_multiplicity() {
    let (registry, source, effect, operation) = checked_registry();
    for resume_shape in [
        ResumeShape::ClosureEscape,
        ResumeShape::BranchZero,
        ResumeShape::BranchTwo,
        ResumeShape::SharedOutside,
        ResumeShape::NestedResumeValue,
        ResumeShape::NestedBoundary,
    ] {
        let corrupted = Corruption {
            effect,
            operation,
            request_input_has_effect: false,
            handler_output_has_effect: false,
            resume_owner: ResumeId::new(0),
            resume_use: ResumeUse::Consumed,
            resume_handler: HandlerId::new(0),
            resume_result_is_bool: false,
            resume_output_has_effect: false,
            duplicate_outer_handler: false,
            resume_shape,
        };
        let error = validate_effect(
            unchecked_program(Arc::clone(&registry), &source, effect, corrupted),
            &[&source],
        )
        .expect_err("resume must be exactly once on every path and cannot escape");
        assert_eq!(error.reason(), ValidationReason::Resume);
    }

    validate_effect(
        unchecked_program(
            registry,
            &source,
            effect,
            Corruption {
                effect,
                operation,
                request_input_has_effect: false,
                handler_output_has_effect: false,
                resume_owner: ResumeId::new(0),
                resume_use: ResumeUse::Consumed,
                resume_handler: HandlerId::new(0),
                resume_result_is_bool: false,
                resume_output_has_effect: false,
                duplicate_outer_handler: false,
                resume_shape: ResumeShape::NestedHandlerBody,
            },
        ),
        &[&source],
    )
    .expect("an outer resume remains available in a nested handler body");
}

#[test]
fn effect_core_transforms_revalidate_and_unfinished_arenas_dispose_iteratively() {
    let (registry, source, effect, operation) = checked_registry();
    let canonical = Corruption {
        effect,
        operation,
        request_input_has_effect: false,
        handler_output_has_effect: false,
        resume_owner: ResumeId::new(0),
        resume_use: ResumeUse::Consumed,
        resume_handler: HandlerId::new(0),
        resume_result_is_bool: false,
        resume_output_has_effect: false,
        duplicate_outer_handler: false,
        resume_shape: ResumeShape::Direct,
    };
    let validated = validate_effect(
        unchecked_program(Arc::clone(&registry), &source, effect, canonical),
        &[&source],
    )
    .expect("canonical effect Core should validate");
    let identity = validate_effect(
        identity_effect_traversal(&validated).expect("identity transform"),
        &[&source],
    )
    .expect("identity-transformed effect Core should revalidate");
    let folded = validate_effect(
        fold_effect_literal_primitives(&identity).expect("fold transform"),
        &[&source],
    )
    .expect("fold-transformed effect Core should revalidate");
    assert!(folded.node_count() < identity.node_count());

    std::thread::Builder::new()
        .name("effect-core-iterative-disposal".to_owned())
        .stack_size(64 * 1024)
        .spawn(move || {
            let end = u32::try_from(source.text().len()).expect("fixture length should fit");
            let origin = Origin::Source(
                source
                    .span(ByteRange::new(0, end).expect("ordered range"))
                    .expect("range should belong to source"),
            );
            let mut builder = EffectCoreBuilder::with_effect_registry(registry);
            for _ in 0..32_768 {
                builder
                    .unit(Type::Unit, origin.clone())
                    .expect("unfinished effect node");
            }
            drop(builder);
        })
        .expect("disposal thread should start")
        .join()
        .expect("wide unfinished arena should dispose on a small stack");
}
