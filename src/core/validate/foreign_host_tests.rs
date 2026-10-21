use super::*;
use crate::core::effect::{EffectExprKind, EffectOperation, ForeignHostIdentity};
use crate::types::{EffectId, TypeVariableId};

const SCALAR: &str = r#"import @builtin.foreign as Foreign
foreign checked library C {
    profile "x86_64-unknown-linux-gnu"
    repr I32 = signed(32)
    symbol Abs<H> : Int -> Foreign.CheckedCall<Int> {
        name "abs"
        abi (I32) -> I32
        host H
        assumes { }
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
}
main : Unit -> Foreign.CheckedCall<Int>
main () = foreign host H {
    perform Abs<H>.call 1
}
"#;

pub(super) fn original(
    text: &str,
) -> (
    crate::core::UnvalidatedEffectProgram,
    crate::module::ModuleGraph,
) {
    original_profile(text, true)
}

fn original_profile(
    text: &str,
    checked_profile: bool,
) -> (
    crate::core::UnvalidatedEffectProgram,
    crate::module::ModuleGraph,
) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-core-host-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let entry = directory.join("entry.ash");
    std::fs::write(&entry, text).unwrap();
    let graph =
        crate::module::load_module_graph(&entry, &crate::module::ModuleRoots::empty()).unwrap();
    std::fs::remove_dir_all(directory).unwrap();
    let mut checked: Vec<crate::resolved::CheckedModule> = Vec::new();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                crate::resolve::DependencyExports::new(
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
        let resolved = if checked_profile {
            crate::resolve::resolve_checked_foreign_module(loaded, &dependencies)
        } else {
            crate::resolve::resolve_module(loaded, &dependencies)
        }
        .unwrap();
        checked.push(crate::elaborate::check_module(resolved).unwrap());
    }
    let linked = crate::elaborate::link_modules(checked, graph.entry()).unwrap();
    let linked = crate::evidence_validation::validate_interface_evidence(linked).unwrap();
    let mut elaborator = crate::elaborate::EffectElaborator::for_module_program(&linked).unwrap();
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .unwrap();
    (elaborator.finish(typed.node).unwrap(), graph)
}

fn reason(
    core: &crate::core::UnvalidatedEffectProgram,
    graph: &crate::module::ModuleGraph,
    limit: Option<usize>,
) -> (Option<ValidationReason>, usize) {
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let mut validator = Validator::new_modules(core, &sources, &modules).unwrap();
    if let Some(limit) = limit {
        validator.type_work_limit = limit;
    }
    let failure = validator.run_effect().err().map(|error| error.reason());
    (failure, validator.type_work.get())
}

#[test]
fn checked_host_core_actual_scalar_is_exact_bounded_and_retryable() {
    let (core, graph) = original(SCALAR);
    let (failure, work) = reason(&core, &graph, None);
    assert_eq!(failure, None);
    assert_eq!(reason(&core, &graph, Some(work)).0, None);
    assert_eq!(
        reason(&core, &graph, Some(work - 1)).0,
        Some(ValidationReason::Resource)
    );
    assert_eq!(reason(&core, &graph, Some(work)).0, None);
}

#[test]
fn checked_host_core_rejects_removed_mode_and_independent_host_vector_mutations() {
    let (core, graph) = original(SCALAR);
    assert_eq!(reason(&core, &graph, None).0, None);
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let validated = crate::core::validate_effect_modules(core, &sources, &modules).unwrap();
    for change in 0..5 {
        let mut changed = crate::core::transform::identity_effect_traversal(&validated).unwrap();
        let boundary = changed
            .nodes
            .iter_mut()
            .find_map(|node| match &mut node.kind {
                EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary))
                    if boundary.host().is_some() =>
                {
                    Some(boundary)
                }
                _ => None,
            })
            .unwrap();
        let host = boundary.host.unwrap();
        match change {
            0 => boundary.host = None,
            1 => {
                boundary.host = Some(ForeignHostIdentity {
                    identity: TypeVariableId::new(900_001),
                    ..host
                })
            }
            2 => {
                boundary.host = Some(ForeignHostIdentity {
                    effect: EffectId::new(host.effect().module(), 1),
                    ..host
                })
            }
            3 => boundary.interpretations = Box::new([]),
            4 => {
                boundary.interpretations[0].effect = EffectInstance::new(
                    boundary.interpretations[0].effect.effect(),
                    Box::new([Type::Int]),
                )
            }
            _ => unreachable!(),
        }
        assert!(
            reason(&changed, &graph, None).0.is_some(),
            "host mutation {change}"
        );
    }
}

#[test]
fn checked_host_core_rejects_return_only_handler_for_sealed_zero_operation_effect() {
    let (core, graph) = original(SCALAR);
    assert_eq!(reason(&core, &graph, None).0, None);
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let validated = crate::core::validate_effect_modules(core, &sources, &modules).unwrap();
    let mut changed = crate::core::transform::identity_effect_traversal(&validated).unwrap();
    let index = changed.nodes.iter().position(|node| matches!(&node.kind,
        EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) if boundary.host().is_some())).unwrap();
    let EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) =
        &changed.nodes[index].kind
    else {
        unreachable!()
    };
    let host = boundary.host.unwrap();
    let body = boundary.body();
    let instance = EffectInstance::new(host.effect(), Box::new([Type::Variable(host.identity())]));
    let child = &changed.nodes[body.index().unwrap()];
    let row = child
        .effects
        .remove_exact_with_budget(&instance, &mut TypeWorkBudget::default())
        .unwrap()
        .unwrap();
    let node = StoredNode {
        dialect: child.dialect,
        ty: child.ty.clone(),
        effects: row,
        origin: child.origin.clone(),
        kind: EffectExprKind::Operation(EffectOperation::Handler(crate::core::HandlerNode::new(
            crate::core::HandlerId::new(900_002),
            body,
            instance,
            Vec::new(),
        ))),
    };
    let handler = node_id(changed.arena, changed.nodes.len()).unwrap();
    changed.nodes.push(node);
    let EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) =
        &mut changed.nodes[index].kind
    else {
        unreachable!()
    };
    boundary.body = handler;
    assert_eq!(
        reason(&changed, &graph, None).0,
        Some(ValidationReason::ResourceEscape),
        "the otherwise typed zero-clause handler has no host elimination authority"
    );
}

#[test]
fn checked_host_core_scope_rejects_a_host_dependent_child_shared_outside_its_binder() {
    let (core, graph) = original(SCALAR);
    assert_eq!(reason(&core, &graph, None).0, None);
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let validated = crate::core::validate_effect_modules(core, &sources, &modules).unwrap();
    for outside in [false, true] {
        let mut changed = crate::core::transform::identity_effect_traversal(&validated).unwrap();
        let child = if outside {
            let index = changed
                .nodes
                .iter()
                .position(|node| {
                    matches!(
                        &node.kind,
                        EffectExprKind::Operation(EffectOperation::Request(_))
                    )
                })
                .unwrap();
            node_id(changed.arena, index).unwrap()
        } else {
            changed.root
        };
        let root = &changed.nodes[changed.root.index().unwrap()];
        let right = &changed.nodes[child.index().unwrap()];
        let row = root
            .effects
            .union_with_budget(&right.effects, &mut TypeWorkBudget::default())
            .unwrap()
            .unwrap();
        let node = StoredNode {
            dialect: root.dialect,
            ty: Type::Tuple(vec![root.ty.clone(), right.ty.clone()].into_boxed_slice()),
            effects: row,
            origin: root.origin.clone(),
            kind: EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Tuple(
                crate::core::TupleNode::new(vec![changed.root, child]),
            ))),
        };
        let new_root = node_id(changed.arena, changed.nodes.len()).unwrap();
        changed.nodes.push(node);
        changed.root = new_root;
        let validator = Validator::new_modules(&changed, &sources, &modules).unwrap();
        validator.validate_graph().unwrap();
        let scope = validator.validate_type_scopes();
        if outside {
            assert!(
                scope.is_err(),
                "a global ownership census cannot authorize the sibling edge"
            );
            assert!(reason(&changed, &graph, None).0.is_some());
        } else {
            scope.expect("sharing an independently closed host remains scoped");
            assert_eq!(reason(&changed, &graph, None).0, None);
        }
    }
}

#[test]
fn checked_host_core_forged_mode_cannot_upgrade_a_valid_legacy_interpretation() {
    let header = SCALAR[..SCALAR.find("main :").unwrap()]
        .replace("foreign checked library", "foreign library")
        .replace("Foreign.CheckedCall", "Foreign.Call")
        .replace("        host H\n", "")
        .replace("        assumes { }\n", "");
    let text = format!(
        "{header}main : Unit -> Foreign.Call<Int> ! {{Abs<Unit>}}\nmain () = perform Abs<Unit>.call 1\n"
    );
    let (mut core, graph) = original_profile(&text, false);
    let root = &core.nodes[core.root.index().unwrap()];
    let interpretations = root
        .effects
        .known()
        .iter()
        .map(|instance| {
            let symbol = core
                .registry
                .native_symbol(crate::types::OperationId::new(instance.effect(), 0))
                .unwrap();
            crate::core::NativeInterpretation::new(instance.clone(), Arc::clone(symbol))
        })
        .collect::<Vec<_>>();
    assert_eq!(interpretations.len(), 1);
    let boundary =
        crate::core::NativeInterpretNode::new(core.root, interpretations.into_boxed_slice());
    let node = StoredNode {
        dialect: root.dialect,
        ty: root.ty.clone(),
        effects: EffectRow::empty(),
        origin: root.origin.clone(),
        kind: EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)),
    };
    core.root = node_id(core.arena, core.nodes.len()).unwrap();
    core.nodes.push(node);
    assert_eq!(
        reason(&core, &graph, None).0,
        None,
        "the legacy None-mode control must validate"
    );
    let host_effect = core
        .registry
        .effects()
        .iter()
        .find(|effect| effect.id.module().is_builtin_foreign())
        .unwrap()
        .id;
    let EffectExprKind::Operation(EffectOperation::NativeInterpret(boundary)) =
        &mut core.nodes[core.root.index().unwrap()].kind
    else {
        unreachable!()
    };
    boundary.host = Some(ForeignHostIdentity {
        identity: TypeVariableId::new(900_010),
        effect: host_effect,
    });
    assert_eq!(
        reason(&core, &graph, None).0,
        Some(ValidationReason::Registry),
        "Some mode cannot attest a legacy contract"
    );
}
