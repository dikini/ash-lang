//! Independent reconstruction of worker entry bodies.

#[cfg(test)]
use super::node_id;
use super::{
    AuthenticatedNativeRegistry, NetworkLinkedSpine, ScopeFamily, ValidationError,
    ValidationReason, Validator,
};
use crate::{
    core::{
        dialect::{CoreOperationFamily, NodeId, PureComputation, PureExprKind, PureValue},
        effect::{EffectOperationFamily, NetworkScopeNode},
    },
    resolved::BinderId,
    types::{Kind, OperationId, Type, TypeWorkBudget},
};
use std::collections::{HashMap, HashSet};

pub(super) struct WorkerEntryFact {
    pub(super) binder: crate::resolved::BinderId,
    pub(super) parameter: crate::types::TypeVariableId,
    pub(super) native_effects: Vec<crate::types::EffectInstance>,
}

pub(super) struct NetworkBodyFacts {
    pub(super) linked_result: crate::core::dialect::NodeId,
    pub(super) entries: [WorkerEntryFact; 2],
}

// This pass is a conservative precursor to full worker admission. Whole-graph,
// type, effect, scope and capture validation must also succeed before use.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Visit {
    Evaluate,
    Body,
    Called,
}

pub(super) fn check_entry_bodies(
    validator: &Validator<'_, '_, EffectOperationFamily>,
    id: NodeId,
    network: &NetworkScopeNode,
    spine: &NetworkLinkedSpine,
    native: &AuthenticatedNativeRegistry<'_>,
) -> Result<NetworkBodyFacts, ValidationError> {
    use crate::core::effect::{EffectExprKind, EffectOperation};
    let invalid = || ValidationError::new(ValidationReason::Registry, Some(id));
    let resource = || ValidationError::new(ValidationReason::Resource, Some(id));
    if !matches!(&validator.node(id)?.kind, EffectExprKind::Operation(EffectOperation::Network(actual)) if std::ptr::eq(actual.as_ref(), network))
        || network.linked_result != Some(spine.result)
        || !std::ptr::eq(native.registry, validator.program.registry.as_ref())
        || spine.bindings.len() != spine.initializers.len()
    {
        return Err(invalid());
    }
    let api =
        crate::resolved::NetworkApi::for_module(network.acquisition.builtin).ok_or_else(invalid)?;
    let EffectExprKind::Operation(EffectOperation::Region(root)) =
        &validator.node(spine.entry_region)?.kind
    else {
        return Err(invalid());
    };
    if !root.entry {
        return Err(invalid());
    }

    validator.charge_type_work(spine.bindings.len())?;
    let mut definitions = HashMap::new();
    definitions
        .try_reserve(spine.bindings.len())
        .map_err(|_| resource())?;
    for (&(binder, initializer), &expected) in spine.bindings.iter().zip(&spine.initializers) {
        if initializer != expected || definitions.insert(binder, initializer).is_some() {
            return Err(invalid());
        }
    }
    let mut local_binders = HashSet::new();
    validator.charge_type_work(1)?;
    local_binders.try_reserve(1).map_err(|_| resource())?;
    local_binders.insert(root.access.id());
    let mut uses = Vec::new();
    let mut pending = Vec::new();
    let mut visited = HashSet::new();
    validator.charge_type_work(spine.initializers.len().saturating_add(2))?;
    pending
        .try_reserve(spine.initializers.len().saturating_add(2))
        .map_err(|_| resource())?;
    pending.extend(
        spine
            .initializers
            .iter()
            .copied()
            .map(|node| (node, Visit::Evaluate)),
    );
    for entry in spine.entries {
        pending.push((entry.ok_or_else(invalid)?, Visit::Called));
    }

    while let Some((node_id, mode)) = pending.pop() {
        validator.charge_type_work(1)?;
        if visited.contains(&(node_id, mode)) {
            continue;
        }
        visited.try_reserve(1).map_err(|_| resource())?;
        visited.insert((node_id, mode));
        let node = validator.node(node_id)?;
        // Selection reconstruction requires its actual implementation and
        // prerequisites. Do not treat an evidence anchor as a callable proof.
        validator.charge_type_work(validator.program.method_evidence_anchors.len())?;
        if validator
            .program
            .method_evidence_anchors
            .iter()
            .any(|anchor| anchor.node == node_id)
        {
            return Err(invalid());
        }
        let mut add_binder = |binder: BinderId| -> Result<(), ValidationError> {
            validator.charge_type_work(1)?;
            local_binders.try_reserve(1).map_err(|_| resource())?;
            local_binders.insert(binder);
            Ok(())
        };
        match &node.kind {
            EffectExprKind::Pure(PureExprKind::Variable(variable)) => {
                validator.charge_type_work(1)?;
                uses.try_reserve(1).map_err(|_| resource())?;
                uses.push(variable.binder());
                if mode == Visit::Called {
                    let target = definitions
                        .get(&variable.binder())
                        .copied()
                        .ok_or_else(invalid)?;
                    validator.charge_type_work(1)?;
                    pending.try_reserve(1).map_err(|_| resource())?;
                    pending.push((target, Visit::Called));
                }
            }
            EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) => {
                add_binder(function.parameter().id())?;
            }
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding))) => {
                add_binder(binding.binder().id())?;
                validator.charge_type_work(1)?;
                definitions.try_reserve(1).map_err(|_| resource())?;
                if definitions
                    .insert(binding.binder().id(), binding.initializer())
                    .is_some_and(|previous| previous != binding.initializer())
                {
                    return Err(invalid());
                }
            }
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::RecursiveBind(
                group,
            ))) => {
                for member in group.members() {
                    add_binder(member.binder().id())?;
                    validator.charge_type_work(1)?;
                    definitions.try_reserve(1).map_err(|_| resource())?;
                    if definitions
                        .insert(member.binder().id(), member.initializer())
                        .is_some_and(|previous| previous != member.initializer())
                    {
                        return Err(invalid());
                    }
                }
            }
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(branch))) => {
                for arm in branch.arms() {
                    for binder in arm.pattern().binder_iter() {
                        add_binder(binder.id())?;
                    }
                }
            }
            EffectExprKind::Operation(
                EffectOperation::NativeInterpret(_) | EffectOperation::Network(_),
            ) => return Err(invalid()),
            _ => {}
        }
        let count = EffectOperationFamily::child_count(&node.kind);
        validator.charge_type_work(count)?;
        pending.try_reserve(count).map_err(|_| resource())?;
        for index in 0..count {
            let child = EffectOperationFamily::child_at(&node.kind, index).ok_or_else(invalid)?;
            let mut binder_error = None;
            EffectOperationFamily::visit_operation_child_binders(
                &node.kind,
                index,
                &mut |binder| {
                    if binder_error.is_none() {
                        binder_error = add_binder(binder).err();
                    }
                },
            );
            if let Some(error) = binder_error {
                return Err(error);
            }
            let child_mode = match &node.kind {
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(_))) => {
                    if mode == Visit::Evaluate {
                        continue;
                    } else {
                        Visit::Body
                    }
                }
                EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) => {
                    if index == closure.captures.len() + 2 {
                        if mode == Visit::Evaluate {
                            continue;
                        } else {
                            Visit::Body
                        }
                    } else if mode == Visit::Called {
                        Visit::Evaluate
                    } else {
                        mode
                    }
                }
                EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(_))) => {
                    if mode == Visit::Called {
                        return Err(invalid());
                    }
                    if index == 0 { Visit::Called } else { mode }
                }
                EffectExprKind::Pure(PureExprKind::Computation(
                    PureComputation::TypeApplication(_),
                )) => {
                    if mode == Visit::Called {
                        Visit::Called
                    } else {
                        mode
                    }
                }
                EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(_))) => {
                    if mode == Visit::Called && index == 1 {
                        Visit::Called
                    } else if mode == Visit::Called {
                        Visit::Evaluate
                    } else {
                        mode
                    }
                }
                EffectExprKind::Pure(PureExprKind::Computation(
                    PureComputation::TypeAbstraction(_),
                )) => mode,
                _ if mode == Visit::Called => return Err(invalid()),
                _ => mode,
            };
            pending.push((child, child_mode));
        }
    }
    validator.charge_type_work(uses.len())?;
    if uses
        .iter()
        .any(|binder| !local_binders.contains(binder) && !definitions.contains_key(binder))
    {
        return Err(invalid());
    }

    let mut entries = Vec::new();
    validator.charge_type_work(2)?;
    entries.try_reserve_exact(2).map_err(|_| resource())?;
    for slot in 0..2 {
        let initializer = spine.entries[slot].ok_or_else(invalid)?;
        if definitions.get(&network.entries[slot]) != Some(&initializer) {
            return Err(invalid());
        }
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
            abstraction,
        ))) = &validator.node(initializer)?.kind
        else {
            return Err(invalid());
        };
        let [(parameter, Kind::Type)] = abstraction.parameters() else {
            return Err(invalid());
        };
        let Type::Forall(parameters, ty) = &validator.node(initializer)?.ty else {
            return Err(invalid());
        };
        if !matches!(parameters.as_ref(), [(id, Kind::Type)] if id == parameter) {
            return Err(invalid());
        }
        let function = ty.function_view().ok_or_else(invalid)?;
        let mut native_effects = Vec::new();
        let mut rows = Vec::new();
        validator.charge_type_work(spine.initializers.len().saturating_add(1))?;
        rows.try_reserve(spine.initializers.len().saturating_add(1))
            .map_err(|_| resource())?;
        if let Some(row) = function.effects() {
            rows.push(row);
        }
        for initializer in &spine.initializers {
            rows.push(&validator.node(*initializer)?.effects);
        }
        for row in rows {
            if row.tail().is_some() {
                return Err(invalid());
            }
            validator.charge_type_work(row.known().len())?;
            for instance in row.known() {
                let effect = instance.effect();
                if crate::resolved::RegionApi::for_module(effect.module()).is_some_and(|region| {
                    region.default_alloc() == effect && instance.arguments().is_empty()
                }) {
                    continue;
                }
                if effect == api.io()
                    && matches!(instance.arguments(), [crate::types::KindedArgument::TypeArg(Type::Variable(identity))] if *identity == *parameter)
                {
                    continue;
                }
                let operation = OperationId::new(effect, 0);
                let symbol = native
                    .registry
                    .native_symbol(operation)
                    .ok_or_else(invalid)?;
                let declaration = native.registry.effect(effect).ok_or_else(invalid)?;
                validator.charge_type_work(3)?;
                if symbol.effect() != effect
                    || symbol.operation() != operation
                    || !matches!(declaration.operations.as_ref(), [item] if item.id == operation)
                    || !declaration
                        .native_contract
                        .as_ref()
                        .is_some_and(|original| std::sync::Arc::ptr_eq(original, symbol))
                {
                    return Err(invalid());
                }
                let mut budget = TypeWorkBudget::with_limit(
                    validator
                        .type_work_limit
                        .saturating_sub(validator.type_work.get()),
                );
                let copy = crate::types::clone_effect_instance_with_budget(instance, &mut budget);
                validator.charge_type_work(budget.used())?;
                let copy = copy.map_err(|()| resource())?;
                validator.charge_type_work(1)?;
                native_effects.try_reserve(1).map_err(|_| resource())?;
                native_effects.push(copy);
            }
        }
        entries.push(WorkerEntryFact {
            binder: network.entries[slot],
            parameter: *parameter,
            native_effects,
        });
    }
    let entries: [WorkerEntryFact; 2] = entries.try_into().map_err(|_| invalid())?;
    Ok(NetworkBodyFacts {
        linked_result: spine.result,
        entries,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        core::effect::{EffectExprKind, EffectOperation},
        elaborate::{check_module, link_modules},
        module::{ModuleRoots, load_module_graph},
        resolve::{DependencyExports, resolve_module},
        resolved::CheckedModule,
        validate_linked_facts_for_test,
    };

    #[test]
    fn admits_actual_entries_while_main_has_an_unrelated_handler() {
        let directory =
            std::env::temp_dir().join(format!("ash-network-body-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let path = directory.join("entry.ash");
        std::fs::write(
            directory.join("helper.ash"),
            "pub ping : Unit -> Unit\nping ignored = ()\n",
        )
        .unwrap();
        std::fs::write(&path, "import @builtin.network as Network\nimport @builtin.bytes as ByteOps\nimport helper (ping)\n\
             start<N> : (Network.Worker<N>, Bytes) -> Unit ! {Network.IO<N>}\n\
             start ignored = ping ()\n\
             start2<M> : (Network.Worker<M>, Bytes) -> Unit ! {Network.IO<M>}\n\
             start2 ignored = ()\n\
             effect MainOnly {\nping : Unit -> Unit\n}\n\
             main : Unit -> Unit\nmain () = {\n\
             let _ = handle (perform MainOnly.ping ()) with MainOnly {\nping ignored => resume ()\n}\n\
             resource Network.Pair<N> pair = (1, start, start2, ByteOps.empty (), ByteOps.empty ()) {\n()\n}\n}\n").unwrap();
        let graph = load_module_graph(&path, &ModuleRoots::empty()).unwrap();
        let mut checked = Vec::new();
        for module in graph.modules() {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    let dependency = checked
                        .iter()
                        .find(|m: &&CheckedModule| m.module() == edge.target())
                        .unwrap();
                    DependencyExports::new(edge, dependency.exports()).unwrap()
                })
                .collect::<Vec<_>>();
            checked.push(check_module(resolve_module(module, &dependencies).unwrap()).unwrap());
        }
        let linked =
            validate_linked_facts_for_test(link_modules(checked, graph.entry()).unwrap()).unwrap();
        let mut elaborator =
            crate::elaborate::EffectElaborator::for_module_program(&linked).unwrap();
        let typed = elaborator
            .synthesize_effect_module_program(&linked)
            .unwrap();
        let mut program = elaborator.finish(typed.node).unwrap();
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let relation = graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect::<Vec<_>>();
        let mut validator = Validator::new_modules(&program, &sources, &relation).unwrap();
        validator.linked = Some(&linked);
        let (index, network) = program
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match &node.kind {
                EffectExprKind::Operation(EffectOperation::Network(network)) => {
                    Some((index, network))
                }
                _ => None,
            })
            .unwrap();
        let id = node_id(program.arena, index).unwrap();
        let mut spine = validator.check_network_linked_spine(id, network).unwrap();
        let native = AuthenticatedNativeRegistry {
            registry: program.registry.as_ref(),
        };
        let facts = check_entry_bodies(&validator, id, network, &spine, &native)
            .expect("worker entries should admit");
        assert_eq!(facts.entries[0].binder, network.entries[0]);
        assert_eq!(facts.linked_result, spine.result);
        assert!(facts.entries[0].native_effects.is_empty());
        assert_ne!(facts.entries[0].parameter, facts.entries[1].parameter);
        let other_parameter = facts.entries[1].parameter;
        let foreign_registry = crate::resolved::ResolvedRegistry::new(Vec::new(), Vec::new());
        let forged_native = AuthenticatedNativeRegistry {
            registry: &foreign_registry,
        };
        assert!(
            check_entry_bodies(&validator, id, network, &spine, &forged_native).is_err(),
            "a different registry cannot authenticate worker native services"
        );
        let mut measured = Validator::new_modules(&program, &sources, &relation).unwrap();
        measured.linked = Some(&linked);
        check_entry_bodies(&measured, id, network, &spine, &native).expect("measure body work");
        let exact = measured.type_work.get();
        let mut at_limit = Validator::new_modules(&program, &sources, &relation).unwrap();
        at_limit.linked = Some(&linked);
        at_limit.type_work_limit = exact;
        check_entry_bodies(&at_limit, id, network, &spine, &native).expect("exact work budget");
        let mut short = Validator::new_modules(&program, &sources, &relation).unwrap();
        short.linked = Some(&linked);
        short.type_work_limit = exact - 1;
        assert!(
            matches!(check_entry_bodies(&short, id, network, &spine, &native), Err(error) if error.reason() == ValidationReason::Resource)
        );
        let mut limited = Validator::new_modules(&program, &sources, &relation).unwrap();
        limited.linked = Some(&linked);
        limited.type_work_limit = 0;
        assert!(
            matches!(check_entry_bodies(&limited, id, network, &spine, &native), Err(error) if error.reason() == ValidationReason::Resource)
        );
        assert!(
            check_entry_bodies(&validator, network.capacity, network, &spine, &native).is_err(),
            "a different node cannot designate this network scope"
        );
        let original_result = spine.result;
        spine.result = network.capacity;
        assert!(
            check_entry_bodies(&validator, id, network, &spine, &native).is_err(),
            "a forged linked result cannot identify the worker program"
        );
        spine.result = original_result;
        let original_entry = spine.entries[0];
        spine.entries[0] = Some(network.capacity);
        assert!(
            check_entry_bodies(&validator, id, network, &spine, &native).is_err(),
            "a forged initializer must not name another node"
        );
        spine.entries[0] = original_entry;

        let caller_binder = network.handle.id();
        let entry = spine.entries[0].unwrap();
        let mut pending = vec![entry];
        let mut seen = HashSet::new();
        let context = loop {
            let node = pending.pop().expect("entry closure exists");
            if !seen.insert(node) {
                continue;
            }
            let kind = &program.nodes[node.index().unwrap()].kind;
            if let EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) = kind {
                break closure.context;
            }
            pending.extend(
                (0..EffectOperationFamily::child_count(kind))
                    .filter_map(|index| EffectOperationFamily::child_at(kind, index)),
            );
        };
        let _ = facts;
        let _ = limited;
        let _ = validator;
        let _ = native;
        let EffectExprKind::Pure(PureExprKind::Variable(variable)) =
            &mut program.nodes[context.index().unwrap()].kind
        else {
            panic!("closure context variable")
        };
        let original_context = *variable;
        *variable = crate::core::variable::VariableNode::new(caller_binder);
        let mut validator = Validator::new_modules(&program, &sources, &relation).unwrap();
        validator.linked = Some(&linked);
        let EffectExprKind::Operation(EffectOperation::Network(network)) =
            &program.nodes[index].kind
        else {
            unreachable!()
        };
        let native = AuthenticatedNativeRegistry {
            registry: program.registry.as_ref(),
        };
        assert!(
            check_entry_bodies(&validator, id, network, &spine, &native).is_err(),
            "a caller-owned handle must not enter the reconstructed closure"
        );
        let _ = validator;
        let EffectExprKind::Pure(PureExprKind::Variable(variable)) =
            &mut program.nodes[context.index().unwrap()].kind
        else {
            unreachable!()
        };
        *variable = original_context;
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
            abstraction,
        ))) = &mut program.nodes[entry.index().unwrap()].kind
        else {
            panic!("entry abstraction")
        };
        let body = abstraction.body();
        *abstraction = crate::core::type_ops::TypeAbstractionNode::new(
            vec![(other_parameter, Kind::Type)],
            body,
        );
        let mut validator = Validator::new_modules(&program, &sources, &relation).unwrap();
        validator.linked = Some(&linked);
        let EffectExprKind::Operation(EffectOperation::Network(network)) =
            &program.nodes[index].kind
        else {
            unreachable!()
        };
        let native = AuthenticatedNativeRegistry {
            registry: program.registry.as_ref(),
        };
        assert!(
            check_entry_bodies(&validator, id, network, &spine, &native).is_err(),
            "a forged entry type parameter must not be admitted"
        );
        let _ = std::fs::remove_dir_all(directory);
    }
}
