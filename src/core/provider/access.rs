//! Association checks for unpublished Core drafts. These borrowed header facts
//! are not descriptor certificates, native capabilities or runtime authority.

use super::{
    EffectExprKind, EffectOperation, HashMap, HashSet, NativeFacts, NodeId, TypeWorkBudget,
    UnvalidatedEffectProgram, ValidationError, ValidationReason, charge, invalid, node, resource,
    same_type_with_budget,
};
#[cfg(test)]
use super::{MethodId, PureComputation, PureExprKind, PureValue};
use crate::{
    resolved::ResourceDefinitionId,
    types::{
        IterativeTypeOwner, NominalTypeId, Type, TypeVariableId, clone_type_with_budget,
        discard_type_iteratively, same_effect_rows_with_budget, substitute_type_variables_with,
    },
};

#[derive(Clone, Copy)]
pub(crate) struct DraftStateAssociation<'a> {
    pub definition: ResourceDefinitionId,
    pub family: NominalTypeId,
    pub parameters: &'a [TypeVariableId],
    pub state: &'a Type,
}

#[cfg(test)]
#[derive(Clone, Copy)]
pub(crate) enum AccessMutation {
    Method,
    Definition,
    Arguments,
    Operand,
    Result,
    Effects,
    OtherEnclosing,
    Callable,
}

#[cfg(test)]
pub(crate) fn mutate_state_access(
    program: &mut UnvalidatedEffectProgram,
    mutation: AccessMutation,
) {
    let ordinal = program
        .nodes
        .iter()
        .position(|stored| {
            matches!(
                &stored.kind,
                EffectExprKind::Operation(EffectOperation::ProviderStateAccess(_))
            )
        })
        .unwrap();
    let EffectExprKind::Operation(EffectOperation::ProviderStateAccess(access)) =
        &program.nodes[ordinal].kind
    else {
        unreachable!()
    };
    let mut method = access.method();
    let mut definition = access.definition();
    let mut arguments = access.arguments().to_vec();
    let mut operand = access.operand();
    match mutation {
        AccessMutation::Method => {
            method = MethodId::new(method.interface(), method.declaration() + 1)
        }
        AccessMutation::Definition => {
            definition = ResourceDefinitionId::new(definition.module(), definition.ordinal() + 1)
        }
        AccessMutation::Arguments => arguments[0] = Type::Int,
        AccessMutation::Operand => operand = program.root,
        AccessMutation::Result => program.nodes[ordinal].ty = Type::Int,
        AccessMutation::Effects => {
            program.nodes[ordinal].effects = program
                .nodes
                .iter()
                .find_map(|node| match &node.kind {
                    EffectExprKind::Operation(EffectOperation::Request(_)) => {
                        Some(node.effects.clone())
                    }
                    _ => None,
                })
                .unwrap();
        }
        AccessMutation::OtherEnclosing => {
            let own_identity = program
                .nodes
                .iter()
                .find_map(|stored| match &stored.kind {
                    EffectExprKind::Operation(EffectOperation::Request(request)) => {
                        Some(request.effect().arguments()[0].clone())
                    }
                    _ => None,
                })
                .unwrap();
            let resource = node(program, operand).unwrap().ty.outer_nominal().unwrap();
            let state = program.nodes[ordinal].ty.outer_nominal().unwrap();
            program.nodes[operand.index().unwrap()].ty = Type::Application(
                Box::new(Type::Nominal(resource)),
                Box::new(own_identity.clone()),
            );
            program.nodes[ordinal].ty = Type::Application(
                Box::new(Type::Nominal(state)),
                Box::new(own_identity.clone()),
            );
            arguments[0] = own_identity;
        }
        AccessMutation::Callable => {
            let body =
                program
                    .nodes
                    .iter()
                    .find_map(|stored| match &stored.kind {
                        EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(
                            function,
                        ))) if function.parameter().ty() == &Type::Unit => Some(function.body()),
                        _ => None,
                    })
                    .unwrap();
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding))) =
                &node(program, body).unwrap().kind
            else {
                panic!("missing callable binding")
            };
            let replacement = super::super::binding::BindingNode::new(
                super::super::variable::TypedBinder::new(
                    program.arena,
                    binding.binder().id(),
                    program.nodes[ordinal].ty.clone(),
                    binding.binder().origin().clone(),
                ),
                NodeId::new(program.arena, u32::try_from(ordinal).unwrap()),
                binding.body(),
            );
            program.nodes[body.index().unwrap()].kind = EffectExprKind::Pure(
                PureExprKind::Computation(PureComputation::Bind(replacement)),
            );
        }
    }
    program.nodes[ordinal].kind = EffectExprKind::Operation(EffectOperation::ProviderStateAccess(
        super::super::effect::ProviderStateAccessNode::new(
            method,
            definition,
            arguments.into_boxed_slice(),
            operand,
        ),
    ));
}

#[cfg(test)]
pub(crate) fn deepen_state_access_argument(program: &mut UnvalidatedEffectProgram, depth: usize) {
    let ordinal = program
        .nodes
        .iter()
        .position(|stored| {
            matches!(
                &stored.kind,
                EffectExprKind::Operation(EffectOperation::ProviderStateAccess(_))
            )
        })
        .unwrap();
    let EffectExprKind::Operation(EffectOperation::ProviderStateAccess(access)) =
        &program.nodes[ordinal].kind
    else {
        unreachable!()
    };
    let (method, definition, operand) = (access.method(), access.definition(), access.operand());
    let resource = node(program, operand).unwrap().ty.outer_nominal().unwrap();
    let state = program.nodes[ordinal].ty.outer_nominal().unwrap();
    let mut deep = IterativeTypeOwner::new(Type::Int);
    for _ in 0..depth {
        deep = IterativeTypeOwner::new(Type::Function(
            Box::new(Type::Int),
            Box::new(deep.into_inner()),
        ));
    }
    let mut work = TypeWorkBudget::unbounded();
    program.nodes[operand.index().unwrap()].ty = Type::Application(
        Box::new(Type::Nominal(resource)),
        Box::new(clone_type_with_budget(&deep, &mut work).unwrap()),
    );
    program.nodes[ordinal].ty = Type::Application(
        Box::new(Type::Nominal(state)),
        Box::new(clone_type_with_budget(&deep, &mut work).unwrap()),
    );
    program.nodes[ordinal].kind = EffectExprKind::Operation(EffectOperation::ProviderStateAccess(
        super::super::effect::ProviderStateAccessNode::new(
            method,
            definition,
            Box::new([deep.into_inner()]),
            operand,
        ),
    ));
}

pub(crate) fn check_state_access_associations(
    program: &UnvalidatedEffectProgram,
    associations: &[DraftStateAssociation<'_>],
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let native = NativeFacts::index(program, work)?;
    let catalog = AssociationCatalog::index(associations, &native, program.root, work)?;
    for (ordinal, stored) in program.nodes.iter().enumerate() {
        charge(work, 1)?;
        if let EffectExprKind::Operation(EffectOperation::ProviderStateAccess(access)) =
            &stored.kind
        {
            let id = NodeId::new(
                program.arena,
                u32::try_from(ordinal).map_err(|_| resource())?,
            );
            catalog.check(program, &native, id, access, work)?;
        }
    }
    Ok(())
}

struct Substitutions(HashMap<TypeVariableId, Type>);
impl Drop for Substitutions {
    fn drop(&mut self) {
        for (_, ty) in self.0.drain() {
            discard_type_iteratively(ty);
        }
    }
}

pub(super) struct AssociationCatalog<'a, 'b> {
    associations: HashMap<ResourceDefinitionId, &'a DraftStateAssociation<'b>>,
}

fn nominal_arguments<'a>(
    ty: &'a Type,
    id: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<(NominalTypeId, Vec<&'a Type>), ValidationError> {
    let mut head = ty;
    let mut arguments = Vec::new();
    while let Type::Application(function, argument) = head {
        charge(work, 1)?;
        arguments.try_reserve(1).map_err(|_| resource())?;
        arguments.push(argument.as_ref());
        head = function;
    }
    arguments.reverse();
    match head {
        Type::Nominal(family) => Ok((*family, arguments)),
        _ => Err(invalid(id)),
    }
}

impl<'a, 'b> AssociationCatalog<'a, 'b> {
    pub(super) fn check_enclosing_state(
        &self,
        program: &UnvalidatedEffectProgram,
        native: &NativeFacts<'_>,
        access_id: NodeId,
        request_id: NodeId,
        expected: &crate::foreign::ForeignStateOperandFact,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        let stored = node(program, access_id)?;
        let EffectExprKind::Operation(EffectOperation::ProviderStateAccess(access)) = &stored.kind
        else {
            return Err(invalid(request_id));
        };
        self.check(program, native, access_id, access, work)?;
        let EffectExprKind::Operation(EffectOperation::Request(request)) =
            &node(program, request_id)?.kind
        else {
            return Err(invalid(request_id));
        };
        let (family, arguments) = nominal_arguments(&stored.ty, request_id, work)?;
        if family != expected.state || arguments.len() != expected.lineage.len() {
            return Err(invalid(request_id));
        }
        for (argument, coordinate) in arguments.iter().zip(&expected.lineage) {
            charge(work, 1)?;
            let expected = request
                .effect()
                .arguments()
                .get(*coordinate)
                .ok_or_else(|| invalid(request_id))?;
            if !same_type_with_budget(argument, expected, work).map_err(|()| resource())? {
                return Err(invalid(request_id));
            }
        }
        Ok(())
    }

    pub(super) fn index(
        associations: &'a [DraftStateAssociation<'b>],
        native: &NativeFacts<'_>,
        anchor: NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        charge(
            work,
            associations.len().checked_mul(2).ok_or_else(resource)?,
        )?;
        let mut index = Self {
            associations: HashMap::new(),
        };
        let mut families = HashSet::new();
        index
            .associations
            .try_reserve(associations.len())
            .map_err(|_| resource())?;
        families
            .try_reserve(associations.len())
            .map_err(|_| resource())?;
        for association in associations {
            // A header relation is bounded draft input, never a publication certificate.
            if association.definition.module() != association.family.module()
                || association.parameters.is_empty()
                || !families.insert(association.family)
                || index
                    .associations
                    .insert(association.definition, association)
                    .is_some()
            {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            }
            let (family, arguments) = nominal_arguments(association.state, anchor, work)?;
            charge(work, 1)?;
            let state = native.states.get(&family).ok_or_else(|| invalid(anchor))?;
            if arguments.len() != state.parameter_count
                || arguments.get(state.owned_identity_position).copied()
                    != Some(&Type::Variable(association.parameters[0]))
            {
                return Err(invalid(anchor));
            }
            charge(work, association.parameters.len())?;
            let mut parameters = HashSet::new();
            parameters
                .try_reserve(association.parameters.len())
                .map_err(|_| resource())?;
            for parameter in association.parameters {
                if !parameters.insert(*parameter) {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
            }
        }
        Ok(index)
    }

    pub(super) fn check(
        &self,
        program: &UnvalidatedEffectProgram,
        native: &NativeFacts<'_>,
        id: NodeId,
        access: &super::super::effect::ProviderStateAccessNode,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        charge(work, 2)?;
        if !native.access.contains_key(&access.method()) {
            return Err(invalid(id));
        }
        let association = self
            .associations
            .get(&access.definition())
            .ok_or_else(|| invalid(id))?;
        let stored = node(program, id)?;
        let operand = node(program, access.operand())?;
        let (family, arguments) = nominal_arguments(&operand.ty, id, work)?;
        if family != association.family
            || arguments.len() != association.parameters.len()
            || arguments.len() != access.arguments().len()
        {
            return Err(invalid(id));
        }
        let mut substitutions = Substitutions(HashMap::new());
        charge(work, arguments.len())?;
        substitutions
            .0
            .try_reserve(arguments.len())
            .map_err(|_| resource())?;
        for ((parameter, actual), retained) in association
            .parameters
            .iter()
            .zip(arguments)
            .zip(access.arguments())
        {
            if !same_type_with_budget(actual, retained, work).map_err(|()| resource())? {
                return Err(invalid(id));
            }
            let replacement = IterativeTypeOwner::new(
                clone_type_with_budget(actual, work).map_err(|()| resource())?,
            );
            match substitutions.0.entry(*parameter) {
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(replacement.into_inner());
                }
                std::collections::hash_map::Entry::Occupied(_) => return Err(invalid(id)),
            }
        }
        let expected = IterativeTypeOwner::new(
            substitute_type_variables_with(
                association.state,
                &substitutions.0,
                |cells| work.charge(cells),
                || (),
            )
            .map_err(|()| resource())?,
        );
        if !same_type_with_budget(&expected, &stored.ty, work).map_err(|()| resource())?
            || !same_effect_rows_with_budget(&operand.effects, &stored.effects, work)
                .map_err(|()| resource())?
        {
            return Err(invalid(id));
        }
        Ok(())
    }
}
