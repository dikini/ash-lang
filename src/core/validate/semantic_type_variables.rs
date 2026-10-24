//! Borrowed semantic uses for an OriginalTemplate ordering proof.
//!
//! A canonical variable record is a definition, not a use. Every retained
//! occurrence and correspondence is nevertheless significant, including rigid
//! row tails and phantom operation arguments. This scan grants no scope or
//! resource-family authority.

use std::collections::HashSet;

use crate::types::{
    EffectInstance, EffectRow, KindedArgument, Type, TypeStructureNode, TypeVariableId,
    TypeWorkBudget, visit_argument_structure_with_budget, visit_type_structure_with_budget,
};

pub(crate) struct UnusedVariables<'work> {
    remaining: HashSet<TypeVariableId>,
    work: &'work mut TypeWorkBudget,
}

impl<'work> UnusedVariables<'work> {
    pub(crate) fn new(
        candidates: &HashSet<TypeVariableId>,
        work: &'work mut TypeWorkBudget,
    ) -> Result<Self, ()> {
        work.charge(candidates.len())?;
        let mut remaining = HashSet::new();
        remaining.try_reserve(candidates.len()).map_err(|_| ())?;
        remaining.extend(candidates.iter().copied());
        Ok(Self { remaining, work })
    }

    pub(crate) fn finish(self) -> HashSet<TypeVariableId> {
        self.remaining
    }

    pub(crate) fn charge(&mut self, amount: usize) -> Result<(), ()> {
        self.work.charge(amount)
    }

    // Formal definitions disqualify an ordering candidate as well. Callers
    // explicitly enumerate ownership separately from semantic occurrences.
    pub(crate) fn id(&mut self, id: TypeVariableId) -> Result<(), ()> {
        self.work.charge(1)?;
        self.remaining.remove(&id);
        Ok(())
    }

    pub(crate) fn ty(&mut self, ty: &Type) -> Result<(), ()> {
        let Self { remaining, work } = self;
        visit_type_structure_with_budget(ty, *work, |node, work| {
            work.charge(1)?;
            match node {
                TypeStructureNode::Type(Type::Variable(id)) => {
                    remaining.remove(id);
                }
                TypeStructureNode::Type(Type::Forall(parameters, _)) => {
                    work.charge(parameters.len())?;
                    for (id, _) in parameters.iter() {
                        remaining.remove(id);
                    }
                }
                TypeStructureNode::Tail(tail) => {
                    if let crate::types::EffectRowVariable::Rigid(id) = tail.variable() {
                        remaining.remove(&id);
                    }
                }
                _ => {}
            }
            Ok(false)
        })?;
        Ok(())
    }

    pub(crate) fn argument(&mut self, argument: &KindedArgument) -> Result<(), ()> {
        let Self { remaining, work } = self;
        visit_argument_structure_with_budget(argument, *work, |node, work| {
            work.charge(1)?;
            match node {
                TypeStructureNode::Type(Type::Variable(id)) => {
                    remaining.remove(id);
                }
                TypeStructureNode::Type(Type::Forall(parameters, _)) => {
                    work.charge(parameters.len())?;
                    for (id, _) in parameters.iter() {
                        remaining.remove(id);
                    }
                }
                TypeStructureNode::Tail(tail) => {
                    if let crate::types::EffectRowVariable::Rigid(id) = tail.variable() {
                        remaining.remove(&id);
                    }
                }
                _ => {}
            }
            Ok(false)
        })?;
        Ok(())
    }

    pub(crate) fn arguments(&mut self, arguments: &[KindedArgument]) -> Result<(), ()> {
        self.charge(arguments.len())?;
        for argument in arguments {
            self.argument(argument)?;
        }
        Ok(())
    }

    pub(crate) fn instance(&mut self, instance: &EffectInstance) -> Result<(), ()> {
        self.arguments(instance.arguments())
    }

    pub(crate) fn row(&mut self, row: &EffectRow) -> Result<(), ()> {
        self.charge(row.known().len())?;
        for instance in row.known() {
            self.instance(instance)?;
        }
        if let Some(tail) = row.tail() {
            if let crate::types::EffectRowVariable::Rigid(id) = tail.variable() {
                self.id(id)?;
            }
            self.charge(tail.lacks().len())?;
            for instance in tail.lacks() {
                self.instance(instance)?;
            }
        }
        Ok(())
    }

    pub(crate) fn application(
        &mut self,
        application: &crate::interface::InterfaceApplication,
    ) -> Result<(), ()> {
        self.arguments(application.arguments())
    }

    pub(crate) fn pattern(&mut self, pattern: &crate::core::CorePattern) -> Result<(), ()> {
        let mut pending = Vec::new();
        self.charge(1)?;
        pending.try_reserve(1).map_err(|_| ())?;
        pending.push(pattern);
        while let Some(pattern) = pending.pop() {
            self.charge(1)?;
            self.ty(&pattern.ty)?;
            match &pattern.kind {
                crate::core::CorePatternKind::Binder(binder) => self.ty(binder.ty())?,
                crate::core::CorePatternKind::Tuple(elements) => {
                    self.charge(elements.len())?;
                    pending.try_reserve(elements.len()).map_err(|_| ())?;
                    pending.extend(elements);
                }
                crate::core::CorePatternKind::Constructor { payload, .. } => {
                    if let Some(payload) = payload {
                        self.charge(1)?;
                        pending.try_reserve(1).map_err(|_| ())?;
                        pending.push(payload);
                    }
                }
                crate::core::CorePatternKind::Wildcard
                | crate::core::CorePatternKind::Boolean(_)
                | crate::core::CorePatternKind::Unit => {}
            }
        }
        Ok(())
    }

    pub(crate) fn selection(
        &mut self,
        selection: &crate::interface::EvidenceSelection,
    ) -> Result<(), ()> {
        selection.visit_semantic_type_variables(self)
    }

    pub(crate) fn catalog(
        &mut self,
        catalog: &crate::core::dialect::MethodEvidenceCatalog,
    ) -> Result<(), ()> {
        use crate::core::dialect::MethodEvidenceResourceOwner;
        self.charge(catalog.lexical_owners().len())?;
        for owner in catalog.lexical_owners() {
            self.charge(owner.source_parameters.len())?;
            for id in &owner.source_parameters {
                self.id(*id)?;
            }
            self.application(&owner.application)?;
            match &owner.resource {
                Some(MethodEvidenceResourceOwner::Builtin(owner)) => self.id(owner.identity)?,
                None => {}
            }
        }
        self.charge(catalog.methods().len())?;
        for method in catalog.methods() {
            self.ty(&method.value_type)?;
            self.charge(
                method.interface_parameters.len()
                    + method.inherited_parameters.len()
                    + method.parameters.len(),
            )?;
            for id in &method.interface_parameters {
                self.id(*id)?;
            }
            for parameter in &method.inherited_parameters {
                self.id(parameter.binder)?;
            }
            for (id, _) in &method.parameters {
                self.id(*id)?;
            }
        }
        self.charge(catalog.implementation_owners().len())?;
        for owner in catalog.implementation_owners() {
            self.charge(owner.source_parameters.len())?;
            for (id, _) in &owner.source_parameters {
                self.id(*id)?;
            }
            self.application(&owner.application)?;
        }
        self.charge(catalog.domains().len())?;
        for domain in catalog.domains() {
            self.charge(domain.source_parameters.len())?;
            for (id, _) in &domain.source_parameters {
                self.id(*id)?;
            }
            self.application(&domain.application)?;
        }
        self.charge(catalog.occurrences().len())?;
        for occurrence in catalog.occurrences() {
            self.application(&occurrence.checked_application)?;
            self.charge(occurrence.method_arguments.len())?;
            for argument in &occurrence.method_arguments {
                self.ty(argument)?;
            }
            if let Some(ty) = &occurrence.checked_value_type {
                self.ty(ty)?;
            }
            self.selection(&occurrence.selection)?;
        }
        self.charge(catalog.adapters().len())?;
        for adapter in catalog.adapters() {
            self.charge(
                adapter.source_parameters.len()
                    + adapter.head_arguments.len()
                    + adapter.prerequisites.len(),
            )?;
            for id in &adapter.source_parameters {
                self.id(*id)?;
            }
            for argument in &adapter.head_arguments {
                self.ty(argument)?;
            }
            for prerequisite in &adapter.prerequisites {
                self.application(&prerequisite.application)?;
                self.ty(&prerequisite.value_type)?;
                self.charge(
                    prerequisite.interface_parameters.len() + prerequisite.method_parameters.len(),
                )?;
                for id in &prerequisite.interface_parameters {
                    self.id(*id)?;
                }
                for (id, _) in &prerequisite.method_parameters {
                    self.id(*id)?;
                }
            }
        }
        self.charge(catalog.concrete_sources().len())?;
        for source in catalog.concrete_sources() {
            self.charge(source.head_arguments.len())?;
            for argument in &source.head_arguments {
                self.ty(argument)?;
            }
        }
        // Final-occurrence owners and expectations contain only term/method,
        // plan, ordinal and role identities, with no TypeVariableId payload.
        self.charge(catalog.final_occurrence_owners().len() + catalog.expectations().len())?;
        Ok(())
    }

    pub(crate) fn program(
        &mut self,
        program: &crate::core::effect::UnvalidatedEffectProgram,
    ) -> Result<(), ()> {
        use super::ScopeFamily;
        use crate::core::dialect::{
            CoreOperationFamily, OperationTypeMetadata, PureComputation, PureExprKind, PureValue,
        };
        use crate::core::effect::EffectOperationFamily as F;
        let mut pending = Vec::new();
        let mut seen = HashSet::new();
        self.charge(1)?;
        pending.try_reserve(1).map_err(|_| ())?;
        pending.push(program);
        while let Some(program) = pending.pop() {
            self.charge(1)?;
            seen.try_reserve(1).map_err(|_| ())?;
            if !seen.insert(program as *const _) {
                continue;
            }
            self.charge(program.nodes.len() + program.method_evidence_anchors.len())?;
            for node in &program.nodes {
                self.ty(&node.ty)?;
                self.row(F::effect_row(&node.effects))?;
                // Some operation containers yield no Type metadata (for example a
                // nullary native instance). Pay for them before the borrowed walk.
                if let crate::core::effect::EffectExprKind::Operation(operation) = &node.kind {
                    use crate::core::effect::EffectOperation;
                    match operation {
                        EffectOperation::NativeInterpret(boundary) => {
                            self.charge(boundary.interpretations().len())?;
                        }
                        EffectOperation::Handler(handler) => {
                            self.charge(handler.clauses().len())?
                        }

                        _ => {}
                    }
                }
                match F::pure(&node.kind) {
                    Some(PureExprKind::Value(PureValue::Function(function))) => {
                        self.ty(function.parameter().ty())?
                    }
                    Some(PureExprKind::Computation(PureComputation::Bind(binding))) => {
                        self.ty(binding.binder().ty())?
                    }
                    Some(PureExprKind::Computation(PureComputation::RecursiveBind(binding))) => {
                        self.charge(binding.members().len())?;
                        for member in binding.members() {
                            self.ty(member.binder().ty())?;
                        }
                    }
                    Some(PureExprKind::Computation(PureComputation::Match(select))) => {
                        self.charge(select.arms().len())?;
                        for arm in select.arms() {
                            self.pattern(arm.pattern())?;
                        }
                    }
                    Some(PureExprKind::Computation(PureComputation::TypeApplication(
                        application,
                    ))) => {
                        self.charge(
                            application.arguments().len() + application.row_arguments().len(),
                        )?;
                        for ty in application.arguments() {
                            self.ty(ty)?;
                        }
                        for row in application.row_arguments() {
                            self.row(row)?;
                        }
                    }
                    Some(PureExprKind::Computation(PureComputation::TypeAbstraction(
                        abstraction,
                    ))) => {
                        self.charge(abstraction.parameters().len())?;
                        for (id, _) in abstraction.parameters() {
                            self.id(*id)?;
                        }
                    }
                    // All other pure payloads contain only term/nominal identities
                    // or type-binder definitions; their envelopes are scanned above.
                    _ => {}
                }
                let mut result = Ok(());
                F::visit_operation_type_metadata(&node.kind, &mut |metadata| {
                    if result.is_ok() {
                        result = match metadata {
                            OperationTypeMetadata::Type(ty) => self.ty(ty),
                            OperationTypeMetadata::Argument(argument) => self.argument(argument),
                            OperationTypeMetadata::Row(row) => self.row(row),
                            OperationTypeMetadata::Pattern(pattern) => self.pattern(pattern),
                        };
                    }
                });
                result?;
            }
            for anchor in &program.method_evidence_anchors {
                self.application(&anchor.application)?;
            }
            program.registry.visit_semantic_type_variables(self)?;
            self.catalog(&program.method_evidence)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        module::ModuleId,
        types::{EffectId, EffectRowVariable, Kind},
    };

    #[test]
    fn source_control_unused_footprint_counts_formals_body_uses_and_rigid_actuals() {
        let first = TypeVariableId::new(0);
        let second = TypeVariableId::new(1);
        let candidates = HashSet::from([first, second]);
        let inputs = [
            KindedArgument::TypeArg(Type::Forall(
                Box::new([(first, Kind::Type)]),
                Box::new(Type::Unit),
            )),
            KindedArgument::TypeArg(Type::Forall(
                Box::new([(second, Kind::Type)]),
                Box::new(Type::Variable(first)),
            )),
            KindedArgument::RowArg(EffectRow::open(
                EffectRowVariable::rigid(first),
                Box::new([EffectInstance::new(
                    EffectId::new(ModuleId::new(0), 0),
                    Box::new([Type::Variable(second)]),
                )]),
            )),
        ];
        for (index, input) in inputs.iter().enumerate() {
            let scan = |work: &mut TypeWorkBudget| {
                let mut uses = UnusedVariables::new(&candidates, work)?;
                uses.argument(input)?;
                Ok::<_, ()>(uses.finish())
            };
            let mut measured = TypeWorkBudget::default();
            let unused = scan(&mut measured).unwrap();
            assert_eq!(
                unused,
                if index == 0 {
                    HashSet::from([second])
                } else {
                    HashSet::new()
                }
            );
            let cost = measured.used();
            for prefix in [0, 13] {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                assert_eq!(scan(&mut exact).unwrap(), unused);
                assert_eq!(exact.used(), prefix + cost);
                let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
                short.charge(prefix).unwrap();
                assert!(scan(&mut short).is_err());
                assert_eq!(scan(&mut TypeWorkBudget::default()).unwrap(), unused);
            }
        }
    }
}
