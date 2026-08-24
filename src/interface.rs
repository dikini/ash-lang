//! Stable typed identities for resolved interfaces and implementations.

use std::fmt;

use crate::{
    module::ModuleId,
    resolved::BinderId,
    source::{Origin, Span, discard_origin_iteratively},
    types::{
        Type, TypeVariableId, TypeWorkBudget, clone_type_with_budget, discard_type_iteratively,
    },
};

/// Maximum cumulative interface and constraint work across one module graph.
pub const INTERFACE_CONSTRAINT_WORK_LIMIT: usize = 327_680;

/// Graph-wide accounting for interface facts, constraints, and evidence work.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct InterfaceConstraintBudget {
    used: usize,
    limit: usize,
}

impl Default for InterfaceConstraintBudget {
    fn default() -> Self {
        Self {
            used: 0,
            limit: INTERFACE_CONSTRAINT_WORK_LIMIT,
        }
    }
}

impl InterfaceConstraintBudget {
    #[cfg(test)]
    pub(crate) const fn with_limit(limit: usize) -> Self {
        Self { used: 0, limit }
    }

    pub(crate) fn charge(&mut self, work: usize) -> Result<(), ()> {
        let next = self.used.checked_add(work).ok_or(())?;
        if next > self.limit {
            return Err(());
        }
        self.used = next;
        Ok(())
    }

    pub(crate) fn charge_type(&mut self, root: &Type) -> Result<(), ()> {
        enum Task<'a> {
            Type(&'a Type),
            Sequence(std::slice::Iter<'a, Type>),
        }

        self.charge(1)?;
        let mut pending = Vec::new();
        pending.try_reserve(1).map_err(|_| ())?;
        pending.push(Task::Type(root));
        while let Some(task) = pending.pop() {
            let Task::Type(ty) = task else {
                let Task::Sequence(mut remaining) = task else {
                    unreachable!()
                };
                if let Some(next) = remaining.next() {
                    self.charge(2)?;
                    pending.try_reserve(2).map_err(|_| ())?;
                    pending.push(Task::Sequence(remaining));
                    pending.push(Task::Type(next));
                }
                continue;
            };
            self.charge(1)?;
            match ty {
                Type::Tuple(elements) | Type::AppliedNominal(_, elements) => {
                    self.charge(1)?;
                    pending.try_reserve(1).map_err(|_| ())?;
                    pending.push(Task::Sequence(elements.iter()));
                }
                Type::Function(domain, codomain) => {
                    self.charge(2)?;
                    pending.try_reserve(2).map_err(|_| ())?;
                    pending.push(Task::Type(codomain));
                    pending.push(Task::Type(domain));
                }
                Type::Forall(parameters, body) => {
                    self.charge(parameters.len().saturating_add(1))?;
                    pending.try_reserve(1).map_err(|_| ())?;
                    pending.push(Task::Type(body));
                }
                Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_) => {}
            }
        }
        Ok(())
    }
}

/// The interface or implementation header judgment that rejected source.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InterfaceReason {
    /// An interface method omits its parameter or introduces another type variable.
    MethodParameter,
    /// An interface method signature has no callable function shape.
    MethodNotFunction,
    /// One constrained global repeats an identity-equal requirement.
    DuplicateRequirement,
    /// A requirement mentions a type parameter absent from the value type.
    UndeterminedParameter,
    /// A public constrained global exposes a private interface.
    ConstraintPrivateInterface,
    /// A public implementation or prerequisite exposes a private interface.
    ImplPrivateInterface,
    /// Neither the implemented interface nor outer nominal head is locally owned.
    ImplOrphan,
    /// An implementation head is a bare type variable.
    ImplVariableHead,
    /// Two available implementation heads unify.
    ImplOverlap,
    /// An implementation prerequisite introduces a variable absent from the head.
    ImplPrerequisiteVariable,
    /// A non-ground implementation prerequisite is not a strict head subterm.
    ImplPrerequisiteNotDecreasing,
    /// An implementation omits one required interface method.
    ImplMissingMethod,
    /// An implementation supplies one interface method more than once.
    ImplDuplicateMethod,
    /// An implementation group does not name a method of its interface.
    ImplExtraMethod,
}

impl fmt::Display for InterfaceReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::MethodParameter => "interface.method-parameter",
            Self::MethodNotFunction => "interface.method-not-function",
            Self::DuplicateRequirement => "constraint.duplicate-requirement",
            Self::UndeterminedParameter => "constraint.undetermined-parameter",
            Self::ConstraintPrivateInterface => "constraint.private-interface",
            Self::ImplPrivateInterface => "impl.private-interface",
            Self::ImplOrphan => "impl.orphan",
            Self::ImplVariableHead => "impl.variable-head",
            Self::ImplOverlap => "impl.overlap",
            Self::ImplPrerequisiteVariable => "impl.prerequisite-variable",
            Self::ImplPrerequisiteNotDecreasing => "impl.prerequisite-not-decreasing",
            Self::ImplMissingMethod => "impl.missing-method",
            Self::ImplDuplicateMethod => "impl.duplicate-method",
            Self::ImplExtraMethod => "impl.extra-method",
        })
    }
}

/// Stable identity of one interface declaration.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InterfaceId {
    module: ModuleId,
    declaration: u32,
}

impl InterfaceId {
    /// Creates the identity for one interface declaration in an admitted module.
    #[must_use]
    pub const fn new(module: ModuleId, declaration: u32) -> Self {
        Self {
            module,
            declaration,
        }
    }

    /// Returns the canonical module that owns the declaration.
    #[must_use]
    pub const fn module(self) -> ModuleId {
        self.module
    }

    /// Returns the source-order interface declaration index.
    #[must_use]
    pub const fn declaration(self) -> u32 {
        self.declaration
    }
}

/// Stable identity of one method declared by an interface.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MethodId {
    interface: InterfaceId,
    declaration: u32,
}

impl MethodId {
    /// Creates the identity for one method in its interface declaration.
    #[must_use]
    pub const fn new(interface: InterfaceId, declaration: u32) -> Self {
        Self {
            interface,
            declaration,
        }
    }

    /// Returns the interface that owns the method.
    #[must_use]
    pub const fn interface(self) -> InterfaceId {
        self.interface
    }

    /// Returns the source-order method declaration index.
    #[must_use]
    pub const fn declaration(self) -> u32 {
        self.declaration
    }
}

/// Stable identity of one implementation declaration.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ImplId {
    module: ModuleId,
    declaration: u32,
}

impl ImplId {
    /// Creates the identity for one implementation declaration in an admitted module.
    #[must_use]
    pub const fn new(module: ModuleId, declaration: u32) -> Self {
        Self {
            module,
            declaration,
        }
    }

    /// Returns the canonical module that owns the declaration.
    #[must_use]
    pub const fn module(self) -> ModuleId {
        self.module
    }

    /// Returns the source-order implementation declaration index.
    #[must_use]
    pub const fn declaration(self) -> u32 {
        self.declaration
    }
}

/// Stable identity of one interface method supplied by an implementation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ImplMethodId {
    implementation: ImplId,
    method: MethodId,
}

impl ImplMethodId {
    /// Creates the identity for one implemented interface method.
    #[must_use]
    pub const fn new(implementation: ImplId, method: MethodId) -> Self {
        Self {
            implementation,
            method,
        }
    }

    /// Returns the implementation that supplies the method.
    #[must_use]
    pub const fn implementation(self) -> ImplId {
        self.implementation
    }

    /// Returns the interface method supplied by the implementation.
    #[must_use]
    pub const fn method(self) -> MethodId {
        self.method
    }
}

/// Declaration that owns one ordered interface requirement.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RequirementOwner {
    /// A requirement declared by a module-level global.
    Global(BinderId),
    /// A prerequisite declared by an implementation.
    Impl(ImplId),
}

/// Stable identity of one ordered interface requirement.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RequirementId {
    owner: RequirementOwner,
    declaration: u32,
}

impl RequirementId {
    /// Creates the identity for one requirement under its declaring owner.
    #[must_use]
    pub const fn new(owner: RequirementOwner, declaration: u32) -> Self {
        Self { owner, declaration }
    }

    /// Returns the global or implementation that owns the requirement.
    #[must_use]
    pub const fn owner(self) -> RequirementOwner {
        self.owner
    }

    /// Returns the source-order requirement declaration index.
    #[must_use]
    pub const fn declaration(self) -> u32 {
        self.declaration
    }
}

/// Structural evidence state owned by one resolved constrained occurrence.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum EvidenceSlot {
    /// Resolution has retained the slot, but checking has not selected evidence.
    Empty,
}

/// One admitted requirement in a checked constrained scheme.
#[derive(Debug, Eq, PartialEq)]
pub struct CheckedRequirement {
    /// Stable occurrence identity under its declaring owner.
    pub id: RequirementId,
    /// Stable checked interface identity.
    pub interface: InterfaceId,
    /// Fully resolved requirement argument.
    pub argument: Type,
    /// Causal declaration provenance.
    pub origin: Origin,
    /// Complete source requirement span.
    pub span: Span,
}

impl Drop for CheckedRequirement {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.argument, Type::Unit));
        discard_origin_iteratively(std::mem::replace(
            &mut self.origin,
            Origin::Source(self.span),
        ));
    }
}

/// A checked source scheme whose requirements remain outside ordinary types.
#[derive(Debug, Eq, PartialEq)]
pub struct ConstrainedScheme {
    /// Ordered outer rank-1 type parameters.
    pub type_parameters: Box<[TypeVariableId]>,
    /// Ordered explicit interface requirements.
    pub requirements: Box<[CheckedRequirement]>,
    /// Source value type without an enclosing `forall` node.
    pub value_type: Type,
}

impl ConstrainedScheme {
    #[cfg(test)]
    pub(crate) fn from_rank1_type(scheme: Type) -> Self {
        match scheme {
            Type::Forall(type_parameters, value_type) => Self {
                type_parameters,
                requirements: Box::new([]),
                value_type: *value_type,
            },
            value_type => Self {
                type_parameters: Box::new([]),
                requirements: Box::new([]),
                value_type,
            },
        }
    }

    pub(crate) fn clone_with_budget(&self, budget: &mut TypeWorkBudget) -> Result<Self, ()> {
        budget.charge(
            self.type_parameters
                .len()
                .saturating_add(self.requirements.len()),
        )?;
        let mut type_parameters = Vec::new();
        type_parameters
            .try_reserve(self.type_parameters.len())
            .map_err(|_| ())?;
        type_parameters.extend_from_slice(&self.type_parameters);
        let mut requirements = Vec::new();
        requirements
            .try_reserve(self.requirements.len())
            .map_err(|_| ())?;
        for requirement in &self.requirements {
            requirements.push(CheckedRequirement {
                id: requirement.id,
                interface: requirement.interface,
                argument: clone_type_with_budget(&requirement.argument, budget)?,
                origin: requirement.origin.clone(),
                span: requirement.span,
            });
        }
        Ok(Self {
            type_parameters: type_parameters.into_boxed_slice(),
            requirements: requirements.into_boxed_slice(),
            value_type: clone_type_with_budget(&self.value_type, budget)?,
        })
    }

    /// Reports whether the source scheme requires no interface evidence.
    #[must_use]
    pub const fn is_unconstrained(&self) -> bool {
        self.requirements.is_empty()
    }
}

impl Drop for ConstrainedScheme {
    fn drop(&mut self) {
        for requirement in std::mem::take(&mut self.requirements).into_vec() {
            drop(requirement);
        }
        discard_type_iteratively(std::mem::replace(&mut self.value_type, Type::Unit));
    }
}

#[cfg(test)]
mod tests {
    use std::any::TypeId;

    use super::*;
    use crate::{module::ModuleId, resolved::BinderId};

    #[test]
    fn interface_and_method_identities_preserve_their_components() {
        let module = ModuleId::new(7);
        let interface = InterfaceId::new(module, 3);
        let method = MethodId::new(interface, 5);

        assert_eq!(interface.module(), module);
        assert_eq!(interface.declaration(), 3);
        assert_eq!(method.interface(), interface);
        assert_eq!(method.declaration(), 5);
    }

    #[test]
    fn implementation_and_method_identities_preserve_their_components() {
        let module = ModuleId::new(11);
        let implementation = ImplId::new(module, 13);
        let interface = InterfaceId::new(module, 17);
        let method = MethodId::new(interface, 19);
        let implementation_method = ImplMethodId::new(implementation, method);

        assert_eq!(implementation.module(), module);
        assert_eq!(implementation.declaration(), 13);
        assert_eq!(implementation_method.implementation(), implementation);
        assert_eq!(implementation_method.method(), method);
    }

    #[test]
    fn requirement_identities_preserve_owner_and_declaration_order() {
        let module = ModuleId::new(23);
        let global = RequirementOwner::Global(BinderId::resolved(module, 29));
        let implementation = RequirementOwner::Impl(ImplId::new(module, 31));
        let first = RequirementId::new(global, 0);
        let second = RequirementId::new(global, 1);
        let prerequisite = RequirementId::new(implementation, 0);

        assert_eq!(first.owner(), global);
        assert_eq!(first.declaration(), 0);
        assert_eq!(second.owner(), global);
        assert_eq!(second.declaration(), 1);
        assert_ne!(first, second);
        assert_eq!(prerequisite.owner(), implementation);
        assert_eq!(prerequisite.declaration(), 0);
    }

    #[test]
    fn semantic_identity_categories_remain_distinct_types() {
        assert_ne!(TypeId::of::<InterfaceId>(), TypeId::of::<ImplId>());
        assert_ne!(TypeId::of::<MethodId>(), TypeId::of::<ImplMethodId>());
        assert_ne!(TypeId::of::<RequirementId>(), TypeId::of::<MethodId>());
        assert_eq!(EvidenceSlot::Empty, EvidenceSlot::Empty);
    }

    #[test]
    fn constraint_type_traversal_accepts_its_exact_budget_and_rejects_the_next_unit() {
        let ty = Type::Function(Box::new(Type::Int), Box::new(Type::Bool));

        let mut short = InterfaceConstraintBudget::with_limit(5);
        assert_eq!(short.charge_type(&ty), Err(()));

        let mut exact = InterfaceConstraintBudget::with_limit(6);
        exact
            .charge_type(&ty)
            .expect("the exact traversal and worklist budget should fit");
        assert_eq!(exact.charge(1), Err(()));
    }
}
