//! Independent validation for unchecked pure Core arenas.

use std::{
    cell::Cell,
    collections::{HashMap, HashSet},
    error::Error,
    fmt,
};

#[cfg(test)]
use std::sync::Arc;

use super::{
    dialect::{
        CORE_PATTERN_DEPTH_LIMIT, CoreOperationFamily, CoreProgram, CoreTypedExpr, DialectId,
        MethodEvidenceAnchor, MethodEvidenceAnchorRole, MethodEvidenceExpectedRole,
        MethodEvidenceOwner, MethodEvidenceProducer, NodeId, PureComputation, PureExprKind,
        PureOperationFamily, PureProgram, PureValue, StoredNode, TypedExpr, UnvalidatedCoreProgram,
        UnvalidatedProgram, ValidatedCoreProgram, ValidatedProgram,
        method_evidence_producer_matches, origin_depth_within_limit,
    },
    variable::TypedBinder,
};
use crate::{
    core::{CorePattern, CorePatternKind},
    interface::{EvidenceNode, ImplMethodId, InterfaceApplication},
    module::ModuleId,
    pattern::{UsefulnessBudget, missing_witness_for_types_with_budget, usefulness_with_budget},
    resolved::{
        BinderId, ResolvedConstructor, ResolvedNominalDeclarationKind, ResolvedNominalType,
        ResolvedTypeProvenance, ResolvedTypeProvenanceNode, ResolvedTypeVariable,
        same_resolved_type_variables_with_charge,
    },
    source::{Origin, SourceFile, SourceId, Span},
    types::{
        ConstructorId, EffectInstance, EffectRow, IterativeTypeOwner, Kind, OperationId,
        TYPE_WORK_LIMIT, Type, TypeWorkBudget, clone_effect_row_with_budget,
        clone_type_with_budget, discard_type_iteratively, rebuild_effect_row_with_budget,
        same_effect_rows_with_budget, same_type_with_budget,
        substitute_type_and_row_variables_with, substitute_type_variables_with,
    },
};

/// Cumulative structural-work capacity for independent Core validation.
///
/// Validation reauthenticates the complete admitted Core program, including
/// fixed Kind structure. Construction, rebuilding, and every other type-work
/// owner retain [`TYPE_WORK_LIMIT`].
const CORE_VALIDATION_TYPE_WORK_LIMIT: usize = 3 * TYPE_WORK_LIMIT;

struct TypeReplacementMap(HashMap<crate::types::TypeVariableId, Type>);

impl TypeReplacementMap {
    fn new() -> Self {
        Self(HashMap::new())
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn insert_replacing(&mut self, parameter: crate::types::TypeVariableId, ty: Type) {
        if let Some(displaced) = self.0.insert(parameter, ty) {
            discard_type_iteratively(displaced);
        }
    }

    fn as_map(&self) -> &HashMap<crate::types::TypeVariableId, Type> {
        &self.0
    }
}

impl Drop for TypeReplacementMap {
    fn drop(&mut self) {
        for (_, ty) in self.0.drain() {
            discard_type_iteratively(ty);
        }
    }
}

struct CorePatternMatrix(Vec<Vec<CorePattern>>);

impl Drop for CorePatternMatrix {
    fn drop(&mut self) {
        for row in self.0.drain(..) {
            for pattern in row {
                pattern.discard_iteratively();
            }
        }
    }
}

struct CorePatternRow(Vec<CorePattern>);

impl CorePatternRow {
    fn into_inner(mut self) -> Vec<CorePattern> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for CorePatternRow {
    fn drop(&mut self) {
        for pattern in self.0.drain(..) {
            pattern.discard_iteratively();
        }
    }
}

struct OwnedTypeSequence(std::vec::IntoIter<Type>);

struct OwnedTypeBuffer(Vec<Type>);

impl OwnedTypeBuffer {
    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn push(&mut self, ty: Type) {
        self.0.push(ty);
    }

    fn into_boxed_slice(mut self) -> Box<[Type]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for OwnedTypeBuffer {
    fn drop(&mut self) {
        for ty in self.0.drain(..) {
            discard_type_iteratively(ty);
        }
    }
}

impl OwnedTypeSequence {
    fn next(&mut self) -> Option<Type> {
        self.0.next()
    }
}

type CoreTypeBinders<'a> = HashMap<crate::types::TypeVariableId, (&'a Kind, NodeId)>;
type CoreAbstractionOwners = HashMap<NodeId, BinderId>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RegistryParameterOwner {
    Nominal(crate::types::NominalTypeId),
    Effect(crate::types::EffectId),
}

type RegistryParameterOwners = HashMap<crate::types::TypeVariableId, RegistryParameterOwner>;

#[derive(Clone, Copy)]
enum MonotypeVariableKinds<'scope, 'kind> {
    Core(&'scope CoreTypeBinders<'kind>),
    Registry {
        owner: crate::types::NominalTypeId,
        parameter_owners: &'scope RegistryParameterOwners,
    },
}

impl Drop for OwnedTypeSequence {
    fn drop(&mut self) {
        for ty in self.0.by_ref() {
            discard_type_iteratively(ty);
        }
    }
}

/// The independently checked invariant that malformed Core violated.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValidationReason {
    /// A variable or binder identity violates lexical scope.
    Scope,
    /// A node or binder has an inconsistent structural type.
    NodeType,
    /// An application disagrees with its function domain or codomain.
    ApplicationType,
    /// A recursive binding violates its group-shape invariants.
    RecursiveBinding,
    /// Required causal source provenance is missing or invalid.
    Provenance,
    /// A stored node does not belong to the selected pure dialect.
    DialectMembership,
    /// A node refers outside its arena.
    NodeBounds,
    /// The expression graph contains a cycle.
    Cycle,
    /// The selected root does not belong to the arena.
    Root,
    /// The arena contains a node unreachable from its selected root.
    Unreachable,
    /// The immutable nominal and constructor registry is malformed.
    Registry,
    /// A typed structured pattern is malformed.
    Pattern,
    /// Match arms are redundant or non-exhaustive.
    Coverage,
    /// A deterministic validation resource budget was exhausted.
    Resource,
    /// An explicit Core type abstraction or application is malformed.
    TypeOperation,
    /// A Core type variable occurs outside its abstraction scope.
    TypeScope,
    /// A module-newtype conversion does not match its canonical representation relation.
    NewtypeConversion,
    /// A retained effect or operation does not authenticate against its registry.
    EffectIdentity,
    /// A retained computation row or effect-row equation is false.
    EffectRow,
    /// A retained handler does not cover or discharge its exact instance.
    Handler,
    /// A retained resume violates ownership, use, or non-escape.
    Resume,
}

impl fmt::Display for ValidationReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Scope => "core.validation.scope",
            Self::NodeType => "core.validation.node-type",
            Self::ApplicationType => "core.validation.application-type",
            Self::RecursiveBinding => "core.validation.recursive-binding",
            Self::Provenance => "core.validation.provenance",
            Self::DialectMembership => "core.validation.dialect-membership",
            Self::NodeBounds => "core.validation.node-bounds",
            Self::Cycle => "core.validation.cycle",
            Self::Root => "core.validation.root",
            Self::Unreachable => "core.validation.unreachable",
            Self::Registry => "core.validation.registry",
            Self::Pattern => "core.validation.pattern",
            Self::Coverage => "core.validation.coverage",
            Self::Resource => "core.validation.resource",
            Self::TypeOperation => "core.validation.type-operation",
            Self::TypeScope => "core.validation.type-scope",
            Self::NewtypeConversion => "core.validation.newtype-conversion",
            Self::EffectIdentity => "core.validation.effect-identity",
            Self::EffectRow => "core.validation.effect-row",
            Self::Handler => "core.validation.handler",
            Self::Resume => "core.validation.resume",
        })
    }
}

/// A structured internal compiler failure produced by Core validation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValidationError {
    reason: ValidationReason,
    node: Option<NodeId>,
}

impl ValidationError {
    pub(super) const fn new(reason: ValidationReason, node: Option<NodeId>) -> Self {
        Self { reason, node }
    }

    const fn at_node(mut self, node: NodeId) -> Self {
        if self.node.is_none() {
            self.node = Some(node);
        }
        self
    }

    /// Returns the violated invariant category.
    #[must_use]
    pub const fn reason(&self) -> ValidationReason {
        self.reason
    }

    /// Returns the arena node associated with the failure, when available.
    #[must_use]
    pub const fn node(&self) -> Option<NodeId> {
        self.node
    }
}

impl fmt::Display for ValidationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.node {
            Some(node) => write!(formatter, "{} at Core node {}", self.reason, node.value()),
            None => self.reason.fmt(formatter),
        }
    }
}

impl Error for ValidationError {}

fn valid_upper_spelling(spelling: &str) -> bool {
    let mut bytes = spelling.bytes();
    bytes.next().is_some_and(|byte| byte.is_ascii_uppercase())
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        && !matches!(spelling, "Int" | "Bool" | "Unit")
}

fn valid_lower_spelling(spelling: &str) -> bool {
    let mut bytes = spelling.bytes();
    bytes.next().is_some_and(|byte| byte.is_ascii_lowercase())
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}

fn constructor_belongs_to_owner(owner: &ResolvedNominalType, constructor: ConstructorId) -> bool {
    if constructor.owner() != owner.id {
        return false;
    }
    usize::try_from(constructor.constructor())
        .ok()
        .and_then(|index| owner.constructors.get(index))
        .is_some_and(|owned| *owned == constructor)
}

fn span_contains(outer: Span, inner: Span) -> bool {
    outer.source() == inner.source()
        && outer.range().start() <= inner.range().start()
        && inner.range().end() <= outer.range().end()
}

fn representation_provenance_span(node: &ResolvedTypeProvenanceNode) -> Span {
    match node {
        ResolvedTypeProvenanceNode::Fact(span)
        | ResolvedTypeProvenanceNode::Tuple { span, .. }
        | ResolvedTypeProvenanceNode::Function { span, .. }
        | ResolvedTypeProvenanceNode::Application { span, .. } => *span,
    }
}

/// Consumes unchecked Core and returns the capability required by consumers.
///
/// `sources` is the complete set admitted to the current compilation. Every
/// node and binder origin must lead to a checked span in that set.
///
/// # Errors
///
/// Returns a structured internal failure if graph, scope, type, dialect, or
/// provenance invariants do not hold.
pub fn validate(
    program: UnvalidatedProgram,
    sources: &[&SourceFile],
) -> Result<ValidatedProgram, ValidationError> {
    validate_family(program, sources)
}

pub(super) fn validate_family<F: CoreOperationFamily + ScopeFamily>(
    program: UnvalidatedCoreProgram<F>,
    sources: &[&SourceFile],
) -> Result<ValidatedCoreProgram<F>, ValidationError> {
    if let Err(error) = Validator::new(&program, sources).run() {
        program.discard_iteratively();
        return Err(error);
    }

    let (registry, method_evidence, method_evidence_anchors, arena, stored_nodes, root) =
        program.into_parts();
    let mut nodes = Vec::with_capacity(stored_nodes.len());
    for (index, stored) in stored_nodes.into_iter().enumerate() {
        let node = node_id(arena, index)?;
        let Some(origin) = stored.origin else {
            return Err(ValidationError::new(
                ValidationReason::Provenance,
                Some(node),
            ));
        };
        nodes.push(CoreTypedExpr {
            ty: stored.ty,
            effects: stored.effects,
            origin,
            kind: stored.kind,
        });
    }

    Ok(ValidatedCoreProgram::new(CoreProgram::new(
        registry,
        method_evidence,
        method_evidence_anchors,
        arena,
        nodes,
        root,
    )))
}

pub(super) fn validate_effect_family(
    program: UnvalidatedCoreProgram<super::effect::EffectOperationFamily>,
    sources: &[&SourceFile],
) -> Result<ValidatedCoreProgram<super::effect::EffectOperationFamily>, ValidationError> {
    let mut validator = Validator::new(&program, sources);
    if let Err(error) = validator.run_effect() {
        program.discard_iteratively();
        return Err(error);
    }
    let (registry, method_evidence, anchors, arena, stored, root) = program.into_parts();
    let mut nodes = Vec::with_capacity(stored.len());
    for (index, stored) in stored.into_iter().enumerate() {
        let id = node_id(arena, index)?;
        let Some(origin) = stored.origin else {
            return Err(ValidationError::new(ValidationReason::Provenance, Some(id)));
        };
        nodes.push(CoreTypedExpr {
            ty: stored.ty,
            effects: stored.effects,
            origin,
            kind: stored.kind,
        });
    }
    Ok(ValidatedCoreProgram::new(CoreProgram::new(
        registry,
        method_evidence,
        anchors,
        arena,
        nodes,
        root,
    )))
}

pub(super) fn validate_effect_modules_family(
    program: UnvalidatedCoreProgram<super::effect::EffectOperationFamily>,
    sources: &[&SourceFile],
    module_sources: &[(ModuleId, SourceId)],
) -> Result<ValidatedCoreProgram<super::effect::EffectOperationFamily>, ValidationError> {
    let mut validator = match Validator::new_modules(&program, sources, module_sources) {
        Ok(validator) => validator,
        Err(error) => {
            program.discard_iteratively();
            return Err(error);
        }
    };
    if let Err(error) = validator.run_effect() {
        program.discard_iteratively();
        return Err(error);
    }
    let (registry, method_evidence, anchors, arena, stored, root) = program.into_parts();
    let mut nodes = Vec::with_capacity(stored.len());
    for (index, stored) in stored.into_iter().enumerate() {
        let id = node_id(arena, index)?;
        let Some(origin) = stored.origin else {
            return Err(ValidationError::new(ValidationReason::Provenance, Some(id)));
        };
        nodes.push(CoreTypedExpr {
            ty: stored.ty,
            effects: stored.effects,
            origin,
            kind: stored.kind,
        });
    }
    Ok(ValidatedCoreProgram::new(CoreProgram::new(
        registry,
        method_evidence,
        anchors,
        arena,
        nodes,
        root,
    )))
}

/// Consumes unchecked Core assembled from multiple canonical modules.
///
/// `module_sources` is the explicit one-to-one relation between every module
/// admitted to the compilation and its canonical source. Registry and source
/// binder identities are checked against that relation rather than inferred
/// from the program root.
///
/// # Errors
///
/// Returns a structured internal failure if the module/source relation is
/// missing, duplicated, forged, or if any ordinary Core invariant fails.
pub fn validate_modules(
    program: UnvalidatedProgram,
    sources: &[&SourceFile],
    module_sources: &[(ModuleId, SourceId)],
) -> Result<ValidatedProgram, ValidationError> {
    let mut validator =
        match Validator::<PureOperationFamily>::new_modules(&program, sources, module_sources) {
            Ok(validator) => validator,
            Err(error) => {
                program.discard_iteratively();
                return Err(error);
            }
        };
    if let Err(error) = validator.run() {
        program.discard_iteratively();
        return Err(error);
    }

    let (registry, method_evidence, method_evidence_anchors, arena, stored_nodes, root) =
        program.into_parts();
    let mut nodes = Vec::with_capacity(stored_nodes.len());
    for (index, stored) in stored_nodes.into_iter().enumerate() {
        let node = node_id(arena, index)?;
        let Some(origin) = stored.origin else {
            return Err(ValidationError::new(
                ValidationReason::Provenance,
                Some(node),
            ));
        };
        nodes.push(TypedExpr {
            ty: stored.ty,
            effects: stored.effects,
            origin,
            kind: stored.kind,
        });
    }

    Ok(ValidatedProgram::new(PureProgram::new(
        registry,
        method_evidence,
        method_evidence_anchors,
        arena,
        nodes,
        root,
    )))
}

struct Validator<'program, 'source, F: CoreOperationFamily = PureOperationFamily> {
    program: &'program UnvalidatedCoreProgram<F>,
    sources: HashMap<SourceId, &'source SourceFile>,
    module_sources: Option<HashMap<ModuleId, SourceId>>,
    binders: HashMap<BinderId, &'program TypedBinder>,
    type_work: Cell<usize>,
    #[cfg(test)]
    owner_parameter_index_work: Cell<usize>,
    #[cfg(test)]
    newtype_conversion_parameter_work: Cell<usize>,
    #[cfg(test)]
    type_validation_pending_peak: Cell<usize>,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum ScopeRequirementKey {
    Binder(BinderId),
    Resume(super::effect::HandlerId, crate::resolved::ResumeId),
}

#[derive(Clone, Copy)]
struct ScopeRequirement {
    occurrence: NodeId,
    paths: u8,
}

type ScopeRequirements = HashMap<ScopeRequirementKey, ScopeRequirement>;

pub(super) trait ScopeFamily: CoreOperationFamily {
    fn resume_capability(
        _kind: &Self::Kind,
    ) -> Option<(super::effect::HandlerId, crate::resolved::ResumeId)> {
        None
    }

    fn clause_capability(
        _kind: &Self::Kind,
        _child: usize,
    ) -> Option<(super::effect::HandlerId, crate::resolved::ResumeId)> {
        None
    }

    fn visit_operation_child_binders(
        _kind: &Self::Kind,
        _child: usize,
        _visit: &mut dyn FnMut(BinderId),
    ) {
    }
}

impl ScopeFamily for PureOperationFamily {}

impl ScopeFamily for super::effect::EffectOperationFamily {
    fn resume_capability(
        kind: &Self::Kind,
    ) -> Option<(super::effect::HandlerId, crate::resolved::ResumeId)> {
        let super::effect::EffectExprKind::Operation(super::effect::EffectOperation::Resume(
            resume,
        )) = kind
        else {
            return None;
        };
        Some((resume.handler(), resume.owner()))
    }

    fn clause_capability(
        kind: &Self::Kind,
        child: usize,
    ) -> Option<(super::effect::HandlerId, crate::resolved::ResumeId)> {
        let super::effect::EffectExprKind::Operation(super::effect::EffectOperation::Handler(
            handler,
        )) = kind
        else {
            return None;
        };
        child
            .checked_sub(1)
            .and_then(|index| handler.clauses().get(index))
            .map(|clause| (handler.id(), clause.resume()))
    }

    fn visit_operation_child_binders(
        kind: &Self::Kind,
        child: usize,
        visit: &mut dyn FnMut(BinderId),
    ) {
        let super::effect::EffectExprKind::Operation(super::effect::EffectOperation::Handler(
            handler,
        )) = kind
        else {
            return;
        };
        let Some(clause) = child
            .checked_sub(1)
            .and_then(|index| handler.clauses().get(index))
        else {
            return;
        };
        for binder in clause.pattern().binder_iter() {
            visit(binder.id());
        }
    }
}

impl<'program, 'source, F: CoreOperationFamily + ScopeFamily> Validator<'program, 'source, F> {
    fn new(program: &'program UnvalidatedCoreProgram<F>, sources: &[&'source SourceFile]) -> Self {
        Self {
            program,
            sources: sources
                .iter()
                .map(|source| (source.id(), *source))
                .collect(),
            module_sources: None,
            binders: HashMap::new(),
            type_work: Cell::new(0),
            #[cfg(test)]
            owner_parameter_index_work: Cell::new(0),
            #[cfg(test)]
            newtype_conversion_parameter_work: Cell::new(0),
            #[cfg(test)]
            type_validation_pending_peak: Cell::new(0),
        }
    }

    fn new_modules(
        program: &'program UnvalidatedCoreProgram<F>,
        sources: &[&'source SourceFile],
        module_sources: &[(ModuleId, SourceId)],
    ) -> Result<Self, ValidationError> {
        let mut validator = Self::new(program, sources);
        if validator.sources.len() != sources.len() {
            return Err(ValidationError::new(ValidationReason::Registry, None));
        }
        let mut relation = HashMap::new();
        let mut mapped_sources = HashSet::new();
        relation
            .try_reserve(module_sources.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        mapped_sources
            .try_reserve(module_sources.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        for (module, source) in module_sources.iter().copied() {
            if !validator.sources.contains_key(&source)
                || relation.insert(module, source).is_some()
                || !mapped_sources.insert(source)
            {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            }
        }
        if mapped_sources.len() != validator.sources.len() {
            return Err(ValidationError::new(ValidationReason::Registry, None));
        }
        validator.module_sources = Some(relation);
        Ok(validator)
    }

    fn run(&mut self) -> Result<(), ValidationError> {
        let nominal_parameter_owners = self.validate_registry()?;
        let authenticated_method_evidence = self.validate_method_evidence_authority()?;
        self.validate_envelopes(&authenticated_method_evidence)?;
        self.validate_graph()?;
        let abstraction_owners = self.collect_binders(&authenticated_method_evidence)?;
        let type_binders =
            self.collect_type_binders(&nominal_parameter_owners, &abstraction_owners)?;
        self.validate_method_evidence_type_owners(&type_binders)?;
        self.validate_node_types(
            &nominal_parameter_owners,
            &type_binders,
            &authenticated_method_evidence,
        )?;
        self.validate_scopes()?;
        self.validate_type_scopes()
    }

    fn validate_method_evidence_type_owners(
        &self,
        type_binders: &CoreTypeBinders<'_>,
    ) -> Result<(), ValidationError> {
        for anchor in &self.program.method_evidence_anchors {
            if !matches!(anchor.role, MethodEvidenceAnchorRole::Adapter { .. }) {
                continue;
            }
            let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                self.pure_kind(anchor.node)?
            else {
                return Err(ValidationError::new(
                    ValidationReason::TypeOperation,
                    Some(anchor.node),
                ));
            };
            for (parameter, _) in abstraction.parameters() {
                self.charge_type_work(1)?;
                if !matches!(parameter, crate::types::TypeVariableId::Generated(_))
                    || type_binders
                        .get(parameter)
                        .is_none_or(|(_, owner)| *owner != anchor.node)
                {
                    return Err(ValidationError::new(
                        ValidationReason::TypeOperation,
                        Some(anchor.node),
                    ));
                }
            }
        }
        Ok(())
    }

    fn validate_method_evidence_authority(&self) -> Result<HashSet<NodeId>, ValidationError> {
        let catalog = &self.program.method_evidence;
        self.validate_method_evidence_catalog_applications()?;
        let per_anchor_lookup_work = catalog
            .method_count()
            .checked_add(
                catalog
                    .implementation_owners()
                    .len()
                    .checked_mul(8)
                    .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?,
            )
            .and_then(|work| {
                catalog
                    .occurrence_count()
                    .checked_mul(2)
                    .and_then(|occurrences| work.checked_add(occurrences))
            })
            .and_then(|work| work.checked_add(self.program.method_evidence_anchors.len()))
            .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?;
        self.charge_type_work(
            per_anchor_lookup_work
                .checked_mul(self.program.method_evidence_anchors.len())
                .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?,
        )?;
        let authority_rows = catalog
            .expectations()
            .len()
            .checked_mul(2)
            .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?
            .checked_add(
                self.program
                    .method_evidence_anchors
                    .len()
                    .checked_mul(4)
                    .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?,
            )
            .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?;
        self.charge_type_work(authority_rows)?;
        let mut consumed = Vec::new();
        consumed
            .try_reserve_exact(catalog.expectations().len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        consumed.resize(catalog.expectations().len(), false);
        let mut anchors = HashMap::new();
        anchors
            .try_reserve(self.program.method_evidence_anchors.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        for anchor in &self.program.method_evidence_anchors {
            let Some(expected) = catalog.expectations().get(anchor.expectation) else {
                return Err(ValidationError::new(
                    ValidationReason::NodeType,
                    Some(anchor.node),
                ));
            };
            let mut expectation_work = TypeWorkBudget::with_limit(
                CORE_VALIDATION_TYPE_WORK_LIMIT.saturating_sub(self.type_work.get()),
            );
            let expectation_matches = super::dialect::method_evidence_anchor_matches_expectation(
                catalog,
                expected,
                anchor.owner,
                anchor.requirement,
                anchor.role,
                &anchor.application,
                &mut expectation_work,
            );
            self.charge_type_work(expectation_work.used())?;
            let expectation_matches = expectation_matches.map_err(|()| {
                ValidationError::new(ValidationReason::Resource, Some(anchor.node))
            })?;
            if std::mem::replace(&mut consumed[anchor.expectation], true)
                || expected.occurrence != anchor.occurrence
                || expected.method != anchor.method
                || !expectation_matches
                || (!matches!(
                    anchor.role,
                    MethodEvidenceAnchorRole::AdapterEdge { .. }
                        | MethodEvidenceAnchorRole::ImplementationOwner { .. }
                ) && catalog.method(anchor.method).is_none())
                || self.node(anchor.node).is_err()
                || (!matches!(
                    anchor.role,
                    MethodEvidenceAnchorRole::ImplementationOwner { .. }
                ) && anchors.insert(anchor.node, anchor).is_some())
            {
                return Err(ValidationError::new(
                    ValidationReason::NodeType,
                    Some(anchor.node),
                ));
            }
            let exact_identity_work = match anchor.role {
                MethodEvidenceAnchorRole::Adapter { .. } => 1,
                MethodEvidenceAnchorRole::AdapterEdge { .. } => 4,
                _ => 0,
            };
            self.charge_type_work(exact_identity_work)?;
            let role_matches = match (expected.role, anchor.role) {
                (
                    MethodEvidenceExpectedRole::ImplementationOwner { owner },
                    MethodEvidenceAnchorRole::ImplementationOwner {
                        implementation,
                        binder,
                    },
                ) => {
                    catalog
                        .implementation_owners()
                        .get(owner)
                        .is_some_and(|expected| {
                            expected.implementation == implementation
                                && expected.binder == binder
                                && anchor.owner
                                    == Some(MethodEvidenceOwner::Implementation(implementation))
                                && anchor.requirement.is_none()
                        })
                        && self.validate_implementation_owner_anchor(anchor, owner)?
                }
                (
                    MethodEvidenceExpectedRole::Domain { domain },
                    MethodEvidenceAnchorRole::Domain { binder },
                ) => catalog.domains().get(domain).is_some_and(|domain| {
                    Some(domain.owner) == anchor.owner
                        && Some(domain.requirement) == anchor.requirement
                        && domain.requirement_position == domain.requirement.declaration()
                        && domain.method == anchor.method
                        && domain.method_position == domain.method.declaration()
                        && matches!(
                            self.program.nodes.get(anchor.node.index().unwrap_or(usize::MAX))
                                .and_then(|node| F::pure(&node.kind)),
                            Some(PureExprKind::Value(PureValue::Function(function)))
                                if function.parameter().id() == binder
                        )
                }),
                (
                    MethodEvidenceExpectedRole::Application { domain, producer },
                    MethodEvidenceAnchorRole::Application {
                        producer: actual_producer,
                    },
                ) => catalog.domains().get(domain).is_some_and(|domain| {
                    Some(domain.owner) == anchor.owner
                        && Some(domain.requirement) == anchor.requirement
                        && domain.method == anchor.method
                        && method_evidence_producer_matches(catalog, producer, actual_producer)
                }),
                (
                    MethodEvidenceExpectedRole::Instantiation { .. },
                    MethodEvidenceAnchorRole::Instantiation { .. },
                ) => true,
                (
                    MethodEvidenceExpectedRole::Adapter { adapter },
                    MethodEvidenceAnchorRole::Adapter {
                        implementation: actual,
                        selection_node,
                    },
                ) => catalog.adapters().get(adapter).is_some_and(|row| {
                    actual == row.implementation && selection_node == row.selection_node
                }),
                (
                    MethodEvidenceExpectedRole::AdapterEdge { adapter, ordinal },
                    MethodEvidenceAnchorRole::AdapterEdge {
                        adapter: actual,
                        adapter_selection_node,
                        ordinal: actual_ordinal,
                        producer_node,
                        producer_selection_node,
                        producer_binder,
                        producer: actual_producer,
                    },
                ) => catalog.adapters().get(adapter).is_some_and(|row| {
                    actual == row.implementation
                        && adapter_selection_node == row.selection_node
                        && ordinal == actual_ordinal
                        && matches!(
                            self.program.nodes.get(anchor.node.index().unwrap_or(usize::MAX))
                                .and_then(|node| F::pure(&node.kind)),
                            Some(PureExprKind::Computation(PureComputation::Apply(application)))
                                if application.argument() == producer_node
                        )
                        && row.prerequisites.get(ordinal).is_some_and(|edge| {
                            Some(edge.owner) == anchor.owner
                                && Some(edge.requirement) == anchor.requirement
                                && edge.method == anchor.method
                                && match edge.producer {
                                    super::dialect::MethodEvidenceExpectedProducer::Authenticated(
                                        producer,
                                    ) => method_evidence_producer_matches(
                                        catalog,
                                        producer,
                                        actual_producer,
                                    ),
                                    super::dialect::MethodEvidenceExpectedProducer::Monomorphic {
                                        selection_node,
                                        producer_scope_position: _,
                                        producer,
                                    } => {
                                        selection_node == producer_selection_node
                                            && producer == actual_producer
                                            && match (producer, producer_binder) {
                                                (
                                                    MethodEvidenceProducer::Abstract { .. },
                                                    Some(binder),
                                                ) => matches!(
                                                    self.program.nodes.get(
                                                        producer_node
                                                            .index()
                                                            .unwrap_or(usize::MAX)
                                                    ).and_then(|node| F::pure(&node.kind)),
                                                    Some(PureExprKind::Variable(variable))
                                                        if variable.binder() == binder
                                                ),
                                                (
                                                    MethodEvidenceProducer::Adapter { .. },
                                                    None,
                                                ) => true,
                                                _ => false,
                                            }
                                    }
                                }
                        })
                }),
                _ => false,
            };
            if !role_matches {
                return Err(ValidationError::new(
                    ValidationReason::NodeType,
                    Some(anchor.node),
                ));
            }
        }
        if consumed.iter().any(|consumed| !consumed) {
            return Err(ValidationError::new(ValidationReason::NodeType, None));
        }
        let mut carriers = HashSet::new();
        self.charge_type_work(self.program.nodes.len())?;
        carriers
            .try_reserve(self.program.nodes.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        self.validate_method_evidence_domain_order(&anchors)?;
        self.validate_method_evidence_owner_envelopes(&anchors, &mut carriers)?;
        for anchor in anchors.values() {
            match anchor.role {
                MethodEvidenceAnchorRole::ImplementationOwner { .. } => {}
                MethodEvidenceAnchorRole::Domain { .. } => {
                    self.validate_method_evidence_domain(anchor, &anchors, &mut carriers)?;
                }
                MethodEvidenceAnchorRole::Instantiation { binder } => {
                    self.validate_method_instantiation(anchor, binder, &anchors)?;
                    let PureExprKind::Computation(PureComputation::TypeApplication(application)) =
                        self.pure_kind(anchor.node)?
                    else {
                        unreachable!()
                    };
                    carriers.insert(application.function());
                    carriers.insert(anchor.node);
                }
                MethodEvidenceAnchorRole::Application { .. } => {
                    self.validate_method_application(anchor, &anchors)?;
                    let PureExprKind::Computation(PureComputation::Apply(application)) =
                        self.pure_kind(anchor.node)?
                    else {
                        unreachable!()
                    };
                    let MethodEvidenceExpectedRole::Application { domain, .. } = self
                        .program
                        .method_evidence
                        .expectations()
                        .get(anchor.expectation)
                        .ok_or_else(|| {
                            ValidationError::new(ValidationReason::NodeType, Some(anchor.node))
                        })?
                        .role
                    else {
                        unreachable!()
                    };
                    let target = self
                        .program
                        .method_evidence
                        .domains()
                        .get(domain)
                        .ok_or_else(|| {
                            ValidationError::new(ValidationReason::NodeType, Some(anchor.node))
                        })?;
                    let expected_binder = match target.owner {
                        MethodEvidenceOwner::Global(binder) => binder,
                        MethodEvidenceOwner::Implementation(implementation) => {
                            self.program
                                .method_evidence
                                .implementation_owner(implementation)
                                .ok_or_else(|| {
                                    ValidationError::new(
                                        ValidationReason::NodeType,
                                        Some(anchor.node),
                                    )
                                })?
                                .binder
                        }
                    };
                    let function = application.function();
                    match self.pure_kind(function)? {
                        PureExprKind::Computation(PureComputation::TypeApplication(operation)) => {
                            let source = operation.function();
                            if !matches!(
                                self.pure_kind(source)?,
                                PureExprKind::Variable(variable)
                                    if variable.binder() == expected_binder
                            ) {
                                return Err(ValidationError::new(
                                    ValidationReason::NodeType,
                                    Some(anchor.node),
                                ));
                            }
                            carriers.insert(source);
                            carriers.insert(function);
                        }
                        PureExprKind::Variable(variable)
                            if variable.binder() == expected_binder =>
                        {
                            carriers.insert(function);
                        }
                        _ if anchors.get(&function).is_some_and(|previous| {
                            let Some(MethodEvidenceExpectedRole::Application {
                                domain: previous_domain,
                                ..
                            }) = self
                                .program
                                .method_evidence
                                .expectations()
                                .get(previous.expectation)
                                .map(|expected| expected.role)
                            else {
                                return false;
                            };
                            previous_domain.checked_add(1) == Some(domain)
                                && self
                                    .program
                                    .method_evidence
                                    .domains()
                                    .get(previous_domain)
                                    .is_some_and(|previous| previous.owner == target.owner)
                        }) => {}
                        _ => {
                            return Err(ValidationError::new(
                                ValidationReason::NodeType,
                                Some(anchor.node),
                            ));
                        }
                    }
                    carriers.insert(application.argument());
                    carriers.insert(anchor.node);
                }
                MethodEvidenceAnchorRole::Adapter { .. } => {
                    let MethodEvidenceExpectedRole::Adapter { adapter } = self
                        .program
                        .method_evidence
                        .expectations()
                        .get(anchor.expectation)
                        .ok_or_else(|| {
                            ValidationError::new(ValidationReason::NodeType, Some(anchor.node))
                        })?
                        .role
                    else {
                        return Err(ValidationError::new(
                            ValidationReason::NodeType,
                            Some(anchor.node),
                        ));
                    };
                    if !self.validate_adapter_anchor(anchor, adapter, &anchors)? {
                        return Err(ValidationError::new(
                            ValidationReason::NodeType,
                            Some(anchor.node),
                        ));
                    }
                    self.validate_adapter_prerequisite_sequence(anchor, &anchors)?;
                }
                MethodEvidenceAnchorRole::AdapterEdge { .. } => {
                    self.validate_adapter_edge(anchor, &anchors)?;
                    let PureExprKind::Computation(PureComputation::Apply(application)) =
                        self.pure_kind(anchor.node)?
                    else {
                        unreachable!()
                    };
                    carriers.insert(application.argument());
                    carriers.insert(anchor.node);
                }
            }
        }
        for anchor in anchors
            .values()
            .filter(|anchor| matches!(anchor.role, MethodEvidenceAnchorRole::Adapter { .. }))
        {
            carriers.insert(anchor.node);
            let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                self.pure_kind(anchor.node)?
            else {
                unreachable!()
            };
            let mut current = abstraction.body();
            while let PureExprKind::Computation(PureComputation::Apply(application)) =
                self.pure_kind(current)?
            {
                carriers.insert(current);
                current = application.function();
            }
            let PureExprKind::Computation(PureComputation::TypeApplication(application)) =
                self.pure_kind(current)?
            else {
                return Err(ValidationError::new(
                    ValidationReason::TypeOperation,
                    Some(current),
                ));
            };
            carriers.insert(current);
            carriers.insert(application.function());
        }
        self.validate_method_evidence_carrier_incoming(&carriers)?;
        Ok(carriers)
    }

    fn validate_method_evidence_catalog_applications(&self) -> Result<(), ValidationError> {
        let catalog = &self.program.method_evidence;
        let empty_type_binders = CoreTypeBinders::new();
        let mut previous_method = None;
        let mut previous_interface_parameters = None;
        for method in catalog.methods() {
            self.charge_type_work(method.interface_parameters.len().saturating_add(1))?;
            if previous_method.is_some_and(|previous| previous >= method.id)
                || method.interface_parameters.is_empty()
            {
                return Err(ValidationError::new(ValidationReason::NodeType, None));
            }
            previous_method = Some(method.id);
            if let Some((interface, parameters)) = previous_interface_parameters
                && interface == method.id.interface()
                && parameters != method.interface_parameters.as_ref()
            {
                return Err(ValidationError::new(ValidationReason::NodeType, None));
            }
            previous_interface_parameters =
                Some((method.id.interface(), method.interface_parameters.as_ref()));
            let mut previous_parameter = None;
            for parameter in &method.interface_parameters {
                let Some(canonical) = self.program.registry.type_variable(*parameter) else {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                };
                if parameter.module() != Some(method.id.interface().module())
                    || previous_parameter.is_some_and(|previous| previous >= parameter.local())
                {
                    return Err(ValidationError::new(ValidationReason::NodeType, None));
                }
                previous_parameter = Some(parameter.local());
                self.charge_kind(&canonical.kind)?;
            }
        }

        let validate_application = |validator: &Self,
                                    method_id: crate::interface::MethodId,
                                    application: &InterfaceApplication|
         -> Result<(), ValidationError> {
            let method = catalog
                .method(method_id)
                .ok_or_else(|| ValidationError::new(ValidationReason::NodeType, None))?;
            if application.interface() != method_id.interface()
                || application.arguments().len() != method.interface_parameters.len()
            {
                return Err(ValidationError::new(ValidationReason::NodeType, None));
            }
            for (parameter, argument) in method
                .interface_parameters
                .iter()
                .zip(application.arguments())
            {
                let canonical = validator
                    .program
                    .registry
                    .type_variable(*parameter)
                    .ok_or_else(|| ValidationError::new(ValidationReason::Registry, None))?;
                let Some(actual_kind) = validator.synthesize_monotype_kind(
                    argument,
                    MonotypeVariableKinds::Core(&empty_type_binders),
                )?
                else {
                    return Err(ValidationError::new(ValidationReason::NodeType, None));
                };
                if !validator.same_kind_charged(&canonical.kind, &actual_kind)? {
                    return Err(ValidationError::new(ValidationReason::NodeType, None));
                }
            }
            Ok(())
        };

        for owner in catalog.implementation_owners() {
            validate_application(self, owner.implementation.method(), &owner.application)?;
        }
        for domain in catalog.domains() {
            validate_application(self, domain.method, &domain.application)?;
        }
        for occurrence in catalog.occurrences() {
            let method = occurrence.checked_method.or_else(|| {
                catalog
                    .methods()
                    .iter()
                    .find(|method| {
                        method.id.interface() == occurrence.checked_application.interface()
                    })
                    .map(|method| method.id)
            });
            let Some(method) = method else {
                return Err(ValidationError::new(ValidationReason::NodeType, None));
            };
            validate_application(self, method, &occurrence.checked_application)?;
            self.charge_type_work(1)?;
            if occurrence.selection.interface() != occurrence.checked_application.interface()
                || occurrence.selection.arguments().len()
                    != occurrence.checked_application.arguments().len()
            {
                return Err(ValidationError::new(ValidationReason::NodeType, None));
            }
            for (selected, checked) in occurrence
                .selection
                .arguments()
                .iter()
                .zip(occurrence.checked_application.arguments())
            {
                if !self.same_type_charged(selected, checked)? {
                    return Err(ValidationError::new(ValidationReason::NodeType, None));
                }
            }
        }
        for adapter in catalog.adapters() {
            for edge in &adapter.prerequisites {
                validate_application(self, edge.method, &edge.application)?;
                let method = catalog
                    .method(edge.method)
                    .ok_or_else(|| ValidationError::new(ValidationReason::NodeType, None))?;
                if edge.interface_parameters.as_ref() != method.interface_parameters.as_ref() {
                    return Err(ValidationError::new(ValidationReason::NodeType, None));
                }
            }
        }
        Ok(())
    }

    fn validate_method_evidence_carrier_incoming(
        &self,
        carriers: &HashSet<NodeId>,
    ) -> Result<(), ValidationError> {
        let mut owner_edges = HashSet::new();
        self.charge_type_work(self.program.nodes.len())?;
        owner_edges
            .try_reserve(self.program.nodes.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        self.charge_type_work(self.program.nodes.len())?;
        for (index, stored) in self.program.nodes.iter().enumerate() {
            let parent = node_id(self.program.arena, index)?;
            let Some(PureExprKind::Computation(PureComputation::RecursiveBind(group))) =
                F::pure(&stored.kind)
            else {
                continue;
            };
            for member in group.members() {
                self.charge_type_work(1)?;
                self.charge_type_work(
                    self.program
                        .method_evidence_anchors
                        .len()
                        .checked_add(self.program.method_evidence.domains().len())
                        .ok_or_else(|| {
                            ValidationError::new(ValidationReason::Resource, Some(parent))
                        })?,
                )?;
                if self.program.method_evidence_anchors.iter().any(|anchor| {
                    anchor.node == member.initializer()
                        && matches!(
                            anchor.role,
                            MethodEvidenceAnchorRole::ImplementationOwner { binder, .. }
                                if binder == member.binder().id()
                        )
                }) || self
                    .program
                    .method_evidence
                    .domains()
                    .iter()
                    .any(|domain| domain.owner == MethodEvidenceOwner::Global(member.binder().id()))
                {
                    owner_edges.insert((member.initializer(), parent));
                }
            }
        }
        self.charge_type_work(self.program.nodes.len())?;
        for (index, stored) in self.program.nodes.iter().enumerate() {
            let parent = node_id(self.program.arena, index)?;
            for child_index in 0..F::child_count(&stored.kind) {
                self.charge_type_work(1)?;
                let child = F::child_at(&stored.kind, child_index).ok_or_else(|| {
                    ValidationError::new(ValidationReason::NodeType, Some(parent))
                })?;
                if !carriers.contains(&child)
                    || !self.type_contains_forall_charged(&self.node(child)?.ty)?
                {
                    continue;
                }
                if !carriers.contains(&parent) && !owner_edges.contains(&(child, parent)) {
                    return Err(ValidationError::new(
                        ValidationReason::NodeType,
                        Some(child),
                    ));
                }
            }
        }
        Ok(())
    }

    fn type_contains_forall_charged(&self, root: &Type) -> Result<bool, ValidationError> {
        let mut pending = Vec::new();
        self.charge_type_work(1)?;
        pending
            .try_reserve(1)
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        pending.push(root);
        while let Some(ty) = pending.pop() {
            self.charge_type_work(1)?;
            match ty {
                Type::Forall(_, _) => return Ok(true),
                Type::EffectfulFunction(domain, computation) => {
                    if !F::ALLOWS_EFFECTFUL_TYPES {
                        return Ok(true);
                    }
                    self.schedule_effectful_type_children(&mut pending, domain, computation)?;
                }
                Type::Application(function, argument) | Type::Function(function, argument) => {
                    self.charge_type_work(2)?;
                    pending
                        .try_reserve(2)
                        .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
                    pending.push(argument);
                    pending.push(function);
                }
                Type::Tuple(elements) => {
                    self.charge_type_work(elements.len())?;
                    pending
                        .try_reserve(elements.len())
                        .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
                    pending.extend(elements);
                }
                Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_) => {}
            }
        }
        Ok(false)
    }

    fn schedule_effectful_type_children<'a>(
        &self,
        pending: &mut Vec<&'a Type>,
        domain: &'a Type,
        computation: &'a crate::types::ComputationType,
    ) -> Result<(), ValidationError> {
        let row = computation.effects();
        let row_arguments = row
            .known()
            .iter()
            .chain(row.tail().into_iter().flat_map(|tail| tail.lacks()))
            .try_fold(0_usize, |count, instance| {
                count.checked_add(instance.arguments().len())
            })
            .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?;
        let children = row_arguments
            .checked_add(2)
            .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?;
        let tail_metadata = row
            .tail()
            .map_or(Some(0), |tail| tail.lacks().len().checked_add(1));
        let metadata = tail_metadata.and_then(|tail| row.known().len().checked_add(tail));
        self.charge_type_work(
            children
                .checked_add(
                    metadata
                        .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?,
                )
                .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?,
        )?;
        pending
            .try_reserve(children)
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        for instance in row.known() {
            pending.extend(instance.arguments());
        }
        if let Some(tail) = row.tail() {
            for instance in tail.lacks() {
                pending.extend(instance.arguments());
            }
        }
        pending.push(computation.value());
        pending.push(domain);
        Ok(())
    }

    fn validate_method_evidence_domain_order(
        &self,
        anchors: &HashMap<NodeId, &MethodEvidenceAnchor>,
    ) -> Result<(), ValidationError> {
        let domains = self.program.method_evidence.domains();
        for (domain_index, domain) in domains.iter().enumerate() {
            self.charge_type_work(1)?;
            self.charge_type_work(anchors.len())?;
            let current = anchors
                .values()
                .find(|anchor| {
                    matches!(
                        self.program
                            .method_evidence
                            .expectations()
                            .get(anchor.expectation)
                            .map(|expected| expected.role),
                        Some(MethodEvidenceExpectedRole::Domain { domain }) if domain == domain_index
                    )
                })
                .copied()
                .ok_or_else(|| ValidationError::new(ValidationReason::NodeType, None))?;
            let PureExprKind::Value(PureValue::Function(function)) =
                self.pure_kind(current.node)?
            else {
                return Err(ValidationError::new(
                    ValidationReason::NodeType,
                    Some(current.node),
                ));
            };
            if let Some((next_index, _)) = domains
                .get(domain_index.saturating_add(1))
                .filter(|next| next.owner == domain.owner)
                .map(|next| (domain_index + 1, next))
            {
                self.charge_type_work(anchors.len())?;
                let next = anchors
                    .values()
                    .find(|anchor| {
                        matches!(
                            self.program
                                .method_evidence
                                .expectations()
                                .get(anchor.expectation)
                                .map(|expected| expected.role),
                            Some(MethodEvidenceExpectedRole::Domain { domain }) if domain == next_index
                        )
                    })
                    .copied()
                    .ok_or_else(|| ValidationError::new(ValidationReason::NodeType, Some(current.node)))?;
                if function.body() != next.node {
                    return Err(ValidationError::new(
                        ValidationReason::NodeType,
                        Some(current.node),
                    ));
                }
            } else if anchors.get(&function.body()).is_some_and(|anchor| {
                matches!(anchor.role, MethodEvidenceAnchorRole::Domain { .. })
            }) {
                return Err(ValidationError::new(
                    ValidationReason::NodeType,
                    Some(current.node),
                ));
            }
        }
        Ok(())
    }

    fn validate_method_evidence_owner_envelopes(
        &self,
        anchors: &HashMap<NodeId, &MethodEvidenceAnchor>,
        carriers: &mut HashSet<NodeId>,
    ) -> Result<(), ValidationError> {
        let domains = self.program.method_evidence.domains();
        for (index, domain) in domains.iter().enumerate() {
            self.charge_type_work(anchors.len())?;
            let domain_anchor = anchors
                .values()
                .find(|anchor| {
                    matches!(
                        self.program
                            .method_evidence
                            .expectations()
                            .get(anchor.expectation)
                            .map(|expected| expected.role),
                        Some(MethodEvidenceExpectedRole::Domain { domain: actual }) if actual == index
                    )
                })
                .copied()
                .ok_or_else(|| ValidationError::new(ValidationReason::NodeType, None))?;
            carriers.insert(domain_anchor.node);
            if index > 0 && domains[index - 1].owner == domain.owner {
                continue;
            }
            let (expected_binder, initializer) = match domain.owner {
                MethodEvidenceOwner::Global(binder) => {
                    let mut initializer = None;
                    for node in &self.program.nodes {
                        self.charge_type_work(1)?;
                        let Some(PureExprKind::Computation(PureComputation::RecursiveBind(group))) =
                            F::pure(&node.kind)
                        else {
                            continue;
                        };
                        for member in group.members() {
                            self.charge_type_work(1)?;
                            if member.binder().id() == binder
                                && initializer.replace(member.initializer()).is_some()
                            {
                                return Err(ValidationError::new(
                                    ValidationReason::NodeType,
                                    Some(domain_anchor.node),
                                ));
                            }
                        }
                    }
                    (
                        binder,
                        initializer.ok_or_else(|| {
                            ValidationError::new(
                                ValidationReason::NodeType,
                                Some(domain_anchor.node),
                            )
                        })?,
                    )
                }
                MethodEvidenceOwner::Implementation(implementation) => {
                    self.charge_type_work(self.program.method_evidence_anchors.len())?;
                    let owner = self
                        .program
                        .method_evidence
                        .implementation_owner(implementation)
                        .ok_or_else(|| {
                            ValidationError::new(
                                ValidationReason::NodeType,
                                Some(domain_anchor.node),
                            )
                        })?;
                    let owner_anchor = self
                        .program
                        .method_evidence_anchors
                        .iter()
                        .find(|anchor| {
                            matches!(
                                anchor.role,
                                MethodEvidenceAnchorRole::ImplementationOwner {
                                    implementation: actual,
                                    binder,
                                } if actual == implementation && binder == owner.binder
                            )
                        })
                        .ok_or_else(|| {
                            ValidationError::new(
                                ValidationReason::NodeType,
                                Some(domain_anchor.node),
                            )
                        })?;
                    (owner.binder, owner_anchor.node)
                }
            };
            let owner_root = if initializer == domain_anchor.node {
                if matches!(domain.owner, MethodEvidenceOwner::Global(_))
                    && self
                        .program
                        .registry
                        .global_parameter_row(expected_binder)
                        .is_some()
                {
                    return Err(ValidationError::new(
                        ValidationReason::NodeType,
                        Some(initializer),
                    ));
                }
                initializer
            } else {
                let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                    self.pure_kind(initializer)?
                else {
                    return Err(ValidationError::new(
                        ValidationReason::NodeType,
                        Some(initializer),
                    ));
                };
                if abstraction.body() != domain_anchor.node {
                    return Err(ValidationError::new(
                        ValidationReason::NodeType,
                        Some(initializer),
                    ));
                }
                match domain.owner {
                    MethodEvidenceOwner::Global(binder) => {
                        let row = self
                            .program
                            .registry
                            .global_parameter_row(binder)
                            .ok_or_else(|| {
                                ValidationError::new(ValidationReason::Registry, Some(initializer))
                            })?;
                        if row.parameters().len() != abstraction.parameters().len() {
                            return Err(ValidationError::new(
                                ValidationReason::Registry,
                                Some(initializer),
                            ));
                        }
                        for ((actual, actual_kind), expected) in
                            abstraction.parameters().iter().zip(row.parameters())
                        {
                            self.charge_type_work(1)?;
                            let canonical =
                                self.program.registry.type_variable(*expected).ok_or_else(
                                    || {
                                        ValidationError::new(
                                            ValidationReason::Registry,
                                            Some(initializer),
                                        )
                                    },
                                )?;
                            if actual != expected
                                || !self.same_kind_charged(actual_kind, &canonical.kind)?
                            {
                                return Err(ValidationError::new(
                                    ValidationReason::Registry,
                                    Some(initializer),
                                ));
                            }
                        }
                    }
                    MethodEvidenceOwner::Implementation(implementation) => {
                        self.charge_type_work(self.program.method_evidence_anchors.len())?;
                        let anchored = self.program.method_evidence_anchors.iter().any(|anchor| {
                            anchor.node == initializer
                                && matches!(
                                    anchor.role,
                                    MethodEvidenceAnchorRole::ImplementationOwner {
                                        implementation: actual,
                                        binder,
                                    } if actual == implementation && binder == expected_binder
                                )
                        });
                        if !anchored {
                            return Err(ValidationError::new(
                                ValidationReason::NodeType,
                                Some(initializer),
                            ));
                        }
                    }
                }
                carriers.insert(initializer);
                initializer
            };
            let mut exact_members = 0usize;
            for node in &self.program.nodes {
                self.charge_type_work(1)?;
                let Some(PureExprKind::Computation(PureComputation::RecursiveBind(group))) =
                    F::pure(&node.kind)
                else {
                    continue;
                };
                for member in group.members() {
                    self.charge_type_work(1)?;
                    if member.initializer() == owner_root {
                        if member.binder().id() != expected_binder {
                            return Err(ValidationError::new(
                                ValidationReason::NodeType,
                                Some(owner_root),
                            ));
                        }
                        exact_members = exact_members.checked_add(1).ok_or_else(|| {
                            ValidationError::new(ValidationReason::Resource, Some(owner_root))
                        })?;
                    }
                }
            }
            if exact_members != 1 {
                return Err(ValidationError::new(
                    ValidationReason::NodeType,
                    Some(owner_root),
                ));
            }
        }
        Ok(())
    }

    fn expected_method_scheme(
        &self,
        anchor: &MethodEvidenceAnchor,
    ) -> Result<IterativeTypeOwner, ValidationError> {
        self.expected_method_scheme_for(anchor.method, &anchor.application, anchor.node)
    }

    fn expected_method_scheme_for(
        &self,
        method_id: crate::interface::MethodId,
        application: &InterfaceApplication,
        node: NodeId,
    ) -> Result<IterativeTypeOwner, ValidationError> {
        let method = self
            .program
            .method_evidence
            .method(method_id)
            .ok_or_else(|| ValidationError::new(ValidationReason::NodeType, Some(node)))?;
        if application.interface() != method_id.interface()
            || application.arguments().len() != method.interface_parameters.len()
        {
            return Err(ValidationError::new(ValidationReason::NodeType, Some(node)));
        }
        let mut replacements = TypeReplacementMap::new();
        self.charge_type_work(method.interface_parameters.len())?;
        replacements
            .try_reserve(method.interface_parameters.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(node)))?;
        for (parameter, argument) in method
            .interface_parameters
            .iter()
            .zip(application.arguments())
        {
            replacements.insert_replacing(*parameter, self.clone_type_charged(argument)?);
        }
        let body = substitute_type_variables_with(
            &method.value_type,
            replacements.as_map(),
            |cells| self.charge_type_work(cells),
            || ValidationError::new(ValidationReason::Resource, None),
        )?;
        let mut parameters = Vec::new();
        self.charge_type_work(method.parameters.len())?;
        parameters
            .try_reserve(method.parameters.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(node)))?;
        for (parameter, kind) in &method.parameters {
            parameters.push((*parameter, self.clone_kind_charged(kind)?));
        }
        Ok(IterativeTypeOwner::new(Type::Forall(
            parameters.into_boxed_slice(),
            Box::new(body),
        )))
    }

    fn validate_implementation_owner_anchor(
        &self,
        anchor: &MethodEvidenceAnchor,
        owner: usize,
    ) -> Result<bool, ValidationError> {
        let expected = self
            .program
            .method_evidence
            .implementation_owners()
            .get(owner)
            .ok_or_else(|| ValidationError::new(ValidationReason::NodeType, Some(anchor.node)))?;
        let stored = self.node(anchor.node)?;
        if expected.source_parameters.is_empty() {
            if expected.head_type_parameter_count != 0
                || matches!(
                    F::pure(&stored.kind),
                    Some(PureExprKind::Computation(PureComputation::TypeAbstraction(
                        _
                    )))
                )
            {
                return Ok(false);
            }
            let mut initializer_matches = 0usize;
            for node in &self.program.nodes {
                self.charge_type_work(1)?;
                let Some(PureExprKind::Computation(PureComputation::RecursiveBind(group))) =
                    F::pure(&node.kind)
                else {
                    continue;
                };
                for member in group.members() {
                    self.charge_type_work(1)?;
                    if member.binder().id() == expected.binder {
                        if member.initializer() != anchor.node {
                            return Ok(false);
                        }
                        initializer_matches =
                            initializer_matches.checked_add(1).ok_or_else(|| {
                                ValidationError::new(ValidationReason::Resource, Some(anchor.node))
                            })?;
                    }
                }
            }
            return Ok(initializer_matches == 1);
        }
        let (
            Type::Forall(stored_parameters, stored_body),
            Some(PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction))),
        ) = (&stored.ty, F::pure(&stored.kind))
        else {
            return Ok(false);
        };
        if expected.head_type_parameter_count > expected.source_parameters.len()
            || stored_parameters.len() != expected.source_parameters.len()
            || abstraction.parameters().len() != expected.source_parameters.len()
            || stored_parameters.as_ref() != abstraction.parameters()
        {
            return Ok(false);
        }
        let mut fresh = HashSet::new();
        self.charge_type_work(abstraction.parameters().len())?;
        fresh
            .try_reserve(abstraction.parameters().len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(anchor.node)))?;
        for (((_, expected_kind), (actual, actual_kind)), (stored, stored_kind)) in expected
            .source_parameters
            .iter()
            .zip(abstraction.parameters())
            .zip(stored_parameters.iter())
        {
            if actual != stored
                || !matches!(actual, crate::types::TypeVariableId::Generated(_))
                || !fresh.insert(*actual)
                || !self.same_kind_charged(expected_kind, actual_kind)?
                || !self.same_kind_charged(actual_kind, stored_kind)?
            {
                return Ok(false);
            }
        }
        let body = self.node(abstraction.body())?;
        if !self.same_type_charged(stored_body, &body.ty)? {
            return Ok(false);
        }
        let mut initializer_matches = 0usize;
        for node in &self.program.nodes {
            self.charge_type_work(1)?;
            let Some(PureExprKind::Computation(PureComputation::RecursiveBind(group))) =
                F::pure(&node.kind)
            else {
                continue;
            };
            for member in group.members() {
                self.charge_type_work(1)?;
                if member.binder().id() == expected.binder {
                    if member.initializer() != anchor.node {
                        return Ok(false);
                    }
                    initializer_matches = initializer_matches.checked_add(1).ok_or_else(|| {
                        ValidationError::new(ValidationReason::Resource, Some(anchor.node))
                    })?;
                }
            }
        }
        Ok(initializer_matches == 1)
    }

    fn implementation_replacements(
        &self,
        implementation: ImplMethodId,
        _anchors: &HashMap<NodeId, &MethodEvidenceAnchor>,
        node: NodeId,
        head_only: bool,
    ) -> Result<TypeReplacementMap, ValidationError> {
        let expected = self
            .program
            .method_evidence
            .implementation_owner(implementation)
            .ok_or_else(|| ValidationError::new(ValidationReason::NodeType, Some(node)))?;
        if expected.source_parameters.is_empty() {
            return Ok(TypeReplacementMap::new());
        }
        let owner_anchor = self
            .program
            .method_evidence_anchors
            .iter()
            .find(|anchor| {
                matches!(
                    anchor.role,
                    MethodEvidenceAnchorRole::ImplementationOwner {
                        implementation: actual,
                        binder,
                    } if actual == implementation && binder == expected.binder
                )
            })
            .ok_or_else(|| ValidationError::new(ValidationReason::NodeType, Some(node)))?;
        let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
            self.pure_kind(owner_anchor.node)?
        else {
            return Err(ValidationError::new(ValidationReason::NodeType, Some(node)));
        };
        let mut replacements = TypeReplacementMap::new();
        let parameter_count = if head_only {
            expected.head_type_parameter_count
        } else {
            expected.source_parameters.len()
        };
        self.charge_type_work(parameter_count)?;
        replacements
            .try_reserve(parameter_count)
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(node)))?;
        for ((source, _), (actual, _)) in expected
            .source_parameters
            .iter()
            .take(parameter_count)
            .zip(abstraction.parameters())
        {
            replacements.insert_replacing(*source, Type::Variable(*actual));
        }
        Ok(replacements)
    }

    fn validate_method_evidence_domain(
        &self,
        anchor: &MethodEvidenceAnchor,
        anchors: &HashMap<NodeId, &MethodEvidenceAnchor>,
        carriers: &mut HashSet<NodeId>,
    ) -> Result<(), ValidationError> {
        let stored = self.node(anchor.node)?;
        let (
            Type::Function(domain, codomain),
            Some(PureExprKind::Value(PureValue::Function(function))),
        ) = (&stored.ty, F::pure(&stored.kind))
        else {
            return Err(ValidationError::new(
                ValidationReason::NodeType,
                Some(anchor.node),
            ));
        };
        let actual_interface = match anchor.owner {
            Some(MethodEvidenceOwner::Implementation(implementation))
                if self
                    .program
                    .method_evidence
                    .implementation_owner(implementation)
                    .is_some() =>
            {
                let replacements =
                    self.implementation_replacements(implementation, anchors, anchor.node, true)?;
                Some(
                    self.substitute_interface_application(
                        &anchor.application,
                        replacements.as_map(),
                    )?,
                )
            }
            Some(MethodEvidenceOwner::Implementation(_))
            | Some(MethodEvidenceOwner::Global(_))
            | None => None,
        };
        let scheme = self.expected_method_scheme_for(
            anchor.method,
            actual_interface.as_ref().unwrap_or(&anchor.application),
            anchor.node,
        )?;
        let body = self.node(function.body())?;
        if !self.same_type_charged(domain, &scheme)?
            || !self.same_type_charged(codomain, &body.ty)?
            || !carriers.contains(&anchor.node)
        {
            return Err(ValidationError::new(
                ValidationReason::NodeType,
                Some(anchor.node),
            ));
        }
        Ok(())
    }

    fn validate_adapter_anchor(
        &self,
        anchor: &MethodEvidenceAnchor,
        adapter: usize,
        anchors: &HashMap<NodeId, &MethodEvidenceAnchor>,
    ) -> Result<bool, ValidationError> {
        let expected = self
            .program
            .method_evidence
            .adapters()
            .get(adapter)
            .ok_or_else(|| ValidationError::new(ValidationReason::NodeType, Some(anchor.node)))?;
        let owner = self
            .program
            .method_evidence
            .implementation_owner(expected.implementation)
            .ok_or_else(|| ValidationError::new(ValidationReason::NodeType, Some(anchor.node)))?;
        if expected.binder != owner.binder
            || expected.source_parameters.len() != owner.source_parameters.len()
            || expected.head_arguments.len() != owner.head_type_parameter_count
        {
            return Ok(false);
        }
        for (source, (owner_source, owner_kind)) in expected
            .source_parameters
            .iter()
            .zip(&owner.source_parameters)
        {
            self.charge_type_work(1)?;
            if source != owner_source {
                return Ok(false);
            }
            self.charge_kind(owner_kind)?;
        }
        let mut selected_replacements = TypeReplacementMap::new();
        self.charge_type_work(owner.head_type_parameter_count)?;
        selected_replacements
            .try_reserve(owner.head_type_parameter_count)
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(anchor.node)))?;
        for ((parameter, _), argument) in owner
            .source_parameters
            .iter()
            .take(owner.head_type_parameter_count)
            .zip(&expected.head_arguments)
        {
            selected_replacements.insert_replacing(*parameter, self.clone_type_charged(argument)?);
        }
        let selected_application = self
            .substitute_interface_application(&owner.application, selected_replacements.as_map())?;
        if !self.same_interface_application(&selected_application, &anchor.application)? {
            return Ok(false);
        }
        let stored = self.node(anchor.node)?;
        let Some(PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction))) =
            F::pure(&stored.kind)
        else {
            return Ok(false);
        };
        let mut current = abstraction.body();
        let mut applied_prerequisites = 0usize;
        loop {
            let node = self.node(current)?;
            match F::pure(&node.kind) {
                Some(PureExprKind::Computation(PureComputation::Apply(application))) => {
                    self.charge_type_work(1)?;
                    applied_prerequisites =
                        applied_prerequisites.checked_add(1).ok_or_else(|| {
                            ValidationError::new(ValidationReason::Resource, Some(current))
                        })?;
                    current = application.function();
                }
                Some(PureExprKind::Computation(PureComputation::TypeApplication(application))) => {
                    if applied_prerequisites != expected.prerequisites.len()
                        || application.arguments().len()
                            != expected
                                .head_arguments
                                .len()
                                .saturating_add(abstraction.parameters().len())
                    {
                        return Ok(false);
                    }
                    let scope_replacements = match anchor.owner {
                        Some(MethodEvidenceOwner::Implementation(implementation))
                            if self
                                .program
                                .method_evidence
                                .implementation_owner(implementation)
                                .is_some() =>
                        {
                            self.implementation_replacements(
                                implementation,
                                anchors,
                                anchor.node,
                                true,
                            )?
                        }
                        Some(MethodEvidenceOwner::Implementation(_))
                        | Some(MethodEvidenceOwner::Global(_))
                        | None => TypeReplacementMap::new(),
                    };
                    for (actual, linked) in
                        application.arguments().iter().zip(&expected.head_arguments)
                    {
                        let expected_argument =
                            IterativeTypeOwner::new(substitute_type_variables_with(
                                linked,
                                scope_replacements.as_map(),
                                |cells| self.charge_type_work(cells),
                                || ValidationError::new(ValidationReason::Resource, None),
                            )?);
                        if !self.same_type_charged(actual, &expected_argument)? {
                            return Ok(false);
                        }
                    }
                    if !application
                        .arguments()
                        .iter()
                        .skip(expected.head_arguments.len())
                        .zip(abstraction.parameters())
                        .all(|(argument, (parameter, _))| {
                            matches!(argument, Type::Variable(actual) if actual == parameter)
                        })
                    {
                        return Ok(false);
                    }
                    let actual_interface = self.substitute_interface_application(
                        &anchor.application,
                        scope_replacements.as_map(),
                    )?;
                    let canonical = self.expected_method_scheme_for(
                        anchor.method,
                        &actual_interface,
                        anchor.node,
                    )?;
                    if !self.adapter_scheme_matches(&canonical, &stored.ty)? {
                        return Ok(false);
                    }
                    let function = self.node(application.function())?;
                    let matches = matches!(
                        F::pure(&function.kind),
                        Some(PureExprKind::Variable(variable)) if variable.binder() == expected.binder
                    );
                    return Ok(matches);
                }
                _ => return Ok(false),
            }
        }
    }

    fn adapter_scheme_matches(
        &self,
        canonical: &Type,
        actual: &Type,
    ) -> Result<bool, ValidationError> {
        let (Type::Forall(expected, expected_body), Type::Forall(actual, actual_body)) =
            (canonical, actual)
        else {
            return Ok(false);
        };
        if expected.len() != actual.len() {
            return Ok(false);
        }
        let mut replacements = TypeReplacementMap::new();
        let alpha_carrier_work = expected
            .len()
            .checked_mul(2)
            .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?;
        self.charge_type_work(alpha_carrier_work)?;
        replacements
            .try_reserve(expected.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        let mut fresh = HashSet::new();
        fresh
            .try_reserve(actual.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        for ((expected_id, expected_kind), (actual_id, actual_kind)) in expected.iter().zip(actual)
        {
            if !matches!(actual_id, crate::types::TypeVariableId::Generated(_))
                || !fresh.insert(*actual_id)
                || !self.same_kind_charged(expected_kind, actual_kind)?
                || self.type_contains_variable_charged(expected_body, *actual_id)?
            {
                return Ok(false);
            }
            replacements.insert_replacing(*expected_id, Type::Variable(*actual_id));
        }
        let renamed = IterativeTypeOwner::new(substitute_type_variables_with(
            expected_body,
            replacements.as_map(),
            |cells| self.charge_type_work(cells),
            || ValidationError::new(ValidationReason::Resource, None),
        )?);
        self.same_type_charged(&renamed, actual_body)
    }

    fn type_contains_variable_charged(
        &self,
        root: &Type,
        needle: crate::types::TypeVariableId,
    ) -> Result<bool, ValidationError> {
        let mut pending = Vec::new();
        self.charge_type_work(1)?;
        pending
            .try_reserve(1)
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        pending.push(root);
        while let Some(ty) = pending.pop() {
            self.charge_type_work(1)?;
            match ty {
                Type::Variable(variable) if *variable == needle => return Ok(true),
                Type::Application(function, argument) | Type::Function(function, argument) => {
                    self.charge_type_work(2)?;
                    pending
                        .try_reserve(2)
                        .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
                    pending.push(argument);
                    pending.push(function);
                }
                Type::Tuple(elements) => {
                    self.charge_type_work(elements.len())?;
                    pending
                        .try_reserve(elements.len())
                        .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
                    pending.extend(elements);
                }
                Type::Forall(_, body) => {
                    self.charge_type_work(1)?;
                    pending
                        .try_reserve(1)
                        .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
                    pending.push(body);
                }
                Type::EffectfulFunction(domain, computation) => {
                    if !F::ALLOWS_EFFECTFUL_TYPES {
                        return Ok(false);
                    }
                    let row = computation.effects();
                    if row.tail().is_some_and(|tail| {
                        matches!(
                            tail.variable(),
                            crate::types::EffectRowVariable::Rigid(variable) if variable == needle
                        )
                    }) {
                        return Ok(true);
                    }
                    self.schedule_effectful_type_children(&mut pending, domain, computation)?;
                }
                Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_) => {}
            }
        }
        Ok(false)
    }

    fn validate_method_instantiation(
        &self,
        anchor: &MethodEvidenceAnchor,
        binder: Option<BinderId>,
        anchors: &HashMap<NodeId, &MethodEvidenceAnchor>,
    ) -> Result<(), ValidationError> {
        let occurrence = anchor
            .occurrence
            .and_then(|slot| self.program.method_evidence.occurrence(slot))
            .ok_or_else(|| ValidationError::new(ValidationReason::NodeType, Some(anchor.node)))?;
        let stored = self.node(anchor.node)?;
        let Some(PureExprKind::Computation(PureComputation::TypeApplication(application))) =
            F::pure(&stored.kind)
        else {
            return Err(ValidationError::new(
                ValidationReason::TypeOperation,
                Some(anchor.node),
            ));
        };
        if occurrence.checked_method != Some(anchor.method)
            || occurrence.method_arguments.len() != application.arguments().len()
        {
            return Err(ValidationError::new(
                ValidationReason::TypeOperation,
                Some(anchor.node),
            ));
        }
        let scope_replacements = match anchor.owner {
            Some(MethodEvidenceOwner::Implementation(implementation))
                if self
                    .program
                    .method_evidence
                    .implementation_owner(implementation)
                    .is_some() =>
            {
                self.implementation_replacements(implementation, anchors, anchor.node, false)?
            }
            Some(MethodEvidenceOwner::Implementation(_))
            | Some(MethodEvidenceOwner::Global(_))
            | None => TypeReplacementMap::new(),
        };
        for (expected, actual) in occurrence
            .method_arguments
            .iter()
            .zip(application.arguments())
        {
            let expected = IterativeTypeOwner::new(substitute_type_variables_with(
                expected,
                scope_replacements.as_map(),
                |cells| self.charge_type_work(cells),
                || ValidationError::new(ValidationReason::Resource, None),
            )?);
            if !self.same_type_charged(&expected, actual)? {
                return Err(ValidationError::new(
                    ValidationReason::TypeOperation,
                    Some(anchor.node),
                ));
            }
        }
        if let Some(expected) = occurrence.checked_value_type.as_ref() {
            let expected = IterativeTypeOwner::new(substitute_type_variables_with(
                expected,
                scope_replacements.as_map(),
                |cells| self.charge_type_work(cells),
                || ValidationError::new(ValidationReason::Resource, None),
            )?);
            if !self.same_type_charged(&expected, &stored.ty)? {
                return Err(ValidationError::new(
                    ValidationReason::TypeOperation,
                    Some(anchor.node),
                ));
            }
        }
        let Some(MethodEvidenceExpectedRole::Instantiation { producer }) = self
            .program
            .method_evidence
            .expectations()
            .get(anchor.expectation)
            .map(|expected| expected.role)
        else {
            return Err(ValidationError::new(
                ValidationReason::TypeOperation,
                Some(anchor.node),
            ));
        };
        let source = anchors
            .values()
            .find(|source| source.expectation == producer)
            .copied()
            .ok_or_else(|| {
                ValidationError::new(ValidationReason::TypeOperation, Some(anchor.node))
            })?;
        let function = self.node(application.function())?;
        let producer_matches = match binder {
            Some(binder) => {
                matches!(source.role, MethodEvidenceAnchorRole::Domain { binder: expected } if expected == binder)
                    && matches!(F::pure(&function.kind), Some(PureExprKind::Variable(variable)) if variable.binder() == binder)
            }
            None => {
                source.node == application.function()
                    && matches!(source.role, MethodEvidenceAnchorRole::Adapter { .. })
            }
        };
        if producer_matches {
            Ok(())
        } else {
            Err(ValidationError::new(
                ValidationReason::TypeOperation,
                Some(anchor.node),
            ))
        }
    }

    fn validate_method_application(
        &self,
        anchor: &MethodEvidenceAnchor,
        anchors: &HashMap<NodeId, &MethodEvidenceAnchor>,
    ) -> Result<(), ValidationError> {
        let stored = self.node(anchor.node)?;
        let Some(PureExprKind::Computation(PureComputation::Apply(application))) =
            F::pure(&stored.kind)
        else {
            return Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(anchor.node),
            ));
        };
        let function = self.node(application.function())?;
        let Type::Function(domain, codomain) = &function.ty else {
            return Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(anchor.node),
            ));
        };
        let canonical = self.expected_method_scheme(anchor)?;
        let argument = self.node(application.argument())?;
        let Some(MethodEvidenceExpectedRole::Application { producer, .. }) = self
            .program
            .method_evidence
            .expectations()
            .get(anchor.expectation)
            .map(|expected| expected.role)
        else {
            return Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(anchor.node),
            ));
        };
        let source = anchors
            .values()
            .find(|source| source.expectation == producer)
            .copied()
            .ok_or_else(|| {
                ValidationError::new(ValidationReason::ApplicationType, Some(anchor.node))
            })?;
        let MethodEvidenceAnchorRole::Application {
            producer: actual_producer,
        } = anchor.role
        else {
            return Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(anchor.node),
            ));
        };
        let producer_matches = match source.role {
            MethodEvidenceAnchorRole::Adapter { implementation, .. } => {
                source.node == application.argument()
                    && actual_producer == MethodEvidenceProducer::Adapter { implementation }
            }
            MethodEvidenceAnchorRole::Domain { binder } => {
                let Some(PureExprKind::Variable(variable)) = F::pure(&argument.kind) else {
                    return Err(ValidationError::new(
                        ValidationReason::ApplicationType,
                        Some(anchor.node),
                    ));
                };
                variable.binder() == binder
                    && actual_producer
                        == MethodEvidenceProducer::Abstract {
                            requirement: source.requirement.ok_or_else(|| {
                                ValidationError::new(
                                    ValidationReason::ApplicationType,
                                    Some(anchor.node),
                                )
                            })?,
                        }
                    && self.same_type_charged(&argument.ty, &canonical)?
            }
            _ => false,
        };
        if self.same_type_charged(domain, &canonical)?
            && self.same_type_charged(codomain, &stored.ty)?
            && producer_matches
        {
            Ok(())
        } else {
            Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(anchor.node),
            ))
        }
    }

    fn validate_concrete_adapter_source(
        &self,
        anchor: &MethodEvidenceAnchor,
        anchors: &HashMap<NodeId, &MethodEvidenceAnchor>,
        occurrence_slot: usize,
        selection_node: crate::interface::EvidenceNodeId,
        implementation: crate::interface::ImplMethodId,
        source_node: NodeId,
    ) -> Result<bool, ValidationError> {
        self.charge_type_work(self.program.method_evidence.occurrence_count())?;
        let occurrence = self
            .program
            .method_evidence
            .occurrence(occurrence_slot)
            .ok_or_else(|| {
                ValidationError::new(ValidationReason::ApplicationType, Some(anchor.node))
            })?;
        let sources = self.program.method_evidence.concrete_sources();
        self.charge_type_work(sources.len())?;
        let root = sources
            .iter()
            .position(|source| {
                source.occurrence == occurrence_slot
                    && source.selection_node == selection_node
                    && source.implementation == implementation
            })
            .ok_or_else(|| {
                ValidationError::new(ValidationReason::ApplicationType, Some(anchor.node))
            })?;
        let mut pending = Vec::new();
        self.charge_type_work(1)?;
        pending
            .try_reserve(1)
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(anchor.node)))?;
        pending.push((root, source_node));
        while let Some((source_index, actual_node)) = pending.pop() {
            let source = sources.get(source_index).ok_or_else(|| {
                ValidationError::new(ValidationReason::ApplicationType, Some(anchor.node))
            })?;
            let EvidenceNode::Implementation {
                substitution,
                prerequisites,
                methods,
                ..
            } = occurrence
                .selection
                .node(source.selection_node)
                .ok_or_else(|| {
                    ValidationError::new(ValidationReason::ApplicationType, Some(anchor.node))
                })?
            else {
                return Ok(false);
            };
            self.charge_type_work(methods.len().checked_add(substitution.len()).ok_or_else(
                || ValidationError::new(ValidationReason::Resource, Some(anchor.node)),
            )?)?;
            if source.occurrence != occurrence_slot
                || !methods.contains(&source.implementation)
                || source.head_arguments.len() != substitution.len()
            {
                return Ok(false);
            }
            for (expected, actual) in source.head_arguments.iter().zip(substitution) {
                if !self.same_type_charged(expected, actual.argument())? {
                    return Ok(false);
                }
            }
            let expected_prerequisite_nodes = prerequisites.len();
            self.charge_type_work(expected_prerequisite_nodes)?;
            self.charge_type_work(source.prerequisites.len())?;
            let mut retained_prerequisites = source.prerequisites.iter();
            for expected_selection_node in prerequisites {
                match occurrence
                    .selection
                    .node(*expected_selection_node)
                    .ok_or_else(|| {
                        ValidationError::new(ValidationReason::ApplicationType, Some(anchor.node))
                    })? {
                    EvidenceNode::Abstract { methods, .. } => {
                        self.charge_type_work(methods.len())?;
                        for expected_method in methods {
                            let Some(retained) = retained_prerequisites.next() else {
                                return Ok(false);
                            };
                            if retained.selection_node != *expected_selection_node
                                || retained.method != *expected_method
                            {
                                return Ok(false);
                            }
                        }
                    }
                    EvidenceNode::Implementation { methods, .. } => {
                        self.charge_type_work(methods.len())?;
                        for expected_method in methods {
                            let Some(retained) = retained_prerequisites.next() else {
                                return Ok(false);
                            };
                            if retained.selection_node != *expected_selection_node
                                || retained.method != expected_method.method()
                            {
                                return Ok(false);
                            }
                        }
                    }
                }
            }
            if retained_prerequisites.next().is_some() {
                return Ok(false);
            }
            let mut current = actual_node;
            for prerequisite in source.prerequisites.iter().rev() {
                self.charge_type_work(1)?;
                let PureExprKind::Computation(PureComputation::Apply(application)) =
                    self.pure_kind(current)?
                else {
                    return Ok(false);
                };
                let argument = application.argument();
                match occurrence
                    .selection
                    .node(prerequisite.selection_node)
                    .ok_or_else(|| {
                        ValidationError::new(ValidationReason::ApplicationType, Some(anchor.node))
                    })? {
                    EvidenceNode::Abstract {
                        requirement,
                        methods,
                    } => {
                        self.charge_type_work(methods.len())?;
                        if !methods.contains(&prerequisite.method) {
                            return Ok(false);
                        }
                        let Some(position) = prerequisite.scope_position else {
                            return Ok(false);
                        };
                        let binder = self.method_evidence_scope_binder(anchor, position)?;
                        if !matches!(
                            F::pure(&self.node(argument)?.kind),
                            Some(PureExprKind::Variable(variable)) if variable.binder() == binder
                        ) || !matches!(
                            occurrence.selection.node(prerequisite.selection_node),
                            Some(EvidenceNode::Abstract { requirement: actual, .. }) if actual == requirement
                        ) {
                            return Ok(false);
                        }
                    }
                    EvidenceNode::Implementation { methods, .. } => {
                        self.charge_type_work(methods.len())?;
                        let Some(selected) = methods
                            .iter()
                            .find(|selected| selected.method() == prerequisite.method)
                            .copied()
                        else {
                            return Ok(false);
                        };
                        self.charge_type_work(self.program.method_evidence.method_count())?;
                        if self
                            .program
                            .method_evidence
                            .method(prerequisite.method)
                            .is_some()
                        {
                            self.charge_type_work(anchors.len())?;
                            if !anchors.values().any(|candidate| {
                                candidate.occurrence == Some(occurrence_slot)
                                    && candidate.node == argument
                                    && matches!(candidate.role, MethodEvidenceAnchorRole::Adapter { implementation, selection_node } if implementation == selected && selection_node == prerequisite.selection_node)
                            }) {
                                return Ok(false);
                            }
                        } else {
                            self.charge_type_work(sources.len().checked_add(1).ok_or_else(
                                || {
                                    ValidationError::new(
                                        ValidationReason::Resource,
                                        Some(anchor.node),
                                    )
                                },
                            )?)?;
                            let Some(child) = sources.iter().position(|candidate| {
                                candidate.occurrence == occurrence_slot
                                    && candidate.selection_node == prerequisite.selection_node
                                    && candidate.implementation == selected
                            }) else {
                                return Ok(false);
                            };
                            pending.try_reserve(1).map_err(|_| {
                                ValidationError::new(ValidationReason::Resource, Some(anchor.node))
                            })?;
                            pending.push((child, argument));
                        }
                    }
                }
                current = application.function();
            }
            if source.head_arguments.is_empty() {
                if !matches!(
                    F::pure(&self.node(current)?.kind),
                    Some(PureExprKind::Variable(variable)) if variable.binder() == source.binder
                ) {
                    return Ok(false);
                }
            } else {
                let PureExprKind::Computation(PureComputation::TypeApplication(application)) =
                    self.pure_kind(current)?
                else {
                    return Ok(false);
                };
                if application.arguments().len() != source.head_arguments.len() {
                    return Ok(false);
                }
                for (actual, expected) in application.arguments().iter().zip(&source.head_arguments)
                {
                    if !self.same_type_charged(actual, expected)? {
                        return Ok(false);
                    }
                }
                if !matches!(
                    F::pure(&self.node(application.function())?.kind),
                    Some(PureExprKind::Variable(variable)) if variable.binder() == source.binder
                ) {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }

    fn validate_adapter_edge(
        &self,
        anchor: &MethodEvidenceAnchor,
        anchors: &HashMap<NodeId, &MethodEvidenceAnchor>,
    ) -> Result<(), ValidationError> {
        let MethodEvidenceAnchorRole::AdapterEdge {
            adapter,
            adapter_selection_node,
            ordinal,
            producer_node,
            producer_selection_node,
            producer_binder,
            producer,
        } = anchor.role
        else {
            return Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(anchor.node),
            ));
        };
        // Rechecking the exact adapter selection, argument node, producer
        // selection, and generated-binder identity is separate from retaining
        // those four anchor fields during Core construction.
        self.charge_type_work(4)?;
        let Some(MethodEvidenceExpectedRole::AdapterEdge {
            adapter: adapter_index,
            ordinal: expected_ordinal,
        }) = self
            .program
            .method_evidence
            .expectations()
            .get(anchor.expectation)
            .map(|expected| expected.role)
        else {
            return Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(anchor.node),
            ));
        };
        let row = self
            .program
            .method_evidence
            .adapters()
            .get(adapter_index)
            .ok_or_else(|| {
                ValidationError::new(ValidationReason::ApplicationType, Some(anchor.node))
            })?;
        let edge = row.prerequisites.get(expected_ordinal).ok_or_else(|| {
            ValidationError::new(ValidationReason::ApplicationType, Some(anchor.node))
        })?;
        let stored = self.node(anchor.node)?;
        let Some(PureExprKind::Computation(PureComputation::Apply(application))) =
            F::pure(&stored.kind)
        else {
            return Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(anchor.node),
            ));
        };
        let function = self.node(application.function())?;
        let Type::Function(domain, codomain) = &function.ty else {
            return Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(anchor.node),
            ));
        };
        self.charge_type_work(anchors.len())?;
        let adapter_anchor = anchors
            .values()
            .find(|candidate| {
                candidate.occurrence == anchor.occurrence
                    && matches!(candidate.role, MethodEvidenceAnchorRole::Adapter { implementation, selection_node } if implementation == row.implementation && selection_node == row.selection_node)
            })
            .copied();
        let adapter_anchor = adapter_anchor.ok_or_else(|| {
            ValidationError::new(ValidationReason::ApplicationType, Some(anchor.node))
        })?;
        let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
            self.pure_kind(adapter_anchor.node)?
        else {
            return Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(anchor.node),
            ));
        };
        let mut adapter_source = abstraction.body();
        while let PureExprKind::Computation(PureComputation::Apply(application)) =
            self.pure_kind(adapter_source)?
        {
            self.charge_type_work(1)?;
            adapter_source = application.function();
        }
        let PureExprKind::Computation(PureComputation::TypeApplication(adapter_application)) =
            self.pure_kind(adapter_source)?
        else {
            return Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(anchor.node),
            ));
        };
        if row.source_parameters.len() != adapter_application.arguments().len()
            || Some(row.source_parameters.len())
                != row
                    .head_arguments
                    .len()
                    .checked_add(abstraction.parameters().len())
        {
            return Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(anchor.node),
            ));
        }
        let mut core_source_replacements = TypeReplacementMap::new();
        self.charge_type_work(row.source_parameters.len())?;
        core_source_replacements
            .try_reserve(row.source_parameters.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(anchor.node)))?;
        for (parameter, argument) in row
            .source_parameters
            .iter()
            .zip(adapter_application.arguments())
        {
            self.charge_type_structure(argument)?;
            core_source_replacements.insert_replacing(*parameter, argument.clone());
        }
        let mut anchor_source_replacements = TypeReplacementMap::new();
        self.charge_type_work(row.source_parameters.len())?;
        anchor_source_replacements
            .try_reserve(row.source_parameters.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(anchor.node)))?;
        for (parameter, argument) in row.source_parameters.iter().zip(&row.head_arguments) {
            self.charge_type_structure(argument)?;
            anchor_source_replacements.insert_replacing(*parameter, argument.clone());
        }
        for (parameter, (fresh, _)) in row
            .source_parameters
            .iter()
            .skip(row.head_arguments.len())
            .zip(abstraction.parameters())
        {
            self.charge_type_work(1)?;
            anchor_source_replacements.insert_replacing(*parameter, Type::Variable(*fresh));
        }
        let expected_anchor_application = self.substitute_interface_application(
            &edge.application,
            anchor_source_replacements.as_map(),
        )?;
        if !self.same_interface_application(&anchor.application, &expected_anchor_application)? {
            return Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(anchor.node),
            ));
        }
        let expected_application = self.substitute_interface_application(
            &edge.application,
            core_source_replacements.as_map(),
        )?;
        let mut interface_replacement = TypeReplacementMap::new();
        if edge.interface_parameters.len() != expected_application.arguments().len() {
            return Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(anchor.node),
            ));
        }
        self.charge_type_work(edge.interface_parameters.len())?;
        interface_replacement
            .try_reserve(edge.interface_parameters.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(anchor.node)))?;
        for (parameter, argument) in edge
            .interface_parameters
            .iter()
            .zip(expected_application.arguments())
        {
            interface_replacement.insert_replacing(*parameter, self.clone_type_charged(argument)?);
        }
        let expected_body = substitute_type_variables_with(
            &edge.value_type,
            interface_replacement.as_map(),
            |cells| self.charge_type_work(cells),
            || ValidationError::new(ValidationReason::Resource, None),
        )?;
        let expected_domain = if edge.method_parameters.is_empty() {
            IterativeTypeOwner::new(expected_body)
        } else {
            let mut parameters = Vec::new();
            self.charge_type_work(edge.method_parameters.len())?;
            parameters
                .try_reserve_exact(edge.method_parameters.len())
                .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(anchor.node)))?;
            for (parameter, kind) in &edge.method_parameters {
                parameters.push((*parameter, self.clone_kind_charged(kind)?));
            }
            IterativeTypeOwner::new(Type::Forall(
                parameters.into_boxed_slice(),
                Box::new(expected_body),
            ))
        };
        let argument = self.node(application.argument())?;
        let (source_matches, argument_type_matches) = match edge.producer {
            super::dialect::MethodEvidenceExpectedProducer::Authenticated(expectation) => {
                if let Some(source) = anchors
                    .values()
                    .find(|source| source.expectation == expectation)
                {
                    match source.role {
                        MethodEvidenceAnchorRole::Domain { binder } => (
                            matches!(
                                F::pure(&argument.kind),
                                Some(PureExprKind::Variable(variable)) if variable.binder() == binder
                            ) && source.requirement.is_some_and(|requirement| {
                                producer == MethodEvidenceProducer::Abstract { requirement }
                            }),
                            self.same_type_charged(&argument.ty, &expected_domain)?,
                        ),
                        MethodEvidenceAnchorRole::Adapter { implementation, .. } => (
                            source.node == application.argument()
                                && producer == MethodEvidenceProducer::Adapter { implementation },
                            self.adapter_scheme_matches(&expected_domain, &argument.ty)?,
                        ),
                        _ => (false, false),
                    }
                } else {
                    (false, false)
                }
            }
            super::dialect::MethodEvidenceExpectedProducer::Monomorphic {
                selection_node,
                producer_scope_position,
                producer: expected,
            } => {
                let exact_scope_binder = match (expected, producer_scope_position) {
                    (MethodEvidenceProducer::Abstract { .. }, Some(producer_scope_position)) => {
                        Some(self.method_evidence_scope_binder(anchor, producer_scope_position)?)
                    }
                    (MethodEvidenceProducer::Adapter { .. }, None) => None,
                    _ => {
                        return Err(ValidationError::new(
                            ValidationReason::ApplicationType,
                            Some(anchor.node),
                        ));
                    }
                };
                let concrete_source_matches = match expected {
                    MethodEvidenceProducer::Adapter { implementation } => self
                        .validate_concrete_adapter_source(
                            anchor,
                            anchors,
                            anchor.occurrence.ok_or_else(|| {
                                ValidationError::new(
                                    ValidationReason::ApplicationType,
                                    Some(anchor.node),
                                )
                            })?,
                            selection_node,
                            implementation,
                            application.argument(),
                        )?,
                    MethodEvidenceProducer::Abstract { .. } => true,
                };
                (
                    concrete_source_matches
                        && selection_node == producer_selection_node
                        && expected == producer
                        && producer_node == application.argument()
                        && producer_binder == exact_scope_binder,
                    self.same_type_charged(&argument.ty, &expected_domain)?,
                )
            }
        };
        if adapter != row.implementation
            || adapter_selection_node != row.selection_node
            || match (producer, producer_binder) {
                (MethodEvidenceProducer::Abstract { .. }, Some(binder)) => !matches!(
                    F::pure(&argument.kind),
                    Some(PureExprKind::Variable(variable)) if variable.binder() == binder
                ),
                (MethodEvidenceProducer::Adapter { .. }, None) => false,
                _ => true,
            }
            || ordinal != expected_ordinal
            || !source_matches
            || !argument_type_matches
            || !self.same_type_charged(domain, &expected_domain)?
            || !self.same_type_charged(codomain, &stored.ty)?
        {
            return Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(anchor.node),
            ));
        }
        Ok(())
    }

    fn method_evidence_scope_binder(
        &self,
        anchor: &MethodEvidenceAnchor,
        position: usize,
    ) -> Result<BinderId, ValidationError> {
        let occurrence = anchor
            .occurrence
            .and_then(|slot| self.program.method_evidence.occurrence(slot))
            .ok_or_else(|| {
                ValidationError::new(ValidationReason::ApplicationType, Some(anchor.node))
            })?;
        let scope_binder = occurrence.scope_binder.ok_or_else(|| {
            ValidationError::new(ValidationReason::ApplicationType, Some(anchor.node))
        })?;
        if !matches!(
            occurrence.scope,
            Some(MethodEvidenceOwner::Global(owner)) if owner == scope_binder
        ) && !matches!(
            occurrence.scope,
            Some(MethodEvidenceOwner::Implementation(_))
        ) {
            return Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(anchor.node),
            ));
        }
        self.charge_type_work(self.program.nodes.len())?;
        let mut initializer = None;
        for node in &self.program.nodes {
            let Some(PureExprKind::Computation(PureComputation::RecursiveBind(group))) =
                F::pure(&node.kind)
            else {
                continue;
            };
            self.charge_type_work(group.members().len())?;
            for member in group.members() {
                if member.binder().id() == scope_binder
                    && initializer.replace(member.initializer()).is_some()
                {
                    return Err(ValidationError::new(
                        ValidationReason::ApplicationType,
                        Some(anchor.node),
                    ));
                }
            }
        }
        let mut current = initializer.ok_or_else(|| {
            ValidationError::new(ValidationReason::ApplicationType, Some(anchor.node))
        })?;
        if let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
            self.pure_kind(current)?
        {
            current = abstraction.body();
        }
        for _ in 0..position {
            self.charge_type_work(1)?;
            let PureExprKind::Value(PureValue::Function(function)) = self.pure_kind(current)?
            else {
                return Err(ValidationError::new(
                    ValidationReason::ApplicationType,
                    Some(anchor.node),
                ));
            };
            current = function.body();
        }
        self.charge_type_work(1)?;
        let PureExprKind::Value(PureValue::Function(function)) = self.pure_kind(current)? else {
            return Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(anchor.node),
            ));
        };
        Ok(function.parameter().id())
    }

    fn validate_adapter_prerequisite_sequence(
        &self,
        adapter: &MethodEvidenceAnchor,
        anchors: &HashMap<NodeId, &MethodEvidenceAnchor>,
    ) -> Result<(), ValidationError> {
        let MethodEvidenceAnchorRole::Adapter { .. } = adapter.role else {
            return Ok(());
        };
        let Some(MethodEvidenceExpectedRole::Adapter {
            adapter: expected_adapter,
        }) = self
            .program
            .method_evidence
            .expectations()
            .get(adapter.expectation)
            .map(|expected| expected.role)
        else {
            return Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(adapter.node),
            ));
        };
        let expected = self
            .program
            .method_evidence
            .adapters()
            .get(expected_adapter)
            .ok_or_else(|| {
                ValidationError::new(ValidationReason::ApplicationType, Some(adapter.node))
            })?;
        let stored = self.node(adapter.node)?;
        let Some(PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction))) =
            F::pure(&stored.kind)
        else {
            return Err(ValidationError::new(
                ValidationReason::TypeOperation,
                Some(adapter.node),
            ));
        };
        let mut actual = Vec::new();
        self.charge_type_work(expected.prerequisites.len())?;
        actual
            .try_reserve_exact(expected.prerequisites.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(adapter.node)))?;
        let mut current = abstraction.body();
        while let PureExprKind::Computation(PureComputation::Apply(application)) =
            self.pure_kind(current)?
        {
            self.charge_type_work(1)?;
            if actual.len() == expected.prerequisites.len() {
                return Err(ValidationError::new(
                    ValidationReason::ApplicationType,
                    Some(current),
                ));
            }
            actual.push(current);
            current = application.function();
        }
        let exact_sequence_work = actual
            .len()
            .checked_mul(2)
            .ok_or_else(|| ValidationError::new(ValidationReason::Resource, Some(adapter.node)))?;
        self.charge_type_work(exact_sequence_work)?;
        if actual.len() == expected.prerequisites.len()
            && actual.iter().rev().enumerate().all(|(ordinal, node)| {
                anchors.get(node).is_some_and(|anchor| {
                    matches!(
                        anchor.role,
                        MethodEvidenceAnchorRole::AdapterEdge {
                            adapter: implementation,
                            adapter_selection_node,
                            ordinal: actual,
                            ..
                        } if implementation == expected.implementation
                            && adapter_selection_node == expected.selection_node
                            && actual == ordinal
                    )
                })
            })
        {
            Ok(())
        } else {
            Err(ValidationError::new(
                ValidationReason::ApplicationType,
                Some(adapter.node),
            ))
        }
    }

    fn validate_registry(&self) -> Result<RegistryParameterOwners, ValidationError> {
        if self.module_sources.is_some() {
            return self.validate_module_registry();
        }
        let registry = &self.program.registry;
        let mut nominal_ids = HashSet::new();
        let mut nominal_names = HashSet::new();
        let mut constructor_ids = HashSet::new();
        let mut constructor_names = HashSet::new();
        let root_source = self
            .node(self.program.root)
            .ok()
            .and_then(|root| root.origin.as_ref())
            .map(|origin| origin.primary_span().source());
        let registry_source = registry
            .nominals()
            .first()
            .map(|nominal| nominal.origin.primary_span().source())
            .or_else(|| {
                registry
                    .type_variable(crate::types::TypeVariableId::new(0))
                    .map(|parameter| parameter.origin.primary_span().source())
            })
            .or(root_source);
        let registry_module = registry
            .nominals()
            .first()
            .map(|nominal| nominal.id.module())
            .or_else(|| root_source.map(crate::module::ModuleId::from));
        if registry_source
            .zip(root_source)
            .is_some_and(|(registry_source, root_source)| registry_source != root_source)
        {
            return Err(ValidationError::new(ValidationReason::Registry, None));
        }
        let mut previous_nominal_end = None;
        for (index, nominal) in registry.nominals().iter().enumerate() {
            let index = u32::try_from(index)
                .map_err(|_| ValidationError::new(ValidationReason::Registry, None))?;
            let Some(module) = registry_module else {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            };
            let Some(source) = registry_source else {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            };
            let nominal_range = nominal.origin.primary_span().range();
            if nominal.id != crate::types::NominalTypeId::new(module, index)
                || nominal.origin.primary_span().source() != source
                || !origin_depth_within_limit(&nominal.origin)
                || nominal.constructors.is_empty()
                || !valid_upper_spelling(&nominal.spelling)
                || !nominal_ids.insert(nominal.id)
                || !nominal_names.insert(nominal.spelling.as_str())
                || nominal_range.start() >= nominal_range.end()
                || previous_nominal_end.is_some_and(|previous| nominal_range.start() < previous)
            {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            }
            previous_nominal_end = Some(nominal_range.end());
            self.validate_origin(&nominal.origin, self.program.root)?;
        }
        let owner_parameter_count =
            registry
                .nominal_parameter_entries()
                .try_fold(0_usize, |count, (owner, parameters)| {
                    registry
                        .nominal(owner)
                        .and_then(|_| count.checked_add(parameters.len()))
                });
        if owner_parameter_count.is_none_or(|count| count > registry.type_variable_count()) {
            return Err(ValidationError::new(ValidationReason::Registry, None));
        }
        let type_variable_count = u32::try_from(registry.type_variable_count())
            .map_err(|_| ValidationError::new(ValidationReason::Registry, None))?;
        let mut previous_type_variable_start = None;
        let resolved_type_variables = registry_module.is_some_and(|module| {
            registry
                .type_variable(crate::types::TypeVariableId::resolved(module, 0))
                .is_some()
        });
        for value in 0..type_variable_count {
            let identity = if resolved_type_variables {
                crate::types::TypeVariableId::resolved(
                    registry_module.expect("resolved variables require one module"),
                    value,
                )
            } else {
                crate::types::TypeVariableId::generated(value)
            };
            let parameter = registry
                .type_variable(identity)
                .ok_or_else(|| ValidationError::new(ValidationReason::Registry, None))?;
            self.charge_type_work(1)?;
            let parameter_span = parameter.origin.primary_span();
            let parameter_range = parameter_span.range();
            if identity != parameter.id
                || Some(parameter_span.source()) != registry_source
                || !origin_depth_within_limit(&parameter.origin)
                || !valid_upper_spelling(&parameter.spelling)
                || parameter_range.start() >= parameter_range.end()
                || previous_type_variable_start
                    .is_some_and(|previous| parameter_range.start() <= previous)
            {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            }
            previous_type_variable_start = Some(parameter_range.start());
            self.validate_origin(&parameter.origin, self.program.root)?;
        }
        let mut parameter_owners = HashMap::new();
        for nominal in registry.nominals() {
            let nominal_range = nominal.origin.primary_span().range();
            let parameters = registry
                .nominal_parameters(nominal.id)
                .ok_or_else(|| ValidationError::new(ValidationReason::Registry, None))?;
            let mut parameter_names = HashSet::new();
            let mut previous_parameter_start = None;
            for parameter in parameters {
                #[cfg(test)]
                self.owner_parameter_index_work
                    .set(self.owner_parameter_index_work.get() + 1);
                let parameter_span = parameter.origin.primary_span();
                let parameter_range = parameter_span.range();
                if parameter_owners
                    .insert(parameter.id, RegistryParameterOwner::Nominal(nominal.id))
                    .is_some()
                    || !parameter_names.insert(parameter.spelling.as_str())
                {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
                let canonical = registry
                    .type_variable(parameter.id)
                    .ok_or_else(|| ValidationError::new(ValidationReason::Registry, None))?;
                if !self.same_registry_type_variable(canonical, parameter)?
                    || parameter_range.start() < nominal_range.start()
                    || parameter_range.end() > nominal_range.end()
                    || previous_parameter_start
                        .is_some_and(|previous| parameter_range.start() <= previous)
                {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
                previous_parameter_start = Some(parameter_range.start());
            }
            self.validate_nominal_representation(
                nominal,
                registry_source.expect("validated registry source exists"),
                &parameter_owners,
            )?;
        }
        let mut previous_constructor_start = None;
        for constructor in registry.constructors() {
            let constructor_span = constructor.origin.primary_span();
            let constructor_range = constructor_span.range();
            let owner_range = registry
                .nominal(constructor.owner)
                .map(|owner| owner.origin.primary_span().range());
            let payload_valid = self.valid_registry_payload(
                constructor.payload.as_ref(),
                constructor.owner,
                &parameter_owners,
            )?;
            let payload_kind_valid = payload_valid
                && self.valid_registry_payload_kind(
                    constructor.payload.as_ref(),
                    constructor.owner,
                    &parameter_owners,
                )?;
            if constructor.id.owner() != constructor.owner
                || !nominal_ids.contains(&constructor.owner)
                || Some(constructor.origin.primary_span().source()) != registry_source
                || !origin_depth_within_limit(&constructor.origin)
                || !valid_upper_spelling(&constructor.spelling)
                || !constructor_ids.insert(constructor.id)
                || !constructor_names.insert(constructor.spelling.as_str())
                || !payload_kind_valid
                || owner_range.is_none_or(|owner| {
                    constructor_range.start() < owner.start()
                        || constructor_range.end() > owner.end()
                })
                || constructor_range.start() >= constructor_range.end()
                || previous_constructor_start
                    .is_some_and(|previous| constructor_range.start() <= previous)
            {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            }
            previous_constructor_start = Some(constructor_range.start());
            self.validate_origin(&constructor.origin, self.program.root)?;
        }
        let expected_constructor_order = registry
            .nominals()
            .iter()
            .flat_map(|nominal| nominal.constructors.iter().copied());
        if !registry
            .constructors()
            .iter()
            .map(|constructor| constructor.id)
            .eq(expected_constructor_order)
        {
            return Err(ValidationError::new(ValidationReason::Registry, None));
        }
        for nominal in registry.nominals() {
            for (index, constructor) in nominal.constructors.iter().copied().enumerate() {
                if registry.constructor(constructor).is_none() {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
                if constructor
                    != ConstructorId::new(
                        nominal.id,
                        u32::try_from(index)
                            .map_err(|_| ValidationError::new(ValidationReason::Registry, None))?,
                    )
                {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
            }
        }
        if registry.constructors().iter().any(|constructor| {
            registry
                .nominal(constructor.owner)
                .is_none_or(|owner| !constructor_belongs_to_owner(owner, constructor.id))
        }) {
            return Err(ValidationError::new(ValidationReason::Registry, None));
        }
        Ok(parameter_owners)
    }

    fn validate_global_parameter_rows(
        &self,
        nominal_parameter_owners: &RegistryParameterOwners,
    ) -> Result<(), ValidationError> {
        let registry = &self.program.registry;
        let rows = registry.global_parameter_rows();
        if rows.len() != registry.global_parameter_position_count() {
            return Err(ValidationError::new(ValidationReason::Registry, None));
        }
        let parameter_count = rows.iter().try_fold(0_usize, |count, row| {
            count.checked_add(row.parameters().len())
        });
        let Some(parameter_count) = parameter_count else {
            return Err(ValidationError::new(ValidationReason::Resource, None));
        };
        let retained_work = rows
            .len()
            .checked_mul(2)
            .and_then(|work| {
                parameter_count
                    .checked_mul(2)
                    .and_then(|cells| work.checked_add(cells))
            })
            .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?;
        self.charge_type_work(retained_work)?;

        let mut owners = HashSet::new();
        let mut parameters = HashSet::new();
        owners
            .try_reserve(rows.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        parameters
            .try_reserve(parameter_count)
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        let relation = self
            .module_sources
            .as_ref()
            .expect("global row validation requires a module relation");

        for row in rows {
            let owner = row.owner();
            let Some(owner_module) = owner.module() else {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            };
            let indexed = registry.global_parameter_row(owner);
            if row.parameters().is_empty()
                || !relation.contains_key(&owner_module)
                || !owners.insert(owner)
                || indexed.is_none_or(|indexed| !std::ptr::eq(indexed, row))
            {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            }
            for parameter in row.parameters() {
                let Some(parameter_module) = parameter.module() else {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                };
                let canonical = registry.type_variable(*parameter);
                if parameter_module != owner_module
                    || canonical.is_none_or(|canonical| canonical.id != *parameter)
                    || nominal_parameter_owners.contains_key(parameter)
                    || !parameters.insert(*parameter)
                {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
            }
        }
        Ok(())
    }

    fn validate_module_registry(&self) -> Result<RegistryParameterOwners, ValidationError> {
        let registry = &self.program.registry;
        let relation = self
            .module_sources
            .as_ref()
            .expect("module registry validation requires an explicit relation");
        let mut nominal_ids = HashSet::new();
        let mut nominal_names = HashMap::<ModuleId, HashSet<&str>>::new();
        let mut next_nominal = HashMap::<ModuleId, u32>::new();
        let mut previous_nominal_end = HashMap::new();

        for nominal in registry.nominals() {
            let module = nominal.id.module();
            let Some(source) = relation.get(&module).copied() else {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            };
            let expected = next_nominal.entry(module).or_insert(0);
            let nominal_span = nominal.origin.primary_span();
            let nominal_range = nominal_span.range();
            let names = nominal_names.entry(module).or_default();
            if nominal.id.declaration() != *expected
                || nominal_span.source() != source
                || !origin_depth_within_limit(&nominal.origin)
                || nominal.constructors.is_empty()
                || !valid_upper_spelling(&nominal.spelling)
                || !nominal_ids.insert(nominal.id)
                || !names.insert(nominal.spelling.as_str())
                || nominal_range.start() >= nominal_range.end()
                || previous_nominal_end
                    .get(&module)
                    .is_some_and(|previous| nominal_range.start() < *previous)
            {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            }
            *expected = expected
                .checked_add(1)
                .ok_or_else(|| ValidationError::new(ValidationReason::Registry, None))?;
            previous_nominal_end.insert(module, nominal_range.end());
            self.validate_origin(&nominal.origin, self.program.root)?;
        }

        let owner_parameter_count =
            registry
                .nominal_parameter_entries()
                .try_fold(0_usize, |count, (owner, parameters)| {
                    registry
                        .nominal(owner)
                        .and_then(|_| count.checked_add(parameters.len()))
                });
        if owner_parameter_count.is_none_or(|count| count > registry.type_variable_count()) {
            return Err(ValidationError::new(ValidationReason::Registry, None));
        }

        let mut type_variables = registry.type_variables().collect::<Vec<_>>();
        type_variables.sort_unstable_by_key(|parameter| {
            (
                parameter.id.module(),
                parameter.id.local(),
                parameter.origin.primary_span().range().start(),
            )
        });
        let mut next_type_variable = HashMap::<ModuleId, u32>::new();
        let mut previous_type_variable_start = HashMap::new();
        for parameter in type_variables {
            let Some(module) = parameter.id.module() else {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            };
            let Some(source) = relation.get(&module).copied() else {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            };
            let expected = next_type_variable.entry(module).or_insert(0);
            let parameter_span = parameter.origin.primary_span();
            let parameter_range = parameter_span.range();
            self.charge_type_work(1)?;
            if parameter.id.local() != *expected
                || parameter_span.source() != source
                || !origin_depth_within_limit(&parameter.origin)
                || !valid_upper_spelling(&parameter.spelling)
                || parameter_range.start() >= parameter_range.end()
                || previous_type_variable_start
                    .get(&module)
                    .is_some_and(|previous| parameter_range.start() <= *previous)
            {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            }
            *expected = expected
                .checked_add(1)
                .ok_or_else(|| ValidationError::new(ValidationReason::Registry, None))?;
            previous_type_variable_start.insert(module, parameter_range.start());
            self.validate_origin(&parameter.origin, self.program.root)?;
        }

        let mut parameter_owners = HashMap::new();
        for nominal in registry.nominals() {
            let nominal_range = nominal.origin.primary_span().range();
            let parameters = registry
                .nominal_parameters(nominal.id)
                .ok_or_else(|| ValidationError::new(ValidationReason::Registry, None))?;
            let mut parameter_names = HashSet::new();
            let mut previous_parameter_start = None;
            for parameter in parameters {
                #[cfg(test)]
                self.owner_parameter_index_work
                    .set(self.owner_parameter_index_work.get() + 1);
                let parameter_span = parameter.origin.primary_span();
                let parameter_range = parameter_span.range();
                if parameter.id.module() != Some(nominal.id.module())
                    || parameter_owners
                        .insert(parameter.id, RegistryParameterOwner::Nominal(nominal.id))
                        .is_some()
                    || !parameter_names.insert(parameter.spelling.as_str())
                {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
                let canonical = registry
                    .type_variable(parameter.id)
                    .ok_or_else(|| ValidationError::new(ValidationReason::Registry, None))?;
                if !self.same_registry_type_variable(canonical, parameter)?
                    || parameter_range.start() < nominal_range.start()
                    || parameter_range.end() > nominal_range.end()
                    || previous_parameter_start
                        .is_some_and(|previous| parameter_range.start() <= previous)
                {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
                previous_parameter_start = Some(parameter_range.start());
            }
            let source = relation
                .get(&nominal.id.module())
                .copied()
                .ok_or_else(|| ValidationError::new(ValidationReason::Registry, None))?;
            self.validate_nominal_representation(nominal, source, &parameter_owners)?;
        }

        let mut constructor_ids = HashSet::new();
        let mut constructor_names = HashMap::<ModuleId, HashSet<&str>>::new();
        let mut previous_constructor_start = HashMap::new();
        for constructor in registry.constructors() {
            let module = constructor.owner.module();
            let Some(source) = relation.get(&module).copied() else {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            };
            let constructor_span = constructor.origin.primary_span();
            let constructor_range = constructor_span.range();
            let owner_range = registry
                .nominal(constructor.owner)
                .map(|owner| owner.origin.primary_span().range());
            let payload_valid = self.valid_registry_payload(
                constructor.payload.as_ref(),
                constructor.owner,
                &parameter_owners,
            )?;
            let payload_kind_valid = payload_valid
                && self.valid_registry_payload_kind(
                    constructor.payload.as_ref(),
                    constructor.owner,
                    &parameter_owners,
                )?;
            let names = constructor_names.entry(module).or_default();
            if constructor.id.owner() != constructor.owner
                || !nominal_ids.contains(&constructor.owner)
                || constructor_span.source() != source
                || !origin_depth_within_limit(&constructor.origin)
                || !valid_upper_spelling(&constructor.spelling)
                || !constructor_ids.insert(constructor.id)
                || !names.insert(constructor.spelling.as_str())
                || !payload_kind_valid
                || owner_range.is_none_or(|owner| {
                    constructor_range.start() < owner.start()
                        || constructor_range.end() > owner.end()
                })
                || constructor_range.start() >= constructor_range.end()
                || previous_constructor_start
                    .get(&module)
                    .is_some_and(|previous| constructor_range.start() <= *previous)
            {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            }
            previous_constructor_start.insert(module, constructor_range.start());
            self.validate_origin(&constructor.origin, self.program.root)?;
        }

        let expected_constructor_order = registry
            .nominals()
            .iter()
            .flat_map(|nominal| nominal.constructors.iter().copied());
        if !registry
            .constructors()
            .iter()
            .map(|constructor| constructor.id)
            .eq(expected_constructor_order)
        {
            return Err(ValidationError::new(ValidationReason::Registry, None));
        }
        for nominal in registry.nominals() {
            for (index, constructor) in nominal.constructors.iter().copied().enumerate() {
                let expected = ConstructorId::new(
                    nominal.id,
                    u32::try_from(index)
                        .map_err(|_| ValidationError::new(ValidationReason::Registry, None))?,
                );
                if constructor != expected || registry.constructor(constructor).is_none() {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
            }
        }
        if registry.constructors().iter().any(|constructor| {
            registry
                .nominal(constructor.owner)
                .is_none_or(|owner| !constructor_belongs_to_owner(owner, constructor.id))
        }) {
            return Err(ValidationError::new(ValidationReason::Registry, None));
        }
        self.validate_global_parameter_rows(&parameter_owners)?;
        Ok(parameter_owners)
    }

    fn validate_nominal_representation(
        &self,
        nominal: &ResolvedNominalType,
        source: SourceId,
        parameter_owners: &RegistryParameterOwners,
    ) -> Result<(), ValidationError> {
        match nominal.declaration_kind {
            ResolvedNominalDeclarationKind::Data => {
                if nominal.representation.is_some() || nominal.representation_provenance.is_some() {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
            }
            ResolvedNominalDeclarationKind::Newtype => {
                let [constructor] = nominal.constructors.as_ref() else {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                };
                let Some(constructor) = self.program.registry.constructor(*constructor) else {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                };
                let (Some(representation), Some(provenance)) = (
                    nominal.representation.as_ref(),
                    nominal.representation_provenance.as_ref(),
                ) else {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                };
                if !matches!(nominal.origin, Origin::Source(_))
                    || !matches!(constructor.origin, Origin::Source(_))
                    || constructor.owner != nominal.id
                    || constructor.spelling != nominal.spelling
                    || constructor.payload.is_some()
                    || !self.valid_registry_payload(
                        Some(representation),
                        nominal.id,
                        parameter_owners,
                    )?
                    || !self.valid_registry_payload_kind(
                        Some(representation),
                        nominal.id,
                        parameter_owners,
                    )?
                    || !self.valid_representation_provenance(
                        representation,
                        provenance,
                        source,
                        constructor.origin.primary_span(),
                    )?
                {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
            }
        }
        Ok(())
    }

    fn validate_effect_registry(
        &self,
        module_sources: Option<&HashMap<ModuleId, SourceId>>,
        parameter_owners: &mut RegistryParameterOwners,
    ) -> Result<(), ValidationError> {
        let mut previous_effect: Option<crate::types::EffectId> = None;
        for effect in self.program.registry.effects() {
            self.charge_type_work(
                effect
                    .parameters
                    .len()
                    .checked_add(effect.operations.len())
                    .and_then(|cells| cells.checked_add(1))
                    .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?,
            )?;
            let module = effect.id.module();
            let expected_source = module_sources
                .and_then(|relation| relation.get(&module).copied())
                .or_else(|| {
                    (module_sources.is_none() && self.sources.len() == 1)
                        .then(|| self.sources.keys().next().copied())
                        .flatten()
                });
            if expected_source != Some(effect.origin.primary_span().source()) {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            }
            let ordered = match previous_effect {
                None => effect.id.declaration() == 0,
                Some(previous) if previous.module() == module => previous
                    .declaration()
                    .checked_add(1)
                    .is_some_and(|next| next == effect.id.declaration()),
                Some(previous) => previous.module() < module && effect.id.declaration() == 0,
            };
            if !ordered
                || effect.operations.is_empty()
                || !valid_upper_spelling(&effect.spelling)
                || !origin_depth_within_limit(&effect.origin)
                || self.program.registry.effect(effect.id) != Some(effect)
            {
                return Err(ValidationError::new(ValidationReason::Registry, None));
            }
            previous_effect = Some(effect.id);
            self.validate_origin(&effect.origin, self.program.root)?;
            let mut parameter_ids = HashSet::new();
            let mut parameter_spellings = HashSet::new();
            let mut previous_parameter = None;
            for parameter in &effect.parameters {
                self.charge_type_work(3)?;
                parameter_ids
                    .try_reserve(1)
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
                parameter_spellings
                    .try_reserve(1)
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
                parameter_owners
                    .try_reserve(1)
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
                let Some(canonical) = self.program.registry.type_variable(parameter.id) else {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                };
                if parameter.id.module() != Some(module)
                    || previous_parameter.is_some_and(|previous| previous >= parameter.id.local())
                    || !parameter_ids.insert(parameter.id)
                    || !parameter_spellings.insert(parameter.spelling.as_str())
                    || parameter_owners
                        .insert(parameter.id, RegistryParameterOwner::Effect(effect.id))
                        .is_some()
                    || !valid_upper_spelling(&parameter.spelling)
                    || !crate::kind::binder_kind_is_admitted(&parameter.kind, false)
                    || !self.same_registry_type_variable(canonical, parameter)?
                {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
                previous_parameter = Some(parameter.id.local());
            }
            let mut operation_spellings = HashSet::new();
            let empty_type_binders = CoreTypeBinders::new();
            for (ordinal, operation) in effect.operations.iter().enumerate() {
                self.charge_type_work(1)?;
                operation_spellings
                    .try_reserve(1)
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
                if operation.id.owner() != effect.id
                    || usize::try_from(operation.id.operation()) != Ok(ordinal)
                    || !valid_lower_spelling(&operation.spelling)
                    || !operation_spellings.insert(operation.spelling.as_str())
                    || !origin_depth_within_limit(&operation.origin)
                    || operation.origin.primary_span().source()
                        != effect.origin.primary_span().source()
                    || !matches!(operation.annotation.ty, Type::Function(_, _))
                {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
                let Some(kind) = self.synthesize_monotype_kind(
                    &operation.annotation.ty,
                    MonotypeVariableKinds::Core(&empty_type_binders),
                )?
                else {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                };
                if !self.same_kind_charged(&kind, &Kind::Type)? {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
                let mut free = HashSet::new();
                self.collect_free_type_variables(&operation.annotation.ty, &mut free)?;
                if !free.is_subset(&parameter_ids) {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
                self.validate_origin(&operation.origin, self.program.root)?;
            }
        }
        Ok(())
    }

    fn valid_representation_provenance(
        &self,
        representation: &Type,
        provenance: &ResolvedTypeProvenance,
        source: SourceId,
        declaration: Span,
    ) -> Result<bool, ValidationError> {
        let nodes = provenance.nodes();
        if nodes.is_empty() || provenance.root() >= nodes.len() {
            return Ok(false);
        }
        self.charge_type_work(nodes.len())?;
        let mut visited = HashSet::new();
        visited
            .try_reserve(nodes.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        let mut work = Vec::new();
        self.charge_type_work(1)?;
        work.try_reserve(1)
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        work.push((representation, provenance.root(), declaration));
        while let Some((ty, index, parent)) = work.pop() {
            self.charge_type_work(1)?;
            let Some(node) = nodes.get(index) else {
                return Ok(false);
            };
            if !visited.insert(index) {
                return Ok(false);
            }
            let span = representation_provenance_span(node);
            if span.source() != source
                || span.range().start() >= span.range().end()
                || !span_contains(parent, span)
            {
                return Ok(false);
            }
            match (ty, node) {
                (
                    Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) | Type::Variable(_),
                    ResolvedTypeProvenanceNode::Fact(_),
                ) => {}
                (
                    Type::Application(function, argument),
                    ResolvedTypeProvenanceNode::Application {
                        function: function_index,
                        argument: argument_index,
                        argument_span,
                        ..
                    },
                ) => {
                    if nodes
                        .get(*argument_index)
                        .is_none_or(|node| representation_provenance_span(node) != *argument_span)
                    {
                        return Ok(false);
                    }
                    self.charge_type_work(2)?;
                    work.try_reserve(2)
                        .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
                    work.push((argument, *argument_index, span));
                    work.push((function, *function_index, span));
                }
                (
                    Type::Tuple(elements),
                    ResolvedTypeProvenanceNode::Tuple {
                        elements: provenance_elements,
                        ..
                    },
                ) if elements.len() == provenance_elements.len() => {
                    self.charge_type_work(elements.len())?;
                    work.try_reserve(elements.len())
                        .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
                    work.extend(
                        elements
                            .iter()
                            .zip(provenance_elements.iter().copied())
                            .rev()
                            .map(|(element, index)| (element, index, span)),
                    );
                }
                (
                    Type::Function(domain, codomain),
                    ResolvedTypeProvenanceNode::Function {
                        domain: domain_index,
                        codomain: codomain_index,
                        effect_arguments,
                        ..
                    },
                ) if effect_arguments.is_empty() => {
                    self.charge_type_work(2)?;
                    work.try_reserve(2)
                        .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
                    work.push((codomain, *codomain_index, span));
                    work.push((domain, *domain_index, span));
                }
                (
                    Type::EffectfulFunction(domain, codomain),
                    ResolvedTypeProvenanceNode::Function {
                        domain: domain_index,
                        codomain: codomain_index,
                        effect_arguments,
                        ..
                    },
                ) if F::ALLOWS_EFFECTFUL_TYPES
                    && effect_arguments.len() == codomain.effect_argument_count() =>
                {
                    let child_count = effect_arguments
                        .len()
                        .checked_add(2)
                        .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?;
                    self.charge_type_work(child_count)?;
                    work.try_reserve(child_count)
                        .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
                    let argument_start = work.len();
                    work.extend(
                        codomain
                            .effect_arguments()
                            .zip(effect_arguments.iter().copied())
                            .map(|(argument, index)| (argument, index, span)),
                    );
                    work[argument_start..].reverse();
                    work.push((codomain.value(), *codomain_index, span));
                    work.push((domain, *domain_index, span));
                }
                (Type::Forall(_, _) | Type::Inference(_), _) | (_, _) => return Ok(false),
            }
        }
        Ok(visited.len() == nodes.len())
    }
    fn valid_type(&self, root: Option<&Type>) -> Result<bool, ValidationError> {
        self.valid_type_with_scheme(root, true)
    }

    fn valid_monotype(&self, root: Option<&Type>) -> Result<bool, ValidationError> {
        self.valid_type_with_scheme(root, false)
    }

    fn valid_type_with_scheme(
        &self,
        root: Option<&Type>,
        allow_scheme: bool,
    ) -> Result<bool, ValidationError> {
        let Some(root) = root else {
            return Ok(true);
        };
        enum Task<'a> {
            Visit(&'a Type, bool, usize, usize),
            Sequence(std::slice::Iter<'a, Type>, usize),
        }
        let mut work = vec![Task::Visit(root, allow_scheme, 0, 0)];
        while let Some(task) = work.pop() {
            #[cfg(test)]
            self.type_validation_pending_peak
                .set(self.type_validation_pending_peak.get().max(work.len() + 1));
            match task {
                Task::Visit(ty, allow_scheme, depth, applied_arguments) => {
                    if depth > super::dialect::CORE_PAYLOAD_DEPTH_LIMIT {
                        return Ok(false);
                    }
                    self.charge_type_work(1)?;
                    match ty {
                        Type::Int | Type::Bool | Type::Unit => {}
                        Type::Nominal(id) => {
                            if self.program.registry.nominal_parameters(*id).is_none() {
                                return Ok(false);
                            }
                        }
                        Type::Variable(_) | Type::Inference(_) => {}
                        Type::Application(function, argument) => {
                            let child_depth = depth.saturating_add(1);
                            work.push(Task::Visit(argument, false, child_depth, 0));
                            work.push(Task::Visit(
                                function,
                                false,
                                depth,
                                applied_arguments.saturating_add(1),
                            ));
                        }
                        Type::Forall(parameters, body)
                            if allow_scheme && applied_arguments == 0 =>
                        {
                            self.charge_kinded_parameters(parameters)?;
                            let mut unique = HashSet::new();
                            unique.try_reserve(parameters.len()).map_err(|_| {
                                ValidationError::new(ValidationReason::Resource, None)
                            })?;
                            if parameters.is_empty()
                                || !parameters
                                    .iter()
                                    .all(|(parameter, _)| unique.insert(*parameter))
                            {
                                return Ok(false);
                            }
                            work.push(Task::Visit(body, false, depth.saturating_add(1), 0));
                        }
                        Type::Forall(_, _) => return Ok(false),
                        Type::Tuple(elements) if elements.len() >= 2 => {
                            work.push(Task::Sequence(elements.iter(), depth.saturating_add(1)));
                        }
                        Type::Tuple(_) => return Ok(false),
                        Type::Function(domain, codomain) => {
                            let child_depth = depth.saturating_add(1);
                            work.push(Task::Visit(codomain, false, child_depth, 0));
                            work.push(Task::Visit(domain, false, child_depth, 0));
                        }
                        Type::EffectfulFunction(domain, codomain) if F::ALLOWS_EFFECTFUL_TYPES => {
                            let child_depth = depth.saturating_add(1);
                            work.push(Task::Visit(codomain.value(), false, child_depth, 0));
                            work.push(Task::Visit(domain, false, child_depth, 0));
                        }
                        Type::EffectfulFunction(_, _) => return Ok(false),
                    }
                }
                Task::Sequence(mut remaining, depth) => {
                    if let Some(ty) = remaining.next() {
                        work.push(Task::Sequence(remaining, depth));
                        work.push(Task::Visit(ty, false, depth, 0));
                    }
                }
            }
        }
        Ok(true)
    }

    fn valid_registry_payload(
        &self,
        root: Option<&Type>,
        owner: crate::types::NominalTypeId,
        parameter_owners: &RegistryParameterOwners,
    ) -> Result<bool, ValidationError> {
        let Some(root) = root else {
            return Ok(true);
        };
        enum Task<'a> {
            Visit(&'a Type, usize),
            Sequence(std::slice::Iter<'a, Type>, usize),
        }
        let mut work = vec![Task::Visit(root, 0)];
        while let Some(task) = work.pop() {
            let Task::Visit(ty, depth) = task else {
                let Task::Sequence(mut remaining, depth) = task else {
                    unreachable!()
                };
                if let Some(ty) = remaining.next() {
                    work.push(Task::Sequence(remaining, depth));
                    work.push(Task::Visit(ty, depth));
                }
                continue;
            };
            if depth > super::dialect::CORE_PAYLOAD_DEPTH_LIMIT {
                return Ok(false);
            }
            self.charge_type_work(1)?;
            match ty {
                Type::Int | Type::Bool | Type::Unit => {}
                Type::Nominal(id) => {
                    if self.program.registry.nominal_parameters(*id).is_none() {
                        return Ok(false);
                    }
                }
                Type::Variable(variable)
                    if parameter_owners.get(variable)
                        == Some(&RegistryParameterOwner::Nominal(owner)) => {}
                Type::Variable(_) | Type::Inference(_) | Type::Forall(_, _) => return Ok(false),
                Type::Application(function, argument) => {
                    let child_depth = depth.saturating_add(1);
                    work.push(Task::Visit(argument, child_depth));
                    work.push(Task::Visit(function, depth));
                }
                Type::Tuple(elements) if elements.len() >= 2 => {
                    work.push(Task::Sequence(elements.iter(), depth.saturating_add(1)));
                }
                Type::Tuple(_) => return Ok(false),
                Type::Function(domain, codomain) => {
                    let child_depth = depth.saturating_add(1);
                    work.push(Task::Visit(codomain, child_depth));
                    work.push(Task::Visit(domain, child_depth));
                }
                Type::EffectfulFunction(domain, codomain) if F::ALLOWS_EFFECTFUL_TYPES => {
                    let child_depth = depth.saturating_add(1);
                    work.push(Task::Visit(codomain.value(), child_depth));
                    work.push(Task::Visit(domain, child_depth));
                }
                Type::EffectfulFunction(_, _) => return Ok(false),
            }
        }
        Ok(true)
    }

    fn valid_registry_payload_kind(
        &self,
        root: Option<&Type>,
        owner: crate::types::NominalTypeId,
        parameter_owners: &RegistryParameterOwners,
    ) -> Result<bool, ValidationError> {
        let Some(root) = root else {
            return Ok(true);
        };
        let Some(kind) = self.synthesize_monotype_kind(
            root,
            MonotypeVariableKinds::Registry {
                owner,
                parameter_owners,
            },
        )?
        else {
            return Ok(false);
        };
        self.same_kind_charged(&kind, &Kind::Type)
    }

    fn charge_type_work(&self, cells: usize) -> Result<(), ValidationError> {
        let attempted = self
            .type_work
            .get()
            .checked_add(cells)
            .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?;
        if attempted > CORE_VALIDATION_TYPE_WORK_LIMIT {
            return Err(ValidationError::new(ValidationReason::Resource, None));
        }
        let next = attempted;
        self.type_work.set(next);
        Ok(())
    }

    fn charge_kind(&self, root: &Kind) -> Result<(), ValidationError> {
        let mut work = vec![root];
        while let Some(kind) = work.pop() {
            self.charge_type_work(1)?;
            if let Kind::Arrow(domain, codomain) = kind {
                work.push(codomain);
                work.push(domain);
            }
        }
        Ok(())
    }

    fn charge_kinded_parameters(
        &self,
        parameters: &[(crate::types::TypeVariableId, Kind)],
    ) -> Result<(), ValidationError> {
        for (_, kind) in parameters {
            self.charge_type_work(1)?;
            self.charge_kind(kind)?;
        }
        Ok(())
    }

    fn same_kinded_parameters(
        &self,
        left: &[(crate::types::TypeVariableId, Kind)],
        right: &[(crate::types::TypeVariableId, Kind)],
    ) -> Result<bool, ValidationError> {
        if left.len() != right.len() {
            return Ok(false);
        }
        for ((left_id, left_kind), (right_id, right_kind)) in left.iter().zip(right) {
            self.charge_type_work(1)?;
            if left_id != right_id {
                return Ok(false);
            }
            if !self.same_kind_charged(left_kind, right_kind)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn same_kind_charged(&self, left: &Kind, right: &Kind) -> Result<bool, ValidationError> {
        let mut work = vec![(left, right)];
        while let Some((left, right)) = work.pop() {
            self.charge_type_work(1)?;
            match (left, right) {
                (Kind::Type, Kind::Type) | (Kind::EffectRow, Kind::EffectRow) => {}
                (
                    Kind::Arrow(left_domain, left_codomain),
                    Kind::Arrow(right_domain, right_codomain),
                ) => {
                    work.push((left_codomain, right_codomain));
                    work.push((left_domain, right_domain));
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    fn same_type_charged(&self, left: &Type, right: &Type) -> Result<bool, ValidationError> {
        let mut budget = crate::types::TypeWorkBudget::with_limit(
            CORE_VALIDATION_TYPE_WORK_LIMIT.saturating_sub(self.type_work.get()),
        );
        let result = same_type_with_budget(left, right, &mut budget);
        self.charge_type_work(budget.used())?;
        result.map_err(|()| ValidationError::new(ValidationReason::Resource, None))
    }

    fn same_interface_application(
        &self,
        left: &InterfaceApplication,
        right: &InterfaceApplication,
    ) -> Result<bool, ValidationError> {
        self.charge_type_work(1)?;
        if left.interface() != right.interface()
            || left.arguments().len() != right.arguments().len()
        {
            return Ok(false);
        }
        for (left, right) in left.arguments().iter().zip(right.arguments()) {
            if !self.same_type_charged(left, right)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn substitute_interface_application(
        &self,
        application: &InterfaceApplication,
        replacements: &HashMap<crate::types::TypeVariableId, Type>,
    ) -> Result<InterfaceApplication, ValidationError> {
        self.charge_type_work(application.arguments().len())?;
        let mut arguments = OwnedTypeBuffer(Vec::new());
        arguments
            .try_reserve(application.arguments().len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        for argument in application.arguments() {
            arguments.push(substitute_type_variables_with(
                argument,
                replacements,
                |cells| self.charge_type_work(cells),
                || ValidationError::new(ValidationReason::Resource, None),
            )?);
        }
        Ok(InterfaceApplication::new(
            application.interface(),
            arguments.into_boxed_slice(),
        ))
    }

    fn clone_type_charged(&self, ty: &Type) -> Result<Type, ValidationError> {
        let mut budget = TypeWorkBudget::with_limit(
            CORE_VALIDATION_TYPE_WORK_LIMIT.saturating_sub(self.type_work.get()),
        );
        let result = clone_type_with_budget(ty, &mut budget);
        self.charge_type_work(budget.used())?;
        result.map_err(|()| ValidationError::new(ValidationReason::Resource, None))
    }

    fn clone_effect_row_charged(&self, row: &EffectRow) -> Result<EffectRow, ValidationError> {
        let mut budget = TypeWorkBudget::with_limit(
            CORE_VALIDATION_TYPE_WORK_LIMIT.saturating_sub(self.type_work.get()),
        );
        let result = clone_effect_row_with_budget(row, &mut budget);
        self.charge_type_work(budget.used())?;
        result.map_err(|()| ValidationError::new(ValidationReason::Resource, None))
    }

    fn same_effect_row_charged(
        &self,
        left: &EffectRow,
        right: &EffectRow,
        node: NodeId,
    ) -> Result<bool, ValidationError> {
        let mut budget = TypeWorkBudget::with_limit(
            CORE_VALIDATION_TYPE_WORK_LIMIT.saturating_sub(self.type_work.get()),
        );
        let result = same_effect_rows_with_budget(left, right, &mut budget);
        self.charge_type_work(budget.used())?;
        result.map_err(|()| ValidationError::new(ValidationReason::Resource, Some(node)))
    }

    fn union_effect_rows_charged(
        &self,
        left: &EffectRow,
        right: &EffectRow,
        node: NodeId,
    ) -> Result<EffectRow, ValidationError> {
        let mut budget = TypeWorkBudget::with_limit(
            CORE_VALIDATION_TYPE_WORK_LIMIT.saturating_sub(self.type_work.get()),
        );
        let result = left.union_with_budget(right, &mut budget);
        self.charge_type_work(budget.used())?;
        result
            .map_err(|()| ValidationError::new(ValidationReason::Resource, Some(node)))?
            .map_err(|_| ValidationError::new(ValidationReason::EffectRow, Some(node)))
    }

    fn remove_effect_row_charged(
        &self,
        row: &EffectRow,
        effect: &EffectInstance,
        node: NodeId,
    ) -> Result<EffectRow, ValidationError> {
        let mut budget = TypeWorkBudget::with_limit(
            CORE_VALIDATION_TYPE_WORK_LIMIT.saturating_sub(self.type_work.get()),
        );
        let result = row.remove_exact_with_budget(effect, &mut budget);
        self.charge_type_work(budget.used())?;
        result
            .map_err(|()| ValidationError::new(ValidationReason::Resource, Some(node)))?
            .map_err(|_| ValidationError::new(ValidationReason::EffectRow, Some(node)))
    }

    fn singleton_effect_row_charged(
        &self,
        effect: &EffectInstance,
        node: NodeId,
    ) -> Result<EffectRow, ValidationError> {
        let mut budget = TypeWorkBudget::with_limit(
            CORE_VALIDATION_TYPE_WORK_LIMIT.saturating_sub(self.type_work.get()),
        );
        let result = rebuild_effect_row_with_budget(
            std::iter::once(effect),
            None,
            std::iter::empty(),
            clone_type_with_budget,
            &mut budget,
        );
        self.charge_type_work(budget.used())?;
        result.map_err(|()| ValidationError::new(ValidationReason::Resource, Some(node)))
    }

    fn constructor_value_type_matches(
        &self,
        annotation: &Type,
        constructor: &ResolvedConstructor,
        parameters: &[ResolvedTypeVariable],
    ) -> Result<bool, ValidationError> {
        let monotype = if parameters.is_empty() {
            annotation
        } else {
            let Type::Forall(actual_parameters, body) = annotation else {
                return Ok(false);
            };
            if actual_parameters.len() != parameters.len() {
                return Ok(false);
            }
            for ((actual, actual_kind), expected) in actual_parameters.iter().zip(parameters) {
                self.charge_type_work(1)?;
                if *actual != expected.id || !self.same_kind_charged(actual_kind, &expected.kind)? {
                    return Ok(false);
                }
            }
            body
        };
        let result = if let Some(payload) = constructor.payload.as_ref() {
            let Type::Function(actual_payload, result) = monotype else {
                return Ok(false);
            };
            if !self.same_type_charged(actual_payload, payload)? {
                return Ok(false);
            }
            result.as_ref()
        } else {
            monotype
        };
        let mut current = result;
        for parameter in parameters.iter().rev() {
            self.charge_type_work(1)?;
            let Type::Application(function, argument) = current else {
                return Ok(false);
            };
            if !matches!(argument.as_ref(), Type::Variable(identity) if *identity == parameter.id) {
                return Ok(false);
            }
            current = function;
        }
        self.charge_type_work(1)?;
        Ok(matches!(current, Type::Nominal(owner) if *owner == constructor.owner))
    }

    fn nominal_application_head_and_arity(
        &self,
        ty: &Type,
    ) -> Result<Option<(crate::types::NominalTypeId, usize)>, ValidationError> {
        let mut arity = 0usize;
        let mut function = ty;
        loop {
            self.charge_type_work(1)?;
            let Type::Application(next, _) = function else {
                break;
            };
            arity = arity
                .checked_add(1)
                .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?;
            function = next;
        }
        let Type::Nominal(owner) = function else {
            return Ok(None);
        };
        Ok(Some((*owner, arity)))
    }

    fn clone_kind_charged(&self, kind: &Kind) -> Result<Kind, ValidationError> {
        self.charge_kind(kind)?;
        Ok(kind.clone())
    }

    fn synthesize_monotype_kind(
        &self,
        root: &Type,
        variable_kinds: MonotypeVariableKinds<'_, '_>,
    ) -> Result<Option<Kind>, ValidationError> {
        enum Task<'a> {
            Visit(&'a Type),
            Sequence(std::slice::Iter<'a, Type>),
            FinishTuple(usize),
            FinishApplication,
            FinishFunction,
        }

        let resource = || ValidationError::new(ValidationReason::Resource, None);
        let mut work = Vec::new();
        work.try_reserve(1).map_err(|_| resource())?;
        work.push(Task::Visit(root));
        let mut completed = Vec::new();
        while let Some(task) = work.pop() {
            match task {
                Task::Visit(Type::Int | Type::Bool | Type::Unit) => {
                    self.charge_type_work(1)?;
                    completed.try_reserve(1).map_err(|_| resource())?;
                    completed.push(Kind::Type);
                }
                Task::Visit(Type::Nominal(identity)) => {
                    let Some(parameters) = self.program.registry.nominal_parameters(*identity)
                    else {
                        self.charge_type_work(1)?;
                        return Err(ValidationError::new(ValidationReason::Registry, None));
                    };
                    self.charge_type_work(1)?;
                    let mut result = Kind::Type;
                    for parameter in parameters.iter().rev() {
                        let domain = self.clone_kind_charged(&parameter.kind)?;
                        self.charge_type_work(1)?;
                        result = Kind::Arrow(Box::new(domain), Box::new(result));
                    }
                    completed.try_reserve(1).map_err(|_| resource())?;
                    completed.push(result);
                }
                Task::Visit(Type::Variable(identity)) => {
                    let kind = match variable_kinds {
                        MonotypeVariableKinds::Registry {
                            owner,
                            parameter_owners,
                        } => {
                            if parameter_owners.get(identity)
                                != Some(&RegistryParameterOwner::Nominal(owner))
                            {
                                self.charge_type_work(1)?;
                                return Err(ValidationError::new(ValidationReason::Registry, None));
                            }
                            let Some(parameter) = self.program.registry.type_variable(*identity)
                            else {
                                self.charge_type_work(1)?;
                                return Err(ValidationError::new(ValidationReason::Registry, None));
                            };
                            &parameter.kind
                        }
                        MonotypeVariableKinds::Core(type_binders) => match identity {
                            crate::types::TypeVariableId::Resolved { .. } => {
                                let Some(parameter) =
                                    self.program.registry.type_variable(*identity)
                                else {
                                    self.charge_type_work(1)?;
                                    return Err(ValidationError::new(
                                        ValidationReason::Registry,
                                        None,
                                    ));
                                };
                                &parameter.kind
                            }
                            crate::types::TypeVariableId::Generated(_) => {
                                let Some((kind, _)) = type_binders.get(identity) else {
                                    self.charge_type_work(1)?;
                                    return Err(ValidationError::new(
                                        ValidationReason::TypeScope,
                                        None,
                                    ));
                                };
                                *kind
                            }
                        },
                    };
                    let retained = self.clone_kind_charged(kind)?;
                    completed.try_reserve(1).map_err(|_| resource())?;
                    completed.push(retained);
                }
                Task::Visit(Type::Inference(_)) => {
                    self.charge_type_work(1)?;
                    return Err(ValidationError::new(
                        match variable_kinds {
                            MonotypeVariableKinds::Core(_) => ValidationReason::TypeScope,
                            MonotypeVariableKinds::Registry { .. } => ValidationReason::Registry,
                        },
                        None,
                    ));
                }
                Task::Visit(Type::Forall(_, _)) => {
                    self.charge_type_work(1)?;
                    return Ok(None);
                }
                Task::Visit(Type::Tuple(elements)) => {
                    self.charge_type_work(1)?;
                    work.try_reserve(2).map_err(|_| resource())?;
                    work.push(Task::FinishTuple(elements.len()));
                    work.push(Task::Sequence(elements.iter()));
                }
                Task::Visit(Type::Application(function, argument)) => {
                    self.charge_type_work(1)?;
                    work.try_reserve(3).map_err(|_| resource())?;
                    work.push(Task::FinishApplication);
                    work.push(Task::Visit(argument));
                    work.push(Task::Visit(function));
                }
                Task::Visit(Type::Function(domain, codomain)) => {
                    self.charge_type_work(1)?;
                    work.try_reserve(3).map_err(|_| resource())?;
                    work.push(Task::FinishFunction);
                    work.push(Task::Visit(codomain));
                    work.push(Task::Visit(domain));
                }
                Task::Visit(Type::EffectfulFunction(domain, codomain)) => {
                    if !F::ALLOWS_EFFECTFUL_TYPES {
                        return Ok(None);
                    }
                    self.charge_type_work(1)?;
                    work.try_reserve(3).map_err(|_| resource())?;
                    work.push(Task::FinishFunction);
                    work.push(Task::Visit(codomain.value()));
                    work.push(Task::Visit(domain));
                }
                Task::Sequence(mut remaining) => {
                    if let Some(next) = remaining.next() {
                        work.try_reserve(2).map_err(|_| resource())?;
                        work.push(Task::Sequence(remaining));
                        work.push(Task::Visit(next));
                    }
                }
                Task::FinishTuple(count) => {
                    if completed.len() < count {
                        return Err(ValidationError::new(ValidationReason::TypeOperation, None));
                    }
                    let kinds = completed.split_off(completed.len() - count);
                    for kind in kinds {
                        if !self.same_kind_charged(&kind, &Kind::Type)? {
                            return Ok(None);
                        }
                    }
                    completed.try_reserve(1).map_err(|_| resource())?;
                    completed.push(Kind::Type);
                }
                Task::FinishApplication => {
                    let Some(argument) = completed.pop() else {
                        return Err(ValidationError::new(ValidationReason::TypeOperation, None));
                    };
                    let Some(mut function) = completed.pop() else {
                        return Err(ValidationError::new(ValidationReason::TypeOperation, None));
                    };
                    let Kind::Arrow(domain, codomain) = &mut function else {
                        return Ok(None);
                    };
                    if !self.same_kind_charged(domain, &argument)? {
                        return Ok(None);
                    }
                    let result = std::mem::replace(codomain.as_mut(), Kind::Type);
                    completed.try_reserve(1).map_err(|_| resource())?;
                    completed.push(result);
                }
                Task::FinishFunction => {
                    let Some(codomain) = completed.pop() else {
                        return Err(ValidationError::new(ValidationReason::TypeOperation, None));
                    };
                    let Some(domain) = completed.pop() else {
                        return Err(ValidationError::new(ValidationReason::TypeOperation, None));
                    };
                    if !self.same_kind_charged(&domain, &Kind::Type)?
                        || !self.same_kind_charged(&codomain, &Kind::Type)?
                    {
                        return Ok(None);
                    }
                    completed.try_reserve(1).map_err(|_| resource())?;
                    completed.push(Kind::Type);
                }
            }
        }
        if completed.len() == 1 {
            Ok(completed.pop())
        } else {
            Err(ValidationError::new(ValidationReason::TypeOperation, None))
        }
    }

    fn valid_core_type_kind(
        &self,
        ty: &Type,
        type_binders: &CoreTypeBinders<'program>,
    ) -> Result<bool, ValidationError> {
        let body = if let Type::Forall(parameters, body) = ty {
            if parameters.is_empty() {
                return Ok(false);
            }
            let mut seen = HashSet::new();
            seen.try_reserve(parameters.len())
                .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
            for (parameter, kind) in parameters {
                self.charge_type_work(1)?;
                if !seen.insert(*parameter) {
                    return Ok(false);
                }
                let canonical = match parameter {
                    crate::types::TypeVariableId::Resolved { .. } => self
                        .program
                        .registry
                        .type_variable(*parameter)
                        .map(|parameter| &parameter.kind),
                    crate::types::TypeVariableId::Generated(_) => {
                        type_binders.get(parameter).map(|(kind, _)| *kind)
                    }
                };
                let Some(canonical) = canonical else {
                    self.charge_type_work(1)?;
                    return Err(ValidationError::new(
                        match parameter {
                            crate::types::TypeVariableId::Resolved { .. } => {
                                ValidationReason::Registry
                            }
                            crate::types::TypeVariableId::Generated(_) => {
                                ValidationReason::TypeScope
                            }
                        },
                        None,
                    ));
                };
                if !self.same_kind_charged(canonical, kind)? {
                    return Ok(false);
                }
            }
            body.as_ref()
        } else {
            ty
        };
        let Some(kind) =
            self.synthesize_monotype_kind(body, MonotypeVariableKinds::Core(type_binders))?
        else {
            return Ok(false);
        };
        self.same_kind_charged(&kind, &Kind::Type)
    }

    fn same_registry_type_variable(
        &self,
        left: &ResolvedTypeVariable,
        right: &ResolvedTypeVariable,
    ) -> Result<bool, ValidationError> {
        same_resolved_type_variables_with_charge(
            std::slice::from_ref(left),
            std::slice::from_ref(right),
            |work| self.charge_type_work(work).map_err(|_| ()),
        )
        .map_err(|()| ValidationError::new(ValidationReason::Resource, None))
    }

    fn charge_type_structure(&self, ty: &Type) -> Result<(), ValidationError> {
        enum Task<'a> {
            Visit(&'a Type),
            Sequence(std::slice::Iter<'a, Type>),
        }
        let mut work = vec![Task::Visit(ty)];
        while let Some(task) = work.pop() {
            let Task::Visit(ty) = task else {
                let Task::Sequence(mut remaining) = task else {
                    unreachable!()
                };
                if let Some(ty) = remaining.next() {
                    work.push(Task::Sequence(remaining));
                    work.push(Task::Visit(ty));
                }
                continue;
            };
            self.charge_type_work(1)?;
            match ty {
                Type::Tuple(elements) => {
                    work.push(Task::Sequence(elements.iter()));
                }
                Type::Application(function, argument) => {
                    work.push(Task::Visit(argument));
                    work.push(Task::Visit(function));
                }
                Type::Function(domain, codomain) => {
                    work.push(Task::Visit(codomain));
                    work.push(Task::Visit(domain));
                }
                Type::EffectfulFunction(domain, codomain) => {
                    work.push(Task::Visit(codomain.value()));
                    work.push(Task::Visit(domain));
                }
                Type::Forall(parameters, body) => {
                    self.charge_kinded_parameters(parameters)?;
                    work.push(Task::Visit(body));
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

    fn charge_pattern_type_structure(&self, pattern: &CorePattern) -> Result<(), ValidationError> {
        enum Task<'a> {
            Visit(&'a CorePattern),
            Sequence(std::slice::Iter<'a, CorePattern>),
        }
        let mut work = vec![Task::Visit(pattern)];
        while let Some(task) = work.pop() {
            let Task::Visit(pattern) = task else {
                let Task::Sequence(mut remaining) = task else {
                    unreachable!()
                };
                if let Some(pattern) = remaining.next() {
                    work.push(Task::Sequence(remaining));
                    work.push(Task::Visit(pattern));
                }
                continue;
            };
            self.charge_type_structure(&pattern.ty)?;
            match &pattern.kind {
                CorePatternKind::Binder(binder) => {
                    self.charge_type_structure(binder.ty())?;
                }
                CorePatternKind::Tuple(elements) => work.push(Task::Sequence(elements.iter())),
                CorePatternKind::Constructor { payload, .. } => {
                    if let Some(payload) = payload.as_deref() {
                        work.push(Task::Visit(payload));
                    }
                }
                CorePatternKind::Wildcard | CorePatternKind::Boolean(_) | CorePatternKind::Unit => {
                }
            }
        }
        Ok(())
    }

    fn validate_envelopes(
        &self,
        authenticated_method_evidence: &HashSet<NodeId>,
    ) -> Result<(), ValidationError> {
        for (index, node) in self.program.nodes.iter().enumerate() {
            let id = node_id(self.program.arena, index)?;
            if !F::ALLOWS_EFFECTFUL_TYPES
                && !authenticated_method_evidence.contains(&id)
                && !self.valid_type(Some(&node.ty))?
            {
                return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
            }
            if F::REQUIRES_EMPTY_ROWS && !F::effect_row(&node.effects).is_empty() {
                return Err(ValidationError::new(ValidationReason::EffectRow, Some(id)));
            }
            if node.dialect != DialectId::named(F::DIALECT_NAME) {
                return Err(ValidationError::new(
                    ValidationReason::DialectMembership,
                    Some(id),
                ));
            }
            let Some(origin) = node.origin.as_ref() else {
                return Err(ValidationError::new(ValidationReason::Provenance, Some(id)));
            };
            self.validate_origin(origin, id)?;
        }
        Ok(())
    }

    fn validate_origin(&self, origin: &Origin, node: NodeId) -> Result<(), ValidationError> {
        if !origin_depth_within_limit(origin) {
            return Err(ValidationError::new(
                ValidationReason::Provenance,
                Some(node),
            ));
        }
        let mut work = vec![origin];
        while let Some(current) = work.pop() {
            match current {
                Origin::Source(span) => self.validate_span(*span, node)?,
                Origin::Generated { cause, .. } => work.push(cause),
                Origin::Related { primary, related } => {
                    let primary_source = primary.primary_span().source();
                    for span in related {
                        if span.source() != primary_source {
                            return Err(ValidationError::new(
                                ValidationReason::Provenance,
                                Some(node),
                            ));
                        }
                        self.validate_span(*span, node)?;
                    }
                    work.push(primary);
                }
            }
        }
        Ok(())
    }

    fn validate_span(&self, span: Span, node: NodeId) -> Result<(), ValidationError> {
        let Some(source) = self.sources.get(&span.source()) else {
            return Err(ValidationError::new(
                ValidationReason::Provenance,
                Some(node),
            ));
        };
        source
            .span(span.range())
            .map_err(|_| ValidationError::new(ValidationReason::Provenance, Some(node)))?;
        Ok(())
    }

    fn validate_graph(&self) -> Result<(), ValidationError> {
        if self.node(self.program.root).is_err() {
            return Err(ValidationError::new(ValidationReason::Root, None));
        }

        let mut colors = vec![Color::White; self.program.nodes.len()];
        let mut work = vec![GraphTask::Enter(self.program.root)];
        while let Some(task) = work.pop() {
            match task {
                GraphTask::Enter(id) => {
                    let index = self.index(id)?;
                    match colors[index] {
                        Color::Gray => {
                            return Err(ValidationError::new(ValidationReason::Cycle, Some(id)));
                        }
                        Color::Black => continue,
                        Color::White => {}
                    }
                    colors[index] = Color::Gray;
                    let node = self.node(id)?;
                    self.charge_type_work(F::operation_extra_edge_count(&node.kind))?;
                    let child_count = F::child_count(&node.kind);
                    let pending = child_count.checked_add(1).ok_or_else(|| {
                        ValidationError::new(ValidationReason::Resource, Some(id))
                    })?;
                    work.try_reserve(pending)
                        .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?;
                    work.push(GraphTask::Exit(id));
                    for child_index in (0..child_count).rev() {
                        let Some(child) = F::child_at(&node.kind, child_index) else {
                            return Err(ValidationError::new(
                                ValidationReason::NodeBounds,
                                Some(id),
                            ));
                        };
                        if self.node(child).is_err() {
                            return Err(ValidationError::new(
                                ValidationReason::NodeBounds,
                                Some(id),
                            ));
                        }
                        work.push(GraphTask::Enter(child));
                    }
                }
                GraphTask::Exit(id) => {
                    let index = self.index(id)?;
                    colors[index] = Color::Black;
                }
            }
        }

        if let Some(index) = colors.iter().position(|color| *color == Color::White) {
            return Err(ValidationError::new(
                ValidationReason::Unreachable,
                Some(node_id(self.program.arena, index)?),
            ));
        }
        Ok(())
    }

    fn collect_binders(
        &mut self,
        authenticated_method_evidence: &HashSet<NodeId>,
    ) -> Result<CoreAbstractionOwners, ValidationError> {
        let mut abstraction_owners = HashMap::new();
        for (index, node) in self.program.nodes.iter().enumerate() {
            let id = node_id(self.program.arena, index)?;
            match F::pure(&node.kind) {
                Some(PureExprKind::Value(PureValue::Function(function))) => {
                    self.collect_binder(
                        id,
                        function.parameter(),
                        ValidationReason::NodeType,
                        true,
                        false,
                    )?;
                }
                Some(PureExprKind::Computation(PureComputation::Bind(binding))) => {
                    self.collect_binder(
                        id,
                        binding.binder(),
                        ValidationReason::NodeType,
                        true,
                        false,
                    )?;
                    let initializer = binding.initializer();
                    if self.module_sources.is_some()
                        && let Some(PureExprKind::Computation(PureComputation::TypeAbstraction(
                            abstraction,
                        ))) = F::pure(&self.node(initializer)?.kind)
                        && abstraction
                            .parameters()
                            .first()
                            .is_some_and(|(parameter, _)| {
                                matches!(parameter, crate::types::TypeVariableId::Resolved { .. })
                            })
                    {
                        return Err(ValidationError::new(
                            ValidationReason::Registry,
                            Some(initializer),
                        ));
                    }
                }
                Some(PureExprKind::Computation(PureComputation::RecursiveBind(group))) => {
                    for member in group.members() {
                        self.collect_binder(
                            id,
                            member.binder(),
                            ValidationReason::NodeType,
                            true,
                            authenticated_method_evidence.contains(&member.initializer()),
                        )?;
                        let initializer = member.initializer();
                        if self.module_sources.is_some()
                            && matches!(
                                F::pure(&self.node(initializer)?.kind),
                                Some(PureExprKind::Computation(PureComputation::TypeAbstraction(
                                    _
                                )))
                            )
                        {
                            self.charge_type_work(1)?;
                            if abstraction_owners.contains_key(&initializer) {
                                return Err(ValidationError::new(
                                    ValidationReason::Registry,
                                    Some(initializer),
                                ));
                            }
                            abstraction_owners.try_reserve(1).map_err(|_| {
                                ValidationError::new(ValidationReason::Resource, Some(initializer))
                            })?;
                            abstraction_owners.insert(initializer, member.binder().id());
                        }
                    }
                }
                Some(PureExprKind::Computation(PureComputation::Match(match_node))) => {
                    for arm in match_node.arms() {
                        for binder in arm.pattern().binder_iter() {
                            self.collect_binder(
                                id,
                                binder,
                                ValidationReason::Pattern,
                                false,
                                false,
                            )?;
                        }
                    }
                }
                Some(
                    PureExprKind::Value(
                        PureValue::Integer(_)
                        | PureValue::Boolean(_)
                        | PureValue::Unit(_)
                        | PureValue::Constructor(_),
                    )
                    | PureExprKind::Variable(_)
                    | PureExprKind::Computation(
                        PureComputation::Apply(_)
                        | PureComputation::Primitive(_)
                        | PureComputation::Tuple(_)
                        | PureComputation::NewtypeConversion(_)
                        | PureComputation::TypeAbstraction(_)
                        | PureComputation::TypeApplication(_),
                    ),
                ) => {}
                None => {
                    self.charge_type_work(F::operation_extra_edge_count(&node.kind))?;
                    let mut result = Ok(());
                    F::visit_operation_binders(&node.kind, &mut |binder| {
                        if result.is_ok() {
                            result = self.collect_binder(
                                id,
                                binder,
                                ValidationReason::Pattern,
                                false,
                                false,
                            );
                        }
                    });
                    result?;
                }
            }
        }
        Ok(abstraction_owners)
    }

    fn collect_binder(
        &mut self,
        node: NodeId,
        binder: &'program TypedBinder,
        invalid_type: ValidationReason,
        allow_scheme: bool,
        authenticated_nested: bool,
    ) -> Result<(), ValidationError> {
        if binder.arena() != self.program.arena {
            return Err(ValidationError::new(ValidationReason::Scope, Some(node)));
        }
        self.validate_origin(binder.origin(), node)?;
        if let (Some(relation), Some(module)) = (&self.module_sources, binder.id().module())
            && relation.get(&module).copied() != Some(binder.origin().primary_span().source())
        {
            return Err(ValidationError::new(ValidationReason::Registry, Some(node)));
        }
        let type_valid = if authenticated_nested {
            true
        } else if allow_scheme {
            self.valid_type(Some(binder.ty()))?
        } else {
            self.valid_monotype(Some(binder.ty()))?
        };
        if !type_valid {
            return Err(ValidationError::new(invalid_type, Some(node)));
        }
        if self.binders.contains_key(&binder.id()) {
            return Err(ValidationError::new(ValidationReason::Scope, Some(node)));
        }
        self.binders
            .try_reserve(1)
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(node)))?;
        self.binders.insert(binder.id(), binder);
        Ok(())
    }

    fn collect_type_binders(
        &self,
        nominal_parameter_owners: &RegistryParameterOwners,
        abstraction_owners: &CoreAbstractionOwners,
    ) -> Result<CoreTypeBinders<'program>, ValidationError> {
        let mut definitions = HashMap::new();
        let mut consumed_rows = 0_usize;
        for (index, node) in self.program.nodes.iter().enumerate() {
            let Some(PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction))) =
                F::pure(&node.kind)
            else {
                continue;
            };
            let id = node_id(self.program.arena, index)?;
            let mut linked_identity_class = None;
            for (parameter, kind) in abstraction.parameters() {
                let parameter_is_resolved =
                    matches!(parameter, crate::types::TypeVariableId::Resolved { .. });
                if self.module_sources.is_some() {
                    self.charge_type_work(1)?;
                    if linked_identity_class
                        .replace(parameter_is_resolved)
                        .is_some_and(|class| class != parameter_is_resolved)
                    {
                        return Err(ValidationError::new(ValidationReason::Registry, Some(id)));
                    }
                } else if !parameter_is_resolved {
                    self.charge_type_work(1)?;
                }
                match parameter {
                    crate::types::TypeVariableId::Resolved { .. } => {
                        let Some(canonical) = self.program.registry.type_variable(*parameter)
                        else {
                            return Err(ValidationError::new(ValidationReason::Registry, Some(id)));
                        };
                        if nominal_parameter_owners.contains_key(parameter)
                            || !self.same_kind_charged(&canonical.kind, kind)?
                        {
                            return Err(ValidationError::new(ValidationReason::Registry, Some(id)));
                        }
                    }
                    crate::types::TypeVariableId::Generated(_) => {
                        self.charge_kind(kind)?;
                    }
                }
                if definitions.contains_key(parameter) {
                    return Err(ValidationError::new(
                        match parameter {
                            crate::types::TypeVariableId::Resolved { .. } => {
                                ValidationReason::Registry
                            }
                            crate::types::TypeVariableId::Generated(_) => {
                                ValidationReason::TypeOperation
                            }
                        },
                        Some(id),
                    ));
                }
                definitions
                    .try_reserve(1)
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?;
                definitions.insert(*parameter, (kind, id));
            }
            let linked_row = if linked_identity_class == Some(true) {
                let owner = abstraction_owners
                    .get(&id)
                    .ok_or_else(|| ValidationError::new(ValidationReason::Registry, Some(id)))?;
                let row = self
                    .program
                    .registry
                    .global_parameter_row(*owner)
                    .ok_or_else(|| ValidationError::new(ValidationReason::Registry, Some(id)))?;
                if row.parameters().len() != abstraction.parameters().len() {
                    return Err(ValidationError::new(ValidationReason::Registry, Some(id)));
                }
                Some((*owner, row))
            } else {
                None
            };
            if let Some((owner, row)) = linked_row {
                let source = node
                    .origin
                    .as_ref()
                    .expect("validated envelopes have origins")
                    .primary_span()
                    .source();
                let relation = self
                    .module_sources
                    .as_ref()
                    .expect("linked rows require a module relation");
                for ((actual, _), expected) in abstraction.parameters().iter().zip(row.parameters())
                {
                    self.charge_type_work(1)?;
                    if actual != expected
                        || actual.module() != owner.module()
                        || actual
                            .module()
                            .is_none_or(|module| relation.get(&module).copied() != Some(source))
                    {
                        return Err(ValidationError::new(ValidationReason::Registry, Some(id)));
                    }
                }
                self.charge_type_work(1)?;
                consumed_rows = consumed_rows
                    .checked_add(1)
                    .ok_or_else(|| ValidationError::new(ValidationReason::Resource, Some(id)))?;
            }
        }
        if self.module_sources.is_some()
            && consumed_rows != self.program.registry.global_parameter_rows().len()
        {
            return Err(ValidationError::new(ValidationReason::Registry, None));
        }
        Ok(definitions)
    }

    fn validate_node_types(
        &self,
        nominal_parameter_owners: &RegistryParameterOwners,
        type_binders: &CoreTypeBinders<'program>,
        authenticated_method_evidence: &HashSet<NodeId>,
    ) -> Result<(), ValidationError> {
        for (index, node) in self.program.nodes.iter().enumerate() {
            let id = node_id(self.program.arena, index)?;
            if !authenticated_method_evidence.contains(&id)
                && !matches!(
                    F::pure(&node.kind),
                    Some(PureExprKind::Computation(PureComputation::TypeAbstraction(
                        _
                    )))
                )
                && !self
                    .valid_core_type_kind(&node.ty, type_binders)
                    .map_err(|error| error.at_node(id))?
            {
                return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
            }
            match F::pure(&node.kind) {
                Some(PureExprKind::Value(value)) => self
                    .validate_value(id, node, value)
                    .map_err(|error| error.at_node(id))?,
                Some(PureExprKind::Variable(variable)) => {
                    let Some(binder) = self.binders.get(&variable.binder()) else {
                        return Err(ValidationError::new(ValidationReason::Scope, Some(id)));
                    };
                    if !self.same_type_charged(&node.ty, binder.ty())? {
                        return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                    }
                }
                Some(PureExprKind::Computation(computation)) => {
                    self.validate_computation(
                        id,
                        node,
                        computation,
                        type_binders,
                        nominal_parameter_owners,
                        authenticated_method_evidence.contains(&id),
                    )
                    .map_err(|error| error.at_node(id))?;
                }
                None => {}
            }
        }
        Ok(())
    }

    fn validate_value(
        &self,
        id: NodeId,
        node: &StoredNode<F>,
        value: &PureValue,
    ) -> Result<(), ValidationError> {
        let expected = match value {
            PureValue::Integer(integer) => integer.expected_type(),
            PureValue::Boolean(boolean) => boolean.expected_type(),
            PureValue::Unit(unit) => unit.expected_type(),
            PureValue::Function(function) => {
                let body = self.node(function.body())?;
                let Some(function_type) = node.ty.function_view() else {
                    return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                };
                let effects_match = match function_type.effects() {
                    Some(effects) => {
                        self.same_effect_row_charged(effects, F::effect_row(&body.effects), id)?
                    }
                    None => F::effect_row(&body.effects).is_empty(),
                };
                if (!F::ALLOWS_EFFECTFUL_TYPES && function_type.effects().is_some())
                    || !self.same_type_charged(function_type.domain(), function.parameter().ty())?
                    || !self.same_type_charged(function_type.value(), &body.ty)?
                    || !effects_match
                {
                    return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                }
                return Ok(());
            }
            PureValue::Constructor(constructor) => {
                let Some(info) = self.program.registry.constructor(constructor.constructor())
                else {
                    return Err(ValidationError::new(ValidationReason::Registry, Some(id)));
                };
                if self
                    .program
                    .registry
                    .nominal(info.owner)
                    .is_some_and(|owner| {
                        owner.declaration_kind
                            == crate::resolved::ResolvedNominalDeclarationKind::Newtype
                    })
                {
                    return Err(ValidationError::new(ValidationReason::Registry, Some(id)));
                }
                let parameters = self
                    .program
                    .registry
                    .nominal_parameters(info.owner)
                    .ok_or_else(|| ValidationError::new(ValidationReason::Registry, Some(id)))?;
                if !self.constructor_value_type_matches(&node.ty, info, parameters)? {
                    return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                }
                return Ok(());
            }
        };
        if !self.same_type_charged(&node.ty, &expected)? {
            return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
        }
        Ok(())
    }

    fn validate_computation(
        &self,
        id: NodeId,
        node: &StoredNode<F>,
        computation: &PureComputation,
        type_binders: &CoreTypeBinders<'program>,
        nominal_parameter_owners: &RegistryParameterOwners,
        authenticated_method_evidence: bool,
    ) -> Result<(), ValidationError> {
        match computation {
            PureComputation::Bind(binding) => {
                let initializer = self.node(binding.initializer())?;
                let body = self.node(binding.body())?;
                if !self.same_type_charged(&initializer.ty, binding.binder().ty())?
                    || !self.same_type_charged(&node.ty, &body.ty)?
                {
                    return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                }
            }
            PureComputation::RecursiveBind(group) => {
                if group.members().is_empty() {
                    return Err(ValidationError::new(
                        ValidationReason::RecursiveBinding,
                        Some(id),
                    ));
                }
                let recursive = group
                    .members()
                    .iter()
                    .map(|member| member.binder().id())
                    .collect::<HashSet<_>>();
                for member in group.members() {
                    let initializer = self.node(member.initializer())?;
                    let safe = match member.binder().ty() {
                        Type::Function(_, _) => matches!(
                            F::pure(&initializer.kind),
                            Some(PureExprKind::Value(PureValue::Function(_)))
                        ),
                        Type::EffectfulFunction(_, _) if F::ALLOWS_EFFECTFUL_TYPES => matches!(
                            F::pure(&initializer.kind),
                            Some(PureExprKind::Value(PureValue::Function(_)))
                        ),
                        ty if ty.outer_nominal().is_some() => match ty.outer_nominal() {
                            Some(owner) => {
                                self.guarded_data_root(member.initializer(), owner, &recursive)?
                            }
                            None => false,
                        },
                        Type::Forall(parameters, body)
                            if matches!(body.as_ref(), Type::Function(_, _))
                                || (F::ALLOWS_EFFECTFUL_TYPES
                                    && matches!(body.as_ref(), Type::EffectfulFunction(_, _))) =>
                        {
                            let Some(PureExprKind::Computation(PureComputation::TypeAbstraction(
                                abstraction,
                            ))) = F::pure(&initializer.kind)
                            else {
                                return Err(ValidationError::new(
                                    ValidationReason::RecursiveBinding,
                                    Some(id),
                                ));
                            };
                            self.same_kinded_parameters(
                                abstraction.parameters(),
                                parameters.as_ref(),
                            )? && matches!(
                                F::pure(&self.node(abstraction.body())?.kind),
                                Some(PureExprKind::Value(PureValue::Function(_)))
                            )
                        }
                        Type::Int
                        | Type::Bool
                        | Type::Unit
                        | Type::Tuple(_)
                        | Type::Nominal(_)
                        | Type::Application(_, _)
                        | Type::Variable(_)
                        | Type::Inference(_)
                        | Type::EffectfulFunction(_, _)
                        | Type::Forall(_, _) => false,
                    };
                    if !safe {
                        return Err(ValidationError::new(
                            ValidationReason::RecursiveBinding,
                            Some(id),
                        ));
                    }
                    if !self.same_type_charged(&initializer.ty, member.binder().ty())? {
                        return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                    }
                }
                let body = self.node(group.body())?;
                if !self.same_type_charged(&node.ty, &body.ty)? {
                    return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                }
            }
            PureComputation::Apply(application) => {
                let function = self.node(application.function())?;
                let argument = self.node(application.argument())?;
                let Some(function_type) = function.ty.function_view() else {
                    return Err(ValidationError::new(
                        ValidationReason::ApplicationType,
                        Some(id),
                    ));
                };
                if (!authenticated_method_evidence
                    && !self.same_type_charged(function_type.domain(), &argument.ty)?)
                    || !self.same_type_charged(function_type.value(), &node.ty)?
                {
                    return Err(ValidationError::new(
                        ValidationReason::ApplicationType,
                        Some(id),
                    ));
                }
            }
            PureComputation::Primitive(primitive) => {
                let left = self.node(primitive.left())?;
                let right = self.node(primitive.right())?;
                let (left_type, right_type, result_type) = primitive.primitive().signature();
                if !self.same_type_charged(&left.ty, &left_type)?
                    || !self.same_type_charged(&right.ty, &right_type)?
                    || !self.same_type_charged(&node.ty, &result_type)?
                {
                    return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                }
            }
            PureComputation::Tuple(tuple) => {
                let Type::Tuple(element_types) = &node.ty else {
                    return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                };
                if element_types.len() < 2 || element_types.len() != tuple.elements().len() {
                    return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                }
                for (element, expected) in tuple.elements().iter().zip(element_types) {
                    if !self.same_type_charged(&self.node(*element)?.ty, expected)? {
                        return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                    }
                }
            }
            PureComputation::Match(match_node) => {
                let scrutinee = self.node(match_node.scrutinee())?;
                if !self.valid_monotype(Some(&scrutinee.ty))? {
                    return Err(ValidationError::new(ValidationReason::Pattern, Some(id)));
                }
                if match_node.arms().is_empty() {
                    return Err(ValidationError::new(ValidationReason::Coverage, Some(id)));
                }
                let mut matrix = CorePatternMatrix(Vec::new());
                let mut coverage_budget = UsefulnessBudget::default();
                for arm in match_node.arms() {
                    self.validate_origin(arm.origin(), id)?;
                    self.validate_pattern(arm.pattern(), &scrutinee.ty, id)?;
                    if !self.same_type_charged(&self.node(arm.body())?.ty, &node.ty)? {
                        return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                    }
                    let row = CorePatternRow(vec![arm.pattern().clone()]);
                    if usefulness_with_budget(
                        &matrix.0,
                        &row.0,
                        std::slice::from_ref(&scrutinee.ty),
                        &self.program.registry,
                        &mut coverage_budget,
                    )
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?
                    .is_none()
                    {
                        return Err(ValidationError::new(ValidationReason::Coverage, Some(id)));
                    }
                    matrix.0.push(row.into_inner());
                }
                if missing_witness_for_types_with_budget(
                    &matrix.0,
                    std::slice::from_ref(&scrutinee.ty),
                    &self.program.registry,
                    &mut coverage_budget,
                )
                .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?
                .is_some()
                {
                    return Err(ValidationError::new(ValidationReason::Coverage, Some(id)));
                }
            }
            PureComputation::NewtypeConversion(conversion) => {
                if !self.valid_newtype_conversion(node, *conversion, type_binders)? {
                    return Err(ValidationError::new(
                        ValidationReason::NewtypeConversion,
                        Some(id),
                    ));
                }
            }
            PureComputation::TypeAbstraction(abstraction) => {
                let body = self.node(abstraction.body())?;
                let Type::Forall(parameters, scheme_body) = &node.ty else {
                    return Err(ValidationError::new(
                        ValidationReason::TypeOperation,
                        Some(id),
                    ));
                };
                self.charge_type_work(abstraction.parameters().len())?;
                if let Some(relation) = &self.module_sources {
                    let source = node
                        .origin
                        .as_ref()
                        .expect("validated envelopes have origins")
                        .primary_span()
                        .source();
                    if abstraction.parameters().iter().any(|parameter| {
                        parameter
                            .0
                            .module()
                            .is_some_and(|module| relation.get(&module).copied() != Some(source))
                    }) {
                        return Err(ValidationError::new(ValidationReason::Registry, Some(id)));
                    }
                }
                if abstraction.parameters().is_empty()
                    || abstraction.parameters().iter().any(|(parameter, _)| {
                        type_binders
                            .get(parameter)
                            .is_none_or(|(_, owner)| *owner != id)
                    })
                    || abstraction
                        .parameters()
                        .iter()
                        .any(|(parameter, _)| nominal_parameter_owners.contains_key(parameter))
                    || !self
                        .same_kinded_parameters(abstraction.parameters(), parameters.as_ref())?
                    || !self.same_type_charged(&body.ty, scheme_body)?
                    || (!authenticated_method_evidence
                        && (matches!(scheme_body.as_ref(), Type::Forall(_, _))
                            || !self.valid_core_type_kind(&node.ty, type_binders)?))
                {
                    return Err(ValidationError::new(
                        ValidationReason::TypeOperation,
                        Some(id),
                    ));
                }
            }
            PureComputation::TypeApplication(application) => {
                let invalid = || ValidationError::new(ValidationReason::TypeOperation, Some(id));
                let function = self.node(application.function())?;
                let Type::Forall(parameters, body) = &function.ty else {
                    return Err(invalid());
                };
                if parameters.len()
                    != application.arguments().len() + application.row_arguments().len()
                    || (!F::ALLOWS_EFFECTFUL_TYPES && !application.row_arguments().is_empty())
                {
                    return Err(invalid());
                }
                self.charge_type_work(parameters.len())?;
                let mut replacements = TypeReplacementMap::new();
                let mut row_replacements = HashMap::new();
                replacements
                    .try_reserve(application.arguments().len())
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?;
                row_replacements
                    .try_reserve(application.row_arguments().len())
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?;
                let mut ordinary = application.arguments().iter();
                let mut rows = application.row_arguments().iter();
                for (parameter, kind) in parameters.iter() {
                    if matches!(kind, Kind::EffectRow) {
                        let row = rows.next().ok_or_else(invalid)?;
                        row_replacements.insert(*parameter, self.clone_effect_row_charged(row)?);
                    } else {
                        let argument = ordinary.next().ok_or_else(invalid)?;
                        let argument_kind = self
                            .synthesize_monotype_kind(
                                argument,
                                MonotypeVariableKinds::Core(type_binders),
                            )?
                            .ok_or_else(invalid)?;
                        if !self.same_kind_charged(kind, &argument_kind)? {
                            return Err(invalid());
                        }
                        replacements
                            .insert_replacing(*parameter, self.clone_type_charged(argument)?);
                    }
                }
                let instantiated = substitute_type_and_row_variables_with(
                    body,
                    replacements.as_map(),
                    &row_replacements,
                    |cells| self.charge_type_work(cells),
                    || ValidationError::new(ValidationReason::Resource, None),
                )?
                .map_err(|_| invalid())?;
                let instantiated = IterativeTypeOwner::new(instantiated);
                if !self.same_type_charged(&node.ty, &instantiated)? {
                    return Err(invalid());
                }
            }
        }
        Ok(())
    }

    fn valid_newtype_conversion(
        &self,
        node: &StoredNode<F>,
        conversion: super::NewtypeConversionNode,
        type_binders: &CoreTypeBinders<'program>,
    ) -> Result<bool, ValidationError> {
        let Some(owner) = self.program.registry.nominal(conversion.owner()) else {
            return Ok(false);
        };
        if owner.declaration_kind != ResolvedNominalDeclarationKind::Newtype {
            return Ok(false);
        }
        let Some(representation) = owner.representation.as_ref() else {
            return Ok(false);
        };
        let Some(parameters) = self.program.registry.nominal_parameters(owner.id) else {
            return Ok(false);
        };
        let child = self.node(conversion.child())?;
        let (nominal, actual_representation) = match conversion.direction() {
            super::NewtypeConversionDirection::Wrap => (&node.ty, &child.ty),
            super::NewtypeConversionDirection::Unwrap => (&child.ty, &node.ty),
        };

        self.charge_type_work(parameters.len())?;
        #[cfg(test)]
        self.newtype_conversion_parameter_work
            .set(self.newtype_conversion_parameter_work.get() + parameters.len());
        let mut arguments = Vec::new();
        arguments
            .try_reserve(parameters.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        let spine_work = parameters
            .len()
            .checked_add(1)
            .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?;
        self.charge_type_work(spine_work)?;
        #[cfg(test)]
        self.newtype_conversion_parameter_work
            .set(self.newtype_conversion_parameter_work.get() + spine_work);
        let mut head = nominal;
        while let Type::Application(function, argument) = head {
            if arguments.len() == parameters.len() {
                return Ok(false);
            }
            arguments.push(argument.as_ref());
            head = function;
        }
        if head != &Type::Nominal(owner.id) || arguments.len() != parameters.len() {
            return Ok(false);
        }

        let mut replacements = TypeReplacementMap::new();
        self.charge_type_work(parameters.len())?;
        #[cfg(test)]
        self.newtype_conversion_parameter_work
            .set(self.newtype_conversion_parameter_work.get() + parameters.len());
        replacements
            .try_reserve(parameters.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        self.charge_type_work(parameters.len())?;
        #[cfg(test)]
        self.newtype_conversion_parameter_work
            .set(self.newtype_conversion_parameter_work.get() + parameters.len());
        for (parameter, argument) in parameters.iter().zip(arguments.into_iter().rev()) {
            let Some(argument_kind) =
                self.synthesize_monotype_kind(argument, MonotypeVariableKinds::Core(type_binders))?
            else {
                return Ok(false);
            };
            if !self.same_kind_charged(&parameter.kind, &argument_kind)? {
                return Ok(false);
            }
            replacements.insert_replacing(parameter.id, self.clone_type_charged(argument)?);
        }

        let expected = IterativeTypeOwner::new(substitute_type_variables_with(
            representation,
            replacements.as_map(),
            |cells| self.charge_type_work(cells),
            || ValidationError::new(ValidationReason::Resource, None),
        )?);
        self.same_type_charged(&expected, actual_representation)
    }

    fn guarded_data_root(
        &self,
        initializer: NodeId,
        owner: crate::types::NominalTypeId,
        recursive: &HashSet<BinderId>,
    ) -> Result<bool, ValidationError> {
        let initializer = self.erase_type_applications(initializer)?;
        let root = self.node(initializer)?;
        let payload = match F::pure(&root.kind) {
            Some(PureExprKind::Value(PureValue::Constructor(constructor))) => {
                let Some(info) = self.program.registry.constructor(constructor.constructor())
                else {
                    return Ok(false);
                };
                if info.owner != owner || info.payload.is_some() {
                    return Ok(false);
                }
                return Ok(true);
            }
            Some(PureExprKind::Computation(PureComputation::Apply(application))) => {
                let function = self.node(self.erase_type_applications(application.function())?)?;
                let Some(PureExprKind::Value(PureValue::Constructor(constructor))) =
                    F::pure(&function.kind)
                else {
                    return Ok(false);
                };
                let Some(info) = self.program.registry.constructor(constructor.constructor())
                else {
                    return Ok(false);
                };
                if info.owner != owner || info.payload.is_none() {
                    return Ok(false);
                }
                application.argument()
            }
            _ => return Ok(false),
        };
        self.guarded_payload(payload, recursive)
    }

    fn guarded_payload(
        &self,
        root: NodeId,
        recursive: &HashSet<BinderId>,
    ) -> Result<bool, ValidationError> {
        let reaches_recursive = self.recursive_reachability(root, recursive)?;
        let mut work = vec![root];
        while let Some(id) = work.pop() {
            if !reaches_recursive.get(&id).copied().unwrap_or(false) {
                continue;
            }
            let node = self.node(id)?;
            match F::pure(&node.kind) {
                Some(PureExprKind::Variable(variable))
                    if recursive.contains(&variable.binder()) => {}
                Some(PureExprKind::Computation(PureComputation::Tuple(tuple))) => {
                    work.extend(tuple.elements().iter().copied());
                }
                Some(PureExprKind::Computation(PureComputation::Apply(application))) => {
                    let function =
                        self.node(self.erase_type_applications(application.function())?)?;
                    if !matches!(
                        F::pure(&function.kind),
                        Some(PureExprKind::Value(PureValue::Constructor(_)))
                    ) {
                        return Ok(false);
                    }
                    work.push(application.argument());
                }
                Some(PureExprKind::Value(PureValue::Function(_))) => {}
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    fn erase_type_applications(&self, mut id: NodeId) -> Result<NodeId, ValidationError> {
        loop {
            let node = self.node(id)?;
            let Some(PureExprKind::Computation(PureComputation::TypeApplication(application))) =
                F::pure(&node.kind)
            else {
                return Ok(id);
            };
            id = application.function();
        }
    }

    fn recursive_reachability(
        &self,
        root: NodeId,
        recursive: &HashSet<BinderId>,
    ) -> Result<HashMap<NodeId, bool>, ValidationError> {
        enum Task {
            Visit(NodeId),
            Finish(NodeId),
        }

        let mut work = vec![Task::Visit(root)];
        let mut scheduled = HashSet::new();
        let mut result = HashMap::new();
        while let Some(task) = work.pop() {
            match task {
                Task::Visit(id) => {
                    if result.contains_key(&id) || !scheduled.insert(id) {
                        continue;
                    }
                    let node = self.node(id)?;
                    self.charge_type_work(F::operation_extra_edge_count(&node.kind))?;
                    let child_count = F::child_count(&node.kind);
                    work.try_reserve(child_count.checked_add(1).ok_or_else(|| {
                        ValidationError::new(ValidationReason::Resource, Some(id))
                    })?)
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?;
                    work.push(Task::Finish(id));
                    for index in 0..child_count {
                        work.push(Task::Visit(F::child_at(&node.kind, index).ok_or_else(
                            || ValidationError::new(ValidationReason::NodeBounds, Some(id)),
                        )?));
                    }
                }
                Task::Finish(id) => {
                    let node = self.node(id)?;
                    let direct = matches!(
                        F::pure(&node.kind),
                        Some(PureExprKind::Variable(variable))
                            if recursive.contains(&variable.binder())
                    );
                    let mut reaches = direct;
                    self.charge_type_work(F::operation_extra_edge_count(&node.kind))?;
                    for index in 0..F::child_count(&node.kind) {
                        let child = F::child_at(&node.kind, index).ok_or_else(|| {
                            ValidationError::new(ValidationReason::NodeBounds, Some(id))
                        })?;
                        reaches |= result.get(&child).copied().unwrap_or(false);
                    }
                    result.insert(id, reaches);
                }
            }
        }
        Ok(result)
    }

    fn validate_pattern(
        &self,
        pattern: &CorePattern,
        expected: &Type,
        node: NodeId,
    ) -> Result<(), ValidationError> {
        enum Expected<'a> {
            Borrowed(&'a Type),
            Owned(IterativeTypeOwner),
        }
        impl Expected<'_> {
            fn as_type(&self) -> &Type {
                match self {
                    Self::Borrowed(ty) => ty,
                    Self::Owned(ty) => ty,
                }
            }
        }
        enum Task<'a> {
            Visit(&'a CorePattern, Expected<'a>, usize),
            BorrowedTupleSequence {
                patterns: std::slice::Iter<'a, CorePattern>,
                types: std::slice::Iter<'a, Type>,
                depth: usize,
            },
            OwnedTupleSequence {
                patterns: std::slice::Iter<'a, CorePattern>,
                types: OwnedTypeSequence,
                depth: usize,
            },
        }
        let mut work = vec![Task::Visit(pattern, Expected::Borrowed(expected), 0)];
        let mut binders = HashSet::new();
        while let Some(task) = work.pop() {
            let (pattern, expected, depth) = match task {
                Task::Visit(pattern, expected, depth) => (pattern, expected, depth),
                Task::BorrowedTupleSequence {
                    mut patterns,
                    mut types,
                    depth,
                } => {
                    if let (Some(pattern), Some(ty)) = (patterns.next(), types.next()) {
                        work.push(Task::BorrowedTupleSequence {
                            patterns,
                            types,
                            depth,
                        });
                        work.push(Task::Visit(pattern, Expected::Borrowed(ty), depth));
                    }
                    continue;
                }
                Task::OwnedTupleSequence {
                    mut patterns,
                    mut types,
                    depth,
                } => {
                    if let (Some(pattern), Some(ty)) = (patterns.next(), types.next()) {
                        work.push(Task::OwnedTupleSequence {
                            patterns,
                            types,
                            depth,
                        });
                        work.push(Task::Visit(
                            pattern,
                            Expected::Owned(IterativeTypeOwner::new(ty)),
                            depth,
                        ));
                    }
                    continue;
                }
            };
            if depth > CORE_PATTERN_DEPTH_LIMIT {
                return Err(ValidationError::new(ValidationReason::Pattern, Some(node)));
            }
            self.validate_origin(&pattern.origin, node)?;
            if !self.same_type_charged(&pattern.ty, expected.as_type())?
                || !self.valid_monotype(Some(&pattern.ty))?
            {
                return Err(ValidationError::new(ValidationReason::Pattern, Some(node)));
            }
            match &pattern.kind {
                CorePatternKind::Binder(binder) => {
                    if binder.arena() != self.program.arena
                        || !self.same_type_charged(binder.ty(), expected.as_type())?
                        || !binders.insert(binder.id())
                    {
                        return Err(ValidationError::new(ValidationReason::Pattern, Some(node)));
                    }
                    self.validate_origin(binder.origin(), node)?;
                }
                CorePatternKind::Wildcard => {}
                CorePatternKind::Boolean(_) if matches!(expected.as_type(), Type::Bool) => {}
                CorePatternKind::Unit if matches!(expected.as_type(), Type::Unit) => {}
                CorePatternKind::Tuple(patterns) => match expected {
                    Expected::Borrowed(Type::Tuple(types)) if patterns.len() == types.len() => {
                        work.push(Task::BorrowedTupleSequence {
                            patterns: patterns.iter(),
                            types: types.iter(),
                            depth: depth.saturating_add(1),
                        });
                    }
                    Expected::Owned(expected) => {
                        let expected = expected.into_inner();
                        let Type::Tuple(types) = expected else {
                            discard_type_iteratively(expected);
                            return Err(ValidationError::new(
                                ValidationReason::Pattern,
                                Some(node),
                            ));
                        };
                        if patterns.len() != types.len() {
                            for ty in types {
                                discard_type_iteratively(ty);
                            }
                            return Err(ValidationError::new(
                                ValidationReason::Pattern,
                                Some(node),
                            ));
                        }
                        work.push(Task::OwnedTupleSequence {
                            patterns: patterns.iter(),
                            types: OwnedTypeSequence(types.into_vec().into_iter()),
                            depth: depth.saturating_add(1),
                        });
                    }
                    _ => {
                        return Err(ValidationError::new(ValidationReason::Pattern, Some(node)));
                    }
                },
                CorePatternKind::Constructor {
                    constructor,
                    payload,
                } => {
                    let Some((owner, arity)) =
                        self.nominal_application_head_and_arity(expected.as_type())?
                    else {
                        return Err(ValidationError::new(ValidationReason::Pattern, Some(node)));
                    };
                    let Some(info) = self.program.registry.constructor(*constructor) else {
                        return Err(ValidationError::new(ValidationReason::Pattern, Some(node)));
                    };
                    if self
                        .program
                        .registry
                        .nominal(info.owner)
                        .is_some_and(|owner| {
                            owner.declaration_kind
                                == crate::resolved::ResolvedNominalDeclarationKind::Newtype
                        })
                    {
                        return Err(ValidationError::new(ValidationReason::Pattern, Some(node)));
                    }
                    if info.owner != owner {
                        return Err(ValidationError::new(ValidationReason::Pattern, Some(node)));
                    }
                    let Some(parameters) = self.program.registry.nominal_parameters(owner) else {
                        return Err(ValidationError::new(ValidationReason::Pattern, Some(node)));
                    };
                    if parameters.len() != arity {
                        return Err(ValidationError::new(ValidationReason::Pattern, Some(node)));
                    }
                    let payload_type = if let Some(payload) = info.payload.as_ref() {
                        self.charge_type_work(parameters.len())?;
                        let mut replacements = TypeReplacementMap::new();
                        replacements.try_reserve(parameters.len()).map_err(|_| {
                            ValidationError::new(ValidationReason::Resource, Some(node))
                        })?;
                        let mut current = expected.as_type();
                        for parameter in parameters.iter().rev() {
                            let Type::Application(function, argument) = current else {
                                return Err(ValidationError::new(
                                    ValidationReason::Pattern,
                                    Some(node),
                                ));
                            };
                            self.charge_type_structure(argument)?;
                            replacements.insert_replacing(parameter.id, argument.as_ref().clone());
                            current = function;
                        }
                        Some(IterativeTypeOwner::new(substitute_type_variables_with(
                            payload,
                            replacements.as_map(),
                            |cells| self.charge_type_work(cells),
                            || ValidationError::new(ValidationReason::Resource, None),
                        )?))
                    } else {
                        None
                    };
                    match (payload_type, payload.as_deref()) {
                        (None, None) => {}
                        (Some(payload_type), Some(payload_pattern)) => work.push(Task::Visit(
                            payload_pattern,
                            Expected::Owned(payload_type),
                            depth.saturating_add(1),
                        )),
                        _ => {
                            return Err(ValidationError::new(
                                ValidationReason::Pattern,
                                Some(node),
                            ));
                        }
                    }
                }
                CorePatternKind::Boolean(_) | CorePatternKind::Unit => {
                    return Err(ValidationError::new(ValidationReason::Pattern, Some(node)));
                }
            }
        }
        Ok(())
    }

    fn validate_scopes(&self) -> Result<(), ValidationError> {
        let analysis = self.analyze_free_binders()?;
        if analysis.analyzed_nodes != self.program.nodes.len() {
            return Err(ValidationError::new(ValidationReason::Scope, None));
        }
        if let Some((key, requirement)) = analysis
            .root_requirements
            .iter()
            .min_by_key(|(_, requirement)| requirement.occurrence.value())
        {
            return Err(ValidationError::new(
                if matches!(key, ScopeRequirementKey::Resume(_, _)) {
                    ValidationReason::Resume
                } else {
                    ValidationReason::Scope
                },
                Some(requirement.occurrence),
            ));
        }
        Ok(())
    }

    fn validate_type_scopes(&self) -> Result<(), ValidationError> {
        let mut scheduled = vec![false; self.program.nodes.len()];
        let mut requirements = vec![None; self.program.nodes.len()];
        let mut remaining_uses = vec![0_usize; self.program.nodes.len()];
        for (index, node) in self.program.nodes.iter().enumerate() {
            let id = node_id(self.program.arena, index)?;
            self.charge_type_work(F::operation_extra_edge_count(&node.kind))?;
            for child_index in 0..F::child_count(&node.kind) {
                let child = F::child_at(&node.kind, child_index)
                    .ok_or_else(|| ValidationError::new(ValidationReason::TypeScope, Some(id)))?;
                let child_index = self.index(child)?;
                remaining_uses[child_index] = remaining_uses[child_index]
                    .checked_add(1)
                    .ok_or_else(|| ValidationError::new(ValidationReason::Resource, Some(id)))?;
            }
        }
        let mut work = vec![ScopeAnalysisTask::Enter(self.program.root)];
        while let Some(task) = work.pop() {
            match task {
                ScopeAnalysisTask::Enter(id) => {
                    let index = self.index(id)?;
                    if scheduled[index] {
                        continue;
                    }
                    scheduled[index] = true;
                    let kind = &self.node(id)?.kind;
                    self.charge_type_work(F::operation_extra_edge_count(kind))?;
                    let child_count = F::child_count(kind);
                    work.try_reserve(child_count.checked_add(1).ok_or_else(|| {
                        ValidationError::new(ValidationReason::Resource, Some(id))
                    })?)
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?;
                    work.push(ScopeAnalysisTask::Finish(id));
                    for child_index in (0..child_count).rev() {
                        let child = F::child_at(kind, child_index).ok_or_else(|| {
                            ValidationError::new(ValidationReason::TypeScope, Some(id))
                        })?;
                        work.push(ScopeAnalysisTask::Enter(child));
                    }
                }
                ScopeAnalysisTask::Finish(id) => {
                    let node = self.node(id)?;
                    let mut free = HashSet::new();
                    self.charge_type_structure(&node.ty)?;
                    self.collect_free_type_variables(&node.ty, &mut free)?;
                    self.collect_effect_row_type_variables(
                        F::effect_row(&node.effects),
                        &mut free,
                    )?;
                    self.charge_type_work(F::operation_extra_edge_count(&node.kind))?;
                    for child_index in 0..F::child_count(&node.kind) {
                        let child = F::child_at(&node.kind, child_index).ok_or_else(|| {
                            ValidationError::new(ValidationReason::TypeScope, Some(id))
                        })?;
                        let child_free = self.take_type_scope_requirements(
                            &mut requirements,
                            &mut remaining_uses,
                            child,
                            id,
                        )?;
                        self.merge_type_scope_requirements(&mut free, child_free)?;
                    }
                    match F::pure(&node.kind) {
                        Some(PureExprKind::Value(PureValue::Function(function))) => {
                            self.charge_type_structure(function.parameter().ty())?;
                            self.collect_free_type_variables(function.parameter().ty(), &mut free)?;
                        }
                        Some(PureExprKind::Computation(PureComputation::Bind(binding))) => {
                            self.charge_type_structure(binding.binder().ty())?;
                            self.collect_free_type_variables(binding.binder().ty(), &mut free)?;
                        }
                        Some(PureExprKind::Computation(PureComputation::RecursiveBind(group))) => {
                            for member in group.members() {
                                self.charge_type_structure(member.binder().ty())?;
                                self.collect_free_type_variables(member.binder().ty(), &mut free)?;
                            }
                        }
                        Some(PureExprKind::Computation(PureComputation::Match(match_node))) => {
                            for arm in match_node.arms() {
                                self.charge_pattern_type_structure(arm.pattern())?;
                                self.collect_pattern_type_variables(arm.pattern(), &mut free)?;
                            }
                        }
                        Some(PureExprKind::Computation(PureComputation::TypeApplication(
                            operation,
                        ))) => {
                            for argument in operation.arguments() {
                                self.charge_type_structure(argument)?;
                                self.collect_free_type_variables(argument, &mut free)?;
                            }
                            for row in operation.row_arguments() {
                                self.collect_effect_row_type_variables(row, &mut free)?;
                            }
                        }
                        Some(PureExprKind::Computation(PureComputation::TypeAbstraction(
                            operation,
                        ))) => {
                            for (parameter, _) in operation.parameters() {
                                free.remove(parameter);
                            }
                        }
                        Some(
                            PureExprKind::Value(
                                PureValue::Integer(_)
                                | PureValue::Boolean(_)
                                | PureValue::Unit(_)
                                | PureValue::Constructor(_),
                            )
                            | PureExprKind::Variable(_)
                            | PureExprKind::Computation(
                                PureComputation::Apply(_)
                                | PureComputation::Primitive(_)
                                | PureComputation::Tuple(_)
                                | PureComputation::NewtypeConversion(_),
                            ),
                        ) => {}
                        None => {}
                    }
                    let mut metadata_error = None;
                    F::visit_operation_type_metadata(&node.kind, &mut |metadata| {
                        if metadata_error.is_some() {
                            return;
                        }
                        metadata_error = match metadata {
                            super::dialect::OperationTypeMetadata::Type(ty) => self
                                .charge_type_structure(ty)
                                .and_then(|()| self.collect_free_type_variables(ty, &mut free))
                                .err(),
                            super::dialect::OperationTypeMetadata::Pattern(pattern) => self
                                .charge_pattern_type_structure(pattern)
                                .and_then(|()| {
                                    self.collect_pattern_type_variables(pattern, &mut free)
                                })
                                .err(),
                        };
                    });
                    if let Some(error) = metadata_error {
                        return Err(error);
                    }
                    requirements[self.index(id)?] = Some(free);
                }
            }
        }
        let root = requirements
            .get(self.index(self.program.root)?)
            .and_then(Option::as_ref)
            .ok_or_else(|| ValidationError::new(ValidationReason::TypeScope, None))?;
        if root.is_empty() {
            Ok(())
        } else {
            Err(ValidationError::new(
                ValidationReason::TypeScope,
                Some(self.program.root),
            ))
        }
    }

    fn take_type_scope_requirements(
        &self,
        requirements: &mut [Option<HashSet<crate::types::TypeVariableId>>],
        remaining_uses: &mut [usize],
        child: NodeId,
        parent: NodeId,
    ) -> Result<HashSet<crate::types::TypeVariableId>, ValidationError> {
        let child_index = self.index(child)?;
        let remaining = remaining_uses
            .get_mut(child_index)
            .ok_or_else(|| ValidationError::new(ValidationReason::TypeScope, Some(parent)))?;
        *remaining = remaining
            .checked_sub(1)
            .ok_or_else(|| ValidationError::new(ValidationReason::TypeScope, Some(parent)))?;
        let requirement = requirements
            .get_mut(child_index)
            .ok_or_else(|| ValidationError::new(ValidationReason::TypeScope, Some(parent)))?;
        if *remaining == 0 {
            return requirement
                .take()
                .ok_or_else(|| ValidationError::new(ValidationReason::TypeScope, Some(parent)));
        }
        let requirement = requirement
            .as_ref()
            .ok_or_else(|| ValidationError::new(ValidationReason::TypeScope, Some(parent)))?;
        self.charge_type_work(requirement.len())?;
        let mut cloned = HashSet::new();
        cloned
            .try_reserve(requirement.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(parent)))?;
        cloned.extend(requirement.iter().copied());
        Ok(cloned)
    }

    fn merge_type_scope_requirements(
        &self,
        target: &mut HashSet<crate::types::TypeVariableId>,
        mut incoming: HashSet<crate::types::TypeVariableId>,
    ) -> Result<(), ValidationError> {
        if target.is_empty() {
            *target = incoming;
            return Ok(());
        }
        if target.len() < incoming.len() {
            std::mem::swap(target, &mut incoming);
        }
        for variable in incoming {
            self.retain_type_scope_requirement(target, variable)?;
        }
        Ok(())
    }

    fn retain_type_scope_requirement(
        &self,
        output: &mut HashSet<crate::types::TypeVariableId>,
        variable: crate::types::TypeVariableId,
    ) -> Result<(), ValidationError> {
        if output.contains(&variable) {
            return Ok(());
        }
        self.charge_type_work(1)?;
        output
            .try_reserve(1)
            .map_err(|_| ValidationError::new(ValidationReason::Resource, None))?;
        output.insert(variable);
        Ok(())
    }

    fn collect_free_type_variables(
        &self,
        ty: &Type,
        output: &mut HashSet<crate::types::TypeVariableId>,
    ) -> Result<(), ValidationError> {
        enum Task<'a> {
            Visit(&'a Type),
            Sequence(std::slice::Iter<'a, Type>),
        }

        let mut discovered = HashSet::new();
        let mut quantified = Vec::new();
        let mut work = vec![Task::Visit(ty)];
        while let Some(task) = work.pop() {
            match task {
                Task::Visit(Type::Variable(variable)) => {
                    self.retain_type_scope_requirement(&mut discovered, *variable)?;
                }
                Task::Visit(Type::Tuple(elements)) => {
                    work.push(Task::Sequence(elements.iter()));
                }
                Task::Visit(Type::Application(function, argument)) => {
                    work.push(Task::Visit(argument));
                    work.push(Task::Visit(function));
                }
                Task::Visit(Type::Function(domain, codomain)) => {
                    work.push(Task::Visit(codomain));
                    work.push(Task::Visit(domain));
                }
                Task::Visit(Type::EffectfulFunction(domain, codomain)) => {
                    self.collect_effect_row_type_variables(codomain.effects(), &mut discovered)?;
                    work.push(Task::Visit(codomain.value()));
                    work.push(Task::Visit(domain));
                }
                Task::Visit(Type::Forall(parameters, body)) => {
                    quantified.push(parameters.as_ref());
                    work.push(Task::Visit(body));
                }
                Task::Visit(
                    Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) | Type::Inference(_),
                ) => {}
                Task::Sequence(mut remaining) => {
                    if let Some(ty) = remaining.next() {
                        work.push(Task::Sequence(remaining));
                        work.push(Task::Visit(ty));
                    }
                }
            }
        }
        for parameters in quantified {
            for (parameter, _) in parameters {
                discovered.remove(parameter);
            }
        }
        self.merge_type_scope_requirements(output, discovered)
    }

    fn collect_effect_row_type_variables(
        &self,
        row: &EffectRow,
        output: &mut HashSet<crate::types::TypeVariableId>,
    ) -> Result<(), ValidationError> {
        self.charge_type_work(
            row.known()
                .len()
                .saturating_add(usize::from(row.tail().is_some())),
        )?;
        for instance in row.known() {
            for argument in instance.arguments() {
                self.charge_type_structure(argument)?;
                self.collect_free_type_variables(argument, output)?;
            }
        }
        if let Some(tail) = row.tail() {
            if let crate::types::EffectRowVariable::Rigid(variable) = tail.variable() {
                self.retain_type_scope_requirement(output, variable)?;
            }
            self.charge_type_work(tail.lacks().len())?;
            for instance in tail.lacks() {
                for argument in instance.arguments() {
                    self.charge_type_structure(argument)?;
                    self.collect_free_type_variables(argument, output)?;
                }
            }
        }
        Ok(())
    }

    fn collect_pattern_type_variables(
        &self,
        pattern: &CorePattern,
        output: &mut HashSet<crate::types::TypeVariableId>,
    ) -> Result<(), ValidationError> {
        enum Task<'a> {
            Visit(&'a CorePattern),
            Sequence(std::slice::Iter<'a, CorePattern>),
        }
        let mut work = vec![Task::Visit(pattern)];
        while let Some(task) = work.pop() {
            let Task::Visit(pattern) = task else {
                let Task::Sequence(mut remaining) = task else {
                    unreachable!()
                };
                if let Some(pattern) = remaining.next() {
                    work.push(Task::Sequence(remaining));
                    work.push(Task::Visit(pattern));
                }
                continue;
            };
            self.collect_free_type_variables(&pattern.ty, output)?;
            match &pattern.kind {
                CorePatternKind::Binder(binder) => {
                    self.collect_free_type_variables(binder.ty(), output)?;
                }
                CorePatternKind::Tuple(elements) => work.push(Task::Sequence(elements.iter())),
                CorePatternKind::Constructor { payload, .. } => {
                    if let Some(payload) = payload.as_deref() {
                        work.push(Task::Visit(payload));
                    }
                }
                CorePatternKind::Wildcard | CorePatternKind::Boolean(_) | CorePatternKind::Unit => {
                }
            }
        }
        Ok(())
    }

    fn analyze_free_binders(&self) -> Result<ScopeAnalysis, ValidationError> {
        let mut scheduled = vec![false; self.program.nodes.len()];
        let mut requirements = vec![None; self.program.nodes.len()];
        let mut work = vec![ScopeAnalysisTask::Enter(self.program.root)];
        let mut analyzed_nodes = 0;

        while let Some(task) = work.pop() {
            match task {
                ScopeAnalysisTask::Enter(id) => {
                    let index = self.index(id)?;
                    if scheduled[index] {
                        continue;
                    }
                    scheduled[index] = true;
                    let kind = &self.node(id)?.kind;
                    self.charge_type_work(F::operation_extra_edge_count(kind))?;
                    let child_count = F::child_count(kind);
                    work.try_reserve(child_count.checked_add(1).ok_or_else(|| {
                        ValidationError::new(ValidationReason::Resource, Some(id))
                    })?)
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?;
                    work.push(ScopeAnalysisTask::Finish(id));
                    for child_index in (0..child_count).rev() {
                        let child = F::child_at(kind, child_index).ok_or_else(|| {
                            ValidationError::new(ValidationReason::Scope, Some(id))
                        })?;
                        work.push(ScopeAnalysisTask::Enter(child));
                    }
                }
                ScopeAnalysisTask::Finish(id) => {
                    let node = self.node(id)?;
                    let free = match F::pure(&node.kind) {
                        Some(PureExprKind::Variable(variable)) => HashMap::from([(
                            ScopeRequirementKey::Binder(variable.binder()),
                            ScopeRequirement {
                                occurrence: id,
                                paths: 0,
                            },
                        )]),
                        Some(PureExprKind::Value(PureValue::Function(function))) => {
                            let mut body = self.requirements_for(&requirements, function.body())?;
                            self.reject_resume_capture(&body, id)?;
                            body.remove(&ScopeRequirementKey::Binder(function.parameter().id()));
                            body
                        }
                        Some(PureExprKind::Computation(PureComputation::Bind(binding))) => {
                            let initializer =
                                self.requirements_for(&requirements, binding.initializer())?;
                            let mut body = self.requirements_for(&requirements, binding.body())?;
                            body.remove(&ScopeRequirementKey::Binder(binding.binder().id()));
                            self.union_scope_requirements(initializer, body, id)?
                        }
                        Some(PureExprKind::Computation(PureComputation::RecursiveBind(group))) => {
                            let mut free = self.requirements_for(&requirements, group.body())?;
                            for member in group.members() {
                                let initializer =
                                    self.requirements_for(&requirements, member.initializer())?;
                                self.reject_resume_capture(&initializer, id)?;
                                free = self.union_scope_requirements(free, initializer, id)?;
                            }
                            for member in group.members() {
                                free.remove(&ScopeRequirementKey::Binder(member.binder().id()));
                            }
                            free
                        }
                        Some(PureExprKind::Computation(PureComputation::Apply(application))) => {
                            let function =
                                self.requirements_for(&requirements, application.function())?;
                            let argument =
                                self.requirements_for(&requirements, application.argument())?;
                            self.union_scope_requirements(function, argument, id)?
                        }
                        Some(PureExprKind::Computation(PureComputation::Primitive(primitive))) => {
                            let left = self.requirements_for(&requirements, primitive.left())?;
                            let right = self.requirements_for(&requirements, primitive.right())?;
                            self.union_scope_requirements(left, right, id)?
                        }
                        Some(PureExprKind::Computation(PureComputation::Tuple(tuple))) => {
                            let mut free = HashMap::new();
                            for element in tuple.elements() {
                                free = self.union_scope_requirements(
                                    free,
                                    self.requirements_for(&requirements, *element)?,
                                    id,
                                )?;
                            }
                            free
                        }
                        Some(PureExprKind::Computation(PureComputation::Match(match_node))) => {
                            let mut free =
                                self.requirements_for(&requirements, match_node.scrutinee())?;
                            let mut branch_resumes: Option<ScopeRequirements> = None;
                            for arm in match_node.arms() {
                                let mut arm_free =
                                    self.requirements_for(&requirements, arm.body())?;
                                for binder in arm.pattern().binder_iter() {
                                    arm_free.remove(&ScopeRequirementKey::Binder(binder.id()));
                                }
                                arm_free.retain(|key, requirement| match key {
                                    ScopeRequirementKey::Binder(_) => {
                                        free.entry(*key).or_insert(*requirement);
                                        false
                                    }
                                    ScopeRequirementKey::Resume(_, _) => true,
                                });
                                if let Some(expected) = &branch_resumes {
                                    if expected.len() != arm_free.len()
                                        || expected.iter().any(|(key, requirement)| {
                                            arm_free.get(key).is_none_or(|actual| {
                                                actual.paths != requirement.paths
                                            })
                                        })
                                    {
                                        return Err(ValidationError::new(
                                            ValidationReason::Resume,
                                            Some(id),
                                        ));
                                    }
                                } else {
                                    branch_resumes = Some(arm_free);
                                }
                            }
                            if let Some(resumes) = branch_resumes {
                                free = self.union_scope_requirements(free, resumes, id)?;
                            }
                            free
                        }
                        Some(PureExprKind::Computation(PureComputation::TypeAbstraction(
                            operation,
                        ))) => {
                            let body = self.requirements_for(&requirements, operation.body())?;
                            self.reject_resume_capture(&body, id)?;
                            body
                        }
                        Some(PureExprKind::Computation(PureComputation::NewtypeConversion(
                            operation,
                        ))) => self.requirements_for(&requirements, operation.child())?,
                        Some(PureExprKind::Computation(PureComputation::TypeApplication(
                            operation,
                        ))) => self.requirements_for(&requirements, operation.function())?,
                        Some(PureExprKind::Value(
                            PureValue::Integer(_)
                            | PureValue::Boolean(_)
                            | PureValue::Unit(_)
                            | PureValue::Constructor(_),
                        )) => HashMap::new(),
                        None => {
                            let mut free = HashMap::new();
                            self.charge_type_work(F::operation_extra_edge_count(&node.kind))?;
                            for child_index in 0..F::child_count(&node.kind) {
                                let child =
                                    F::child_at(&node.kind, child_index).ok_or_else(|| {
                                        ValidationError::new(ValidationReason::Scope, Some(id))
                                    })?;
                                let mut child_free = self.requirements_for(&requirements, child)?;
                                F::visit_operation_child_binders(
                                    &node.kind,
                                    child_index,
                                    &mut |binder| {
                                        child_free.remove(&ScopeRequirementKey::Binder(binder));
                                    },
                                );
                                if let Some((handler, owner)) =
                                    F::clause_capability(&node.kind, child_index)
                                {
                                    let capability = child_free
                                        .remove(&ScopeRequirementKey::Resume(handler, owner));
                                    if capability.is_none_or(|capability| capability.paths != 1)
                                        || child_free.keys().any(|key| {
                                            matches!(key, ScopeRequirementKey::Resume(_, _))
                                        })
                                    {
                                        return Err(ValidationError::new(
                                            ValidationReason::Resume,
                                            Some(child),
                                        ));
                                    }
                                }
                                free = self.union_scope_requirements(free, child_free, id)?;
                            }
                            if let Some((handler, owner)) = F::resume_capability(&node.kind) {
                                self.retain_resume_requirement(&mut free, handler, owner, id, 1)?;
                            }
                            free
                        }
                    };
                    let index = self.index(id)?;
                    requirements[index] = Some(free);
                    analyzed_nodes += 1;
                }
            }
        }

        let root_index = self.index(self.program.root)?;
        let Some(root_requirements) = requirements[root_index].take() else {
            return Err(ValidationError::new(ValidationReason::Scope, None));
        };
        Ok(ScopeAnalysis {
            root_requirements,
            analyzed_nodes,
        })
    }

    fn requirements_for(
        &self,
        requirements: &[Option<ScopeRequirements>],
        id: NodeId,
    ) -> Result<ScopeRequirements, ValidationError> {
        let index = self.index(id)?;
        let Some(free) = requirements.get(index).and_then(Option::as_ref) else {
            return Err(ValidationError::new(ValidationReason::Scope, Some(id)));
        };
        let resume_count = free
            .keys()
            .filter(|key| matches!(key, ScopeRequirementKey::Resume(_, _)))
            .count();
        self.charge_type_work(resume_count)?;
        let mut cloned = HashMap::new();
        cloned
            .try_reserve(free.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?;
        cloned.extend(free.iter().map(|(key, requirement)| (*key, *requirement)));
        Ok(cloned)
    }

    fn reject_resume_capture(
        &self,
        requirements: &ScopeRequirements,
        owner: NodeId,
    ) -> Result<(), ValidationError> {
        if requirements
            .keys()
            .any(|key| matches!(key, ScopeRequirementKey::Resume(_, _)))
        {
            Err(ValidationError::new(ValidationReason::Resume, Some(owner)))
        } else {
            Ok(())
        }
    }

    fn retain_resume_requirement(
        &self,
        requirements: &mut ScopeRequirements,
        handler: super::effect::HandlerId,
        owner: crate::resolved::ResumeId,
        occurrence: NodeId,
        paths: u8,
    ) -> Result<(), ValidationError> {
        let key = ScopeRequirementKey::Resume(handler, owner);
        if let Some(current) = requirements.get_mut(&key) {
            current.paths = current.paths.saturating_add(paths).min(2);
            return Ok(());
        }
        self.charge_type_work(1)?;
        requirements
            .try_reserve(1)
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(occurrence)))?;
        requirements.insert(key, ScopeRequirement { occurrence, paths });
        Ok(())
    }

    fn union_scope_requirements(
        &self,
        mut left: ScopeRequirements,
        right: ScopeRequirements,
        _owner: NodeId,
    ) -> Result<ScopeRequirements, ValidationError> {
        for (key, requirement) in right {
            match key {
                ScopeRequirementKey::Binder(_) => {
                    left.entry(key).or_insert(requirement);
                }
                ScopeRequirementKey::Resume(handler, resume) => self.retain_resume_requirement(
                    &mut left,
                    handler,
                    resume,
                    requirement.occurrence,
                    requirement.paths,
                )?,
            }
        }
        Ok(left)
    }

    fn index(&self, id: NodeId) -> Result<usize, ValidationError> {
        if id.arena() != self.program.arena {
            return Err(ValidationError::new(ValidationReason::NodeBounds, Some(id)));
        }
        usize::try_from(id.value())
            .ok()
            .filter(|index| *index < self.program.nodes.len())
            .ok_or_else(|| ValidationError::new(ValidationReason::NodeBounds, Some(id)))
    }

    fn node(&self, id: NodeId) -> Result<&'program StoredNode<F>, ValidationError> {
        let index = self.index(id)?;
        self.program
            .nodes
            .get(index)
            .ok_or_else(|| ValidationError::new(ValidationReason::NodeBounds, Some(id)))
    }

    fn pure_kind(&self, id: NodeId) -> Result<&'program PureExprKind, ValidationError> {
        F::pure(&self.node(id)?.kind)
            .ok_or_else(|| ValidationError::new(ValidationReason::NodeType, Some(id)))
    }
}

#[derive(Clone, Copy)]
struct EffectClauseContract {
    handler: NodeId,
    clause: usize,
}

impl<'program, 'source> Validator<'program, 'source, super::effect::EffectOperationFamily> {
    fn run_effect(&mut self) -> Result<(), ValidationError> {
        let mut nominal_parameter_owners = self.validate_registry()?;
        self.validate_effect_registry(self.module_sources.as_ref(), &mut nominal_parameter_owners)?;
        let empty_type_binders = CoreTypeBinders::new();
        for nominal in self.program.registry.nominals() {
            if let Some(representation) = nominal.representation.as_ref() {
                self.validate_effect_type_rows(
                    representation,
                    &empty_type_binders,
                    self.program.root,
                )?;
            }
        }
        for constructor in self.program.registry.constructors() {
            if let Some(payload) = constructor.payload.as_ref() {
                self.validate_effect_type_rows(payload, &empty_type_binders, self.program.root)?;
            }
        }
        for effect in self.program.registry.effects() {
            for operation in &effect.operations {
                self.validate_effect_type_rows(
                    &operation.annotation.ty,
                    &empty_type_binders,
                    self.program.root,
                )?;
            }
        }
        let authenticated_method_evidence = self.validate_method_evidence_authority()?;
        self.validate_envelopes(&authenticated_method_evidence)?;
        self.validate_graph()?;
        let abstraction_owners = self.collect_binders(&authenticated_method_evidence)?;
        let type_binders =
            self.collect_type_binders(&nominal_parameter_owners, &abstraction_owners)?;
        self.validate_method_evidence_type_owners(&type_binders)?;
        self.validate_node_types(
            &nominal_parameter_owners,
            &type_binders,
            &authenticated_method_evidence,
        )?;
        self.validate_effect_nodes(&type_binders)?;
        self.validate_scopes()?;
        self.validate_type_scopes()
    }

    fn effect_signature(
        &self,
        instance: &EffectInstance,
        operation: OperationId,
        node: NodeId,
        type_binders: &CoreTypeBinders<'_>,
    ) -> Result<(IterativeTypeOwner, IterativeTypeOwner), ValidationError> {
        let declaration = self
            .program
            .registry
            .effect(instance.effect())
            .ok_or_else(|| ValidationError::new(ValidationReason::EffectIdentity, Some(node)))?;
        if operation.owner() != declaration.id
            || declaration.parameters.len() != instance.arguments().len()
        {
            return Err(ValidationError::new(
                ValidationReason::EffectIdentity,
                Some(node),
            ));
        }
        for (parameter, argument) in declaration.parameters.iter().zip(instance.arguments()) {
            let Some(argument_kind) =
                self.synthesize_monotype_kind(argument, MonotypeVariableKinds::Core(type_binders))?
            else {
                return Err(ValidationError::new(
                    ValidationReason::EffectIdentity,
                    Some(node),
                ));
            };
            if !self.same_kind_charged(&parameter.kind, &argument_kind)? {
                return Err(ValidationError::new(
                    ValidationReason::EffectIdentity,
                    Some(node),
                ));
            }
        }
        let Some(operation) = usize::try_from(operation.operation())
            .ok()
            .and_then(|index| declaration.operations.get(index))
            .filter(|candidate| candidate.id == operation)
        else {
            return Err(ValidationError::new(
                ValidationReason::EffectIdentity,
                Some(node),
            ));
        };
        let mut replacements = TypeReplacementMap::new();
        replacements
            .try_reserve(declaration.parameters.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(node)))?;
        for (parameter, argument) in declaration.parameters.iter().zip(instance.arguments()) {
            replacements.insert_replacing(parameter.id, self.clone_type_charged(argument)?);
        }
        let signature = substitute_type_variables_with(
            &operation.annotation.ty,
            replacements.as_map(),
            |cells| self.charge_type_work(cells),
            || ValidationError::new(ValidationReason::Resource, Some(node)),
        )?;
        let Type::Function(domain, result) = signature else {
            discard_type_iteratively(signature);
            return Err(ValidationError::new(
                ValidationReason::EffectIdentity,
                Some(node),
            ));
        };
        Ok((
            IterativeTypeOwner::new(*domain),
            IterativeTypeOwner::new(*result),
        ))
    }

    fn validate_effect_instance(
        &self,
        instance: &EffectInstance,
        type_binders: &CoreTypeBinders<'_>,
        node: NodeId,
    ) -> Result<(), ValidationError> {
        let declaration = self
            .program
            .registry
            .effect(instance.effect())
            .ok_or_else(|| ValidationError::new(ValidationReason::EffectIdentity, Some(node)))?;
        if declaration.parameters.len() != instance.arguments().len() {
            return Err(ValidationError::new(
                ValidationReason::EffectIdentity,
                Some(node),
            ));
        }
        for (parameter, argument) in declaration.parameters.iter().zip(instance.arguments()) {
            let Some(actual) =
                self.synthesize_monotype_kind(argument, MonotypeVariableKinds::Core(type_binders))?
            else {
                return Err(ValidationError::new(
                    ValidationReason::EffectIdentity,
                    Some(node),
                ));
            };
            if !self.same_kind_charged(&parameter.kind, &actual)? {
                return Err(ValidationError::new(
                    ValidationReason::EffectIdentity,
                    Some(node),
                ));
            }
        }
        Ok(())
    }

    fn validate_effect_row(
        &self,
        row: &EffectRow,
        type_binders: &CoreTypeBinders<'_>,
        node: NodeId,
    ) -> Result<(), ValidationError> {
        self.charge_type_work(row.known().len())?;
        for instance in row.known() {
            self.validate_effect_instance(instance, type_binders, node)?;
        }
        if let Some(tail) = row.tail() {
            self.charge_type_work(tail.lacks().len().saturating_add(1))?;
            let crate::types::EffectRowVariable::Rigid(identity) = tail.variable() else {
                return Err(ValidationError::new(
                    ValidationReason::TypeScope,
                    Some(node),
                ));
            };
            let kind = match identity {
                crate::types::TypeVariableId::Resolved { .. } => self
                    .program
                    .registry
                    .type_variable(identity)
                    .map(|parameter| &parameter.kind),
                crate::types::TypeVariableId::Generated(_) => {
                    type_binders.get(&identity).map(|(kind, _)| *kind)
                }
            };
            if kind.is_none_or(|kind| !matches!(kind, Kind::EffectRow)) {
                return Err(ValidationError::new(
                    ValidationReason::TypeScope,
                    Some(node),
                ));
            }
            for instance in tail.lacks() {
                self.validate_effect_instance(instance, type_binders, node)?;
            }
        }
        Ok(())
    }

    fn validate_effect_type_rows(
        &self,
        root: &Type,
        type_binders: &CoreTypeBinders<'_>,
        node: NodeId,
    ) -> Result<(), ValidationError> {
        self.charge_type_work(1)?;
        let mut work = Vec::new();
        work.try_reserve(1)
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(node)))?;
        work.push(root);
        while let Some(ty) = work.pop() {
            match ty {
                Type::Tuple(elements) => {
                    self.charge_type_work(elements.len())?;
                    work.try_reserve(elements.len()).map_err(|_| {
                        ValidationError::new(ValidationReason::Resource, Some(node))
                    })?;
                    work.extend(elements.iter());
                }
                Type::Application(function, argument) | Type::Function(function, argument) => {
                    self.charge_type_work(2)?;
                    work.try_reserve(2).map_err(|_| {
                        ValidationError::new(ValidationReason::Resource, Some(node))
                    })?;
                    work.push(argument);
                    work.push(function);
                }
                Type::EffectfulFunction(domain, computation) => {
                    self.validate_effect_row(computation.effects(), type_binders, node)?;
                    self.charge_type_work(2)?;
                    work.try_reserve(2).map_err(|_| {
                        ValidationError::new(ValidationReason::Resource, Some(node))
                    })?;
                    work.push(computation.value());
                    work.push(domain);
                }
                Type::Forall(_, body) => {
                    self.charge_type_work(1)?;
                    work.try_reserve(1).map_err(|_| {
                        ValidationError::new(ValidationReason::Resource, Some(node))
                    })?;
                    work.push(body);
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

    fn effect_row_subset_charged(
        &self,
        subset: &EffectRow,
        superset: &EffectRow,
        node: NodeId,
    ) -> Result<bool, ValidationError> {
        let union = self.union_effect_rows_charged(subset, superset, node)?;
        self.same_effect_row_charged(&union, superset, node)
    }

    fn validate_effect_nodes(
        &mut self,
        type_binders: &CoreTypeBinders<'_>,
    ) -> Result<(), ValidationError> {
        use super::effect::{EffectExprKind, EffectOperation, ResumeUse};

        let mut handler_ids = HashSet::new();
        let mut clause_contracts = HashMap::new();

        for index in 0..self.program.nodes.len() {
            let id = node_id(self.program.arena, index)?;
            let node = self.node(id)?;
            self.validate_effect_type_rows(&node.ty, type_binders, id)?;
            self.validate_effect_row(&node.effects, type_binders, id)?;
            match &node.kind {
                EffectExprKind::Pure(PureExprKind::Computation(
                    PureComputation::TypeApplication(application),
                )) => {
                    for row in application.row_arguments() {
                        self.validate_effect_row(row, type_binders, id)?;
                    }
                    self.validate_pure_effect_row(id, node)?;
                }
                EffectExprKind::Pure(_) => self.validate_pure_effect_row(id, node)?,
                EffectExprKind::Operation(EffectOperation::Request(request)) => {
                    self.validate_effect_instance(&request.effect, type_binders, id)?;
                    let (domain, result) = self.effect_signature(
                        &request.effect,
                        request.operation,
                        id,
                        type_binders,
                    )?;
                    let operand = self.node(request.operand)?;
                    if !self.same_type_charged(&operand.ty, &domain)? {
                        return Err(ValidationError::new(ValidationReason::EffectRow, Some(id)));
                    }
                    let requested = self.singleton_effect_row_charged(&request.effect, id)?;
                    let expected =
                        self.union_effect_rows_charged(&operand.effects, &requested, id)?;
                    if !self.same_type_charged(&node.ty, &result)?
                        || !self.same_effect_row_charged(&node.effects, &expected, id)?
                    {
                        return Err(ValidationError::new(ValidationReason::EffectRow, Some(id)));
                    }
                }
                EffectExprKind::Operation(EffectOperation::Resume(resume)) => {
                    if resume.use_state != ResumeUse::Consumed {
                        return Err(ValidationError::new(ValidationReason::Resume, Some(id)));
                    }
                }
                EffectExprKind::Operation(EffectOperation::Handler(handler)) => {
                    self.validate_effect_handler(
                        id,
                        node,
                        handler,
                        type_binders,
                        &mut handler_ids,
                        &mut clause_contracts,
                    )?;
                }
            }
        }
        for (index, node) in self.program.nodes.iter().enumerate() {
            let EffectExprKind::Operation(EffectOperation::Resume(resume)) = &node.kind else {
                continue;
            };
            self.validate_effect_resume(
                node_id(self.program.arena, index)?,
                node,
                resume,
                type_binders,
                &clause_contracts,
            )?;
        }
        if self.module_sources.is_some() && !self.node(self.program.root)?.effects.is_empty() {
            return Err(ValidationError::new(
                ValidationReason::EffectRow,
                Some(self.program.root),
            ));
        }
        Ok(())
    }

    fn validate_pure_effect_row(
        &self,
        id: NodeId,
        node: &StoredNode<super::effect::EffectOperationFamily>,
    ) -> Result<(), ValidationError> {
        let kind = super::effect::EffectOperationFamily::pure(&node.kind)
            .ok_or_else(|| ValidationError::new(ValidationReason::NodeType, Some(id)))?;
        let mut expected = EffectRow::empty();
        let effectful_children = match kind {
            PureExprKind::Value(PureValue::Function(_))
            | PureExprKind::Value(
                PureValue::Integer(_)
                | PureValue::Boolean(_)
                | PureValue::Unit(_)
                | PureValue::Constructor(_),
            )
            | PureExprKind::Variable(_) => false,
            PureExprKind::Computation(_) => true,
        };
        if effectful_children {
            for child_index in 0..kind.child_count() {
                let child = kind
                    .child_at(child_index)
                    .ok_or_else(|| ValidationError::new(ValidationReason::NodeBounds, Some(id)))?;
                expected =
                    self.union_effect_rows_charged(&expected, &self.node(child)?.effects, id)?;
            }
            if let PureExprKind::Computation(PureComputation::Apply(application)) = kind {
                let function = self.node(application.function())?;
                if let Type::EffectfulFunction(_, codomain) = &function.ty {
                    expected = self.union_effect_rows_charged(&expected, codomain.effects(), id)?;
                }
            }
        }
        if self.same_effect_row_charged(&node.effects, &expected, id)? {
            Ok(())
        } else {
            Err(ValidationError::new(ValidationReason::EffectRow, Some(id)))
        }
    }

    fn least_handler_output(&self, root: NodeId) -> Result<EffectRow, ValidationError> {
        use super::effect::{EffectExprKind, EffectOperation};

        enum Task {
            Collect(NodeId),
            Enter(NodeId),
            Exit(NodeId),
        }

        let mut handlers = HashSet::new();
        let mut discovered = HashSet::new();
        let mut work = Vec::new();
        self.charge_type_work(1)?;
        work.try_reserve(1)
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(root)))?;
        work.push(Task::Collect(root));
        while let Some(Task::Collect(id)) = work.pop() {
            if discovered.contains(&id) {
                continue;
            }
            self.charge_type_work(1)?;
            discovered
                .try_reserve(1)
                .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(root)))?;
            discovered.insert(id);
            let node = self.node(id)?;
            if let EffectExprKind::Operation(EffectOperation::Handler(handler)) = &node.kind
                && !handlers.contains(&handler.id())
            {
                self.charge_type_work(1)?;
                handlers
                    .try_reserve(1)
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(root)))?;
                handlers.insert(handler.id());
            }
            let child_count = super::effect::EffectOperationFamily::child_count(&node.kind);
            self.charge_type_work(child_count)?;
            work.try_reserve(child_count)
                .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(root)))?;
            for index in 0..child_count {
                work.push(Task::Collect(
                    super::effect::EffectOperationFamily::child_at(&node.kind, index).ok_or_else(
                        || ValidationError::new(ValidationReason::NodeBounds, Some(id)),
                    )?,
                ));
            }
        }
        drop(discovered);

        self.charge_type_work(1)?;
        work.try_reserve(1)
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(root)))?;
        work.push(Task::Enter(root));
        let mut rows: HashMap<NodeId, Option<EffectRow>> = HashMap::new();
        while let Some(task) = work.pop() {
            match task {
                Task::Collect(_) => unreachable!(),
                Task::Enter(id) => {
                    if rows.contains_key(&id) {
                        continue;
                    }
                    self.charge_type_work(1)?;
                    rows.try_reserve(1).map_err(|_| {
                        ValidationError::new(ValidationReason::Resource, Some(root))
                    })?;
                    rows.insert(id, None);
                    let node = self.node(id)?;
                    let child_count = super::effect::EffectOperationFamily::child_count(&node.kind);
                    let work_slots = child_count.checked_add(1).ok_or_else(|| {
                        ValidationError::new(ValidationReason::Resource, Some(root))
                    })?;
                    self.charge_type_work(work_slots)?;
                    work.try_reserve(work_slots).map_err(|_| {
                        ValidationError::new(ValidationReason::Resource, Some(root))
                    })?;
                    work.push(Task::Exit(id));
                    for index in (0..child_count).rev() {
                        work.push(Task::Enter(
                            super::effect::EffectOperationFamily::child_at(&node.kind, index)
                                .ok_or_else(|| {
                                    ValidationError::new(ValidationReason::NodeBounds, Some(id))
                                })?,
                        ));
                    }
                }
                Task::Exit(id) => {
                    let node = self.node(id)?;
                    let child_row = |child: NodeId| {
                        rows.get(&child).and_then(Option::as_ref).ok_or_else(|| {
                            ValidationError::new(ValidationReason::EffectRow, Some(id))
                        })
                    };
                    let row = match &node.kind {
                        EffectExprKind::Pure(kind) => match kind {
                            PureExprKind::Value(_) | PureExprKind::Variable(_) => {
                                EffectRow::empty()
                            }
                            PureExprKind::Computation(computation) => {
                                let mut row = EffectRow::empty();
                                for index in 0..kind.child_count() {
                                    row = self.union_effect_rows_charged(
                                        &row,
                                        child_row(kind.child_at(index).ok_or_else(|| {
                                            ValidationError::new(
                                                ValidationReason::NodeBounds,
                                                Some(id),
                                            )
                                        })?)?,
                                        id,
                                    )?;
                                }
                                if let PureComputation::Apply(application) = computation
                                    && let Type::EffectfulFunction(_, result) =
                                        &self.node(application.function())?.ty
                                {
                                    row =
                                        self.union_effect_rows_charged(&row, result.effects(), id)?;
                                }
                                row
                            }
                        },
                        EffectExprKind::Operation(EffectOperation::Request(request)) => {
                            let requested =
                                self.singleton_effect_row_charged(request.effect(), id)?;
                            self.union_effect_rows_charged(
                                child_row(request.operand())?,
                                &requested,
                                id,
                            )?
                        }
                        EffectExprKind::Operation(EffectOperation::Resume(resume)) => {
                            let source = if handlers.contains(&resume.handler()) {
                                child_row(resume.value())?
                            } else {
                                &node.effects
                            };
                            self.union_effect_rows_charged(&EffectRow::empty(), source, id)?
                        }
                        EffectExprKind::Operation(EffectOperation::Handler(handler)) => {
                            let mut row = self.remove_effect_row_charged(
                                child_row(handler.body())?,
                                handler.effect(),
                                id,
                            )?;
                            for clause in handler.clauses() {
                                row = self.union_effect_rows_charged(
                                    &row,
                                    child_row(clause.body())?,
                                    id,
                                )?;
                            }
                            row
                        }
                    };
                    *rows.get_mut(&id).ok_or_else(|| {
                        ValidationError::new(ValidationReason::EffectRow, Some(id))
                    })? = Some(row);
                }
            }
        }
        rows.remove(&root)
            .flatten()
            .ok_or_else(|| ValidationError::new(ValidationReason::EffectRow, Some(root)))
    }

    fn validate_effect_handler(
        &self,
        id: NodeId,
        node: &StoredNode<super::effect::EffectOperationFamily>,
        handler: &super::effect::HandlerNode,
        type_binders: &CoreTypeBinders<'_>,
        handler_ids: &mut HashSet<super::effect::HandlerId>,
        clause_contracts: &mut HashMap<
            (super::effect::HandlerId, crate::resolved::ResumeId),
            EffectClauseContract,
        >,
    ) -> Result<(), ValidationError> {
        self.charge_type_work(1)?;
        handler_ids
            .try_reserve(1)
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?;
        if !handler_ids.insert(handler.id) {
            return Err(ValidationError::new(ValidationReason::Handler, Some(id)));
        }
        self.validate_effect_instance(&handler.effect, type_binders, id)?;
        let declaration = self
            .program
            .registry
            .effect(handler.effect.effect())
            .ok_or_else(|| ValidationError::new(ValidationReason::EffectIdentity, Some(id)))?;
        if declaration.parameters.len() != handler.effect.arguments().len()
            || handler.clauses.len() != declaration.operations.len()
        {
            return Err(ValidationError::new(ValidationReason::Handler, Some(id)));
        }
        let body = self.node(handler.body)?;
        let remainder = self.remove_effect_row_charged(&body.effects, &handler.effect, id)?;
        if !self.same_type_charged(&body.ty, &node.ty)?
            || !self.effect_row_subset_charged(&remainder, &node.effects, id)?
        {
            return Err(ValidationError::new(ValidationReason::EffectRow, Some(id)));
        }
        self.charge_type_work(declaration.operations.len())?;
        let mut covered = Vec::new();
        covered
            .try_reserve_exact(declaration.operations.len())
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?;
        covered.resize(declaration.operations.len(), false);
        for (clause_index, clause) in handler.clauses.iter().enumerate() {
            self.charge_type_work(1)?;
            clause_contracts
                .try_reserve(1)
                .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?;
            if clause_contracts
                .insert(
                    (handler.id, clause.resume),
                    EffectClauseContract {
                        handler: id,
                        clause: clause_index,
                    },
                )
                .is_some()
            {
                return Err(ValidationError::new(ValidationReason::Handler, Some(id)));
            }
            self.validate_origin(clause.origin(), id)?;
            let (domain, _result) =
                self.effect_signature(&handler.effect, clause.operation, id, type_binders)?;
            let ordinal = usize::try_from(clause.operation.operation())
                .map_err(|_| ValidationError::new(ValidationReason::Handler, Some(id)))?;
            let Some(slot) = covered.get_mut(ordinal) else {
                return Err(ValidationError::new(ValidationReason::Handler, Some(id)));
            };
            if std::mem::replace(slot, true) {
                return Err(ValidationError::new(ValidationReason::Handler, Some(id)));
            }
            let clause_body = self.node(clause.body())?;
            self.validate_pattern(clause.pattern(), &domain, id)?;
            let matrix = vec![vec![clause.pattern().clone()]];
            let mut coverage_budget = UsefulnessBudget::default();
            if missing_witness_for_types_with_budget(
                &matrix,
                std::slice::from_ref(&domain),
                &self.program.registry,
                &mut coverage_budget,
            )
            .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?
            .is_some()
                || !self.same_type_charged(&clause_body.ty, &node.ty)?
                || !self.effect_row_subset_charged(&clause_body.effects, &node.effects, id)?
            {
                return Err(ValidationError::new(ValidationReason::Handler, Some(id)));
            }
        }
        let least = self.least_handler_output(id)?;
        if !self.same_effect_row_charged(&node.effects, &least, id)? {
            return Err(ValidationError::new(ValidationReason::EffectRow, Some(id)));
        }
        Ok(())
    }

    fn validate_effect_resume(
        &self,
        id: NodeId,
        node: &StoredNode<super::effect::EffectOperationFamily>,
        resume: &super::effect::ResumeNode,
        type_binders: &CoreTypeBinders<'_>,
        contracts: &HashMap<
            (super::effect::HandlerId, crate::resolved::ResumeId),
            EffectClauseContract,
        >,
    ) -> Result<(), ValidationError> {
        self.charge_type_work(1)?;
        let contract = contracts
            .get(&(resume.handler(), resume.owner()))
            .ok_or_else(|| ValidationError::new(ValidationReason::Resume, Some(id)))?;
        let handler_node = self.node(contract.handler)?;
        let super::effect::EffectExprKind::Operation(super::effect::EffectOperation::Handler(
            handler,
        )) = &handler_node.kind
        else {
            return Err(ValidationError::new(ValidationReason::Resume, Some(id)));
        };
        let clause = handler
            .clauses()
            .get(contract.clause)
            .ok_or_else(|| ValidationError::new(ValidationReason::Resume, Some(id)))?;
        let (_, result) =
            self.effect_signature(handler.effect(), clause.operation(), id, type_binders)?;
        let value = self.node(resume.value())?;
        if resume.use_state() != super::effect::ResumeUse::Consumed
            || !self.same_type_charged(&value.ty, &result)?
            || !self.same_type_charged(&node.ty, &handler_node.ty)?
            || !self.same_effect_row_charged(&node.effects, &handler_node.effects, id)?
            || !self.effect_row_subset_charged(&value.effects, &handler_node.effects, id)?
        {
            return Err(ValidationError::new(ValidationReason::Resume, Some(id)));
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Color {
    White,
    Gray,
    Black,
}

enum GraphTask {
    Enter(NodeId),
    Exit(NodeId),
}

struct ScopeAnalysis {
    root_requirements: ScopeRequirements,
    analyzed_nodes: usize,
}

enum ScopeAnalysisTask {
    Enter(NodeId),
    Finish(NodeId),
}

fn node_id(arena: super::dialect::ArenaId, index: usize) -> Result<NodeId, ValidationError> {
    u32::try_from(index)
        .map(|index| NodeId::new(arena, index))
        .map_err(|_| ValidationError::new(ValidationReason::NodeBounds, None))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        core::{
            CoreBuilder, NewtypeConversionDirection, PureValue,
            binding::BindingNode,
            function::{ApplicationNode, FunctionNode},
            transform::{fold_literal_primitives, identity_traversal},
            type_ops::{TypeAbstractionNode, TypeApplicationNode},
        },
        elaborate::{Elaborator, check_module, link_modules},
        integer::Integer,
        module::{ModuleGraph, ModuleRoots, load_module_graph},
        resolve::{DependencyExports, resolve_module},
        resolved::{CheckedModule, CoreGlobalParameterRowMutationForTest},
        source::ByteRange,
        validate_linked_facts_for_test,
    };
    use std::{
        fs,
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
    };

    static LINKED_VALIDATION_TEMP_IDS: AtomicU64 = AtomicU64::new(0);

    struct LinkedValidationDirectory(PathBuf);

    impl LinkedValidationDirectory {
        fn create() -> Self {
            loop {
                let id = LINKED_VALIDATION_TEMP_IDS.fetch_add(1, Ordering::Relaxed);
                let directory = std::env::temp_dir().join(format!(
                    "ash-linked-core-authority-{}-{id}",
                    std::process::id(),
                ));
                match fs::create_dir(&directory) {
                    Ok(()) => return Self(directory),
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(error) => {
                        panic!("linked Core authority fixture should be creatable: {error}")
                    }
                }
            }
        }

        fn write(&self, name: &str, source: &str) -> PathBuf {
            let path = self.0.join(name);
            fs::write(&path, source).expect("linked Core authority fixture should be writable");
            path
        }
    }

    impl Drop for LinkedValidationDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    struct LinkedCoreValidationFixture {
        directory: LinkedValidationDirectory,
        graph: ModuleGraph,
        program: UnvalidatedProgram,
        module_sources: Vec<(ModuleId, SourceId)>,
        globals: HashMap<String, (BinderId, Box<[crate::types::TypeVariableId]>)>,
    }

    impl LinkedCoreValidationFixture {
        fn compile(dependency_source: &str, entry_source: &str, expected_globals: &[&str]) -> Self {
            let directory = LinkedValidationDirectory::create();
            directory.write("dependency.ash", dependency_source);
            let entry = directory.write("entry.ash", entry_source);
            let graph = load_module_graph(&entry, &ModuleRoots::empty())
                .expect("the linked Core authority graph should load");
            let checked = checked_linked_validation_graph(&graph);
            let mut globals = HashMap::new();
            for spelling in expected_globals {
                let scheme = checked
                    .iter()
                    .flat_map(|module| module.schemes())
                    .find(|scheme| scheme.spelling == *spelling)
                    .unwrap_or_else(|| panic!("the checked {spelling} scheme should exist"));
                let parameters = scheme
                    .scheme
                    .type_parameters
                    .iter()
                    .map(|(parameter, _)| *parameter)
                    .collect::<Vec<_>>()
                    .into_boxed_slice();
                assert!(
                    globals
                        .insert((*spelling).to_owned(), (scheme.binder, parameters))
                        .is_none(),
                    "each requested linked global should have one checked scheme",
                );
            }
            let linked = link_modules(checked, graph.entry())
                .expect("the checked Core authority graph should link");
            let linked = validate_linked_facts_for_test(linked)
                .expect("the linked Core authority evidence should authenticate");
            let mut elaborator = Elaborator::for_module_program(&linked)
                .expect("the linked Core authority binder namespace should fit");
            let typed = elaborator
                .synthesize_module_program(&linked)
                .expect("the authenticated linked program should lower to Core");
            let program = elaborator
                .finish(typed.node)
                .expect("the linked Core authority root should finish");
            let module_sources = graph
                .modules()
                .iter()
                .map(|module| (module.id(), module.source().id()))
                .collect();
            Self {
                directory,
                graph,
                program,
                module_sources,
                globals,
            }
        }

        fn global(&self, spelling: &str) -> (BinderId, &[crate::types::TypeVariableId]) {
            let (binder, parameters) = self
                .globals
                .get(spelling)
                .unwrap_or_else(|| panic!("the linked {spelling} identity should be retained"));
            (*binder, parameters)
        }

        fn validate(self) -> Result<ValidatedProgram, ValidationError> {
            let Self {
                directory,
                graph,
                program,
                module_sources,
                globals: _,
            } = self;
            let sources = graph
                .modules()
                .iter()
                .map(|module| module.source())
                .collect::<Vec<_>>();
            let result = validate_modules(program, &sources, &module_sources);
            drop(directory);
            result
        }
    }

    fn method_evidence_validation_fixture() -> LinkedCoreValidationFixture {
        LinkedCoreValidationFixture::compile(
            "pub seed : Unit -> Unit\nseed value = value\n",
            concat!(
                "type Option<A> =\n",
                "None\n",
                "| Some(A)\n\n",
                "interface Score<A> {\n",
                "score<X> : (A, X) -> Int\n",
                "}\n\n",
                "impl Score<Int> {\n",
                "score (value, ignored) = value\n",
                "}\n\n",
                "impl Score<Option<A>> where Score<A> {\n",
                "score (None, ignored) = 4\n",
                "score (Some(value), ignored) = {\n",
                "let empty : Option<A> = None\n",
                "score((empty, ignored)) * 10 + score((value, ignored))\n",
                "}\n",
                "}\n\n",
                "forward<A> : A -> Int where Score<A>\n",
                "forward value = score((value, true))\n\n",
                "main : Unit -> Int\n",
                "main () = forward(Some(2))\n",
            ),
            &[],
        )
    }

    fn vector_method_evidence_validation_fixture() -> LinkedCoreValidationFixture {
        LinkedCoreValidationFixture::compile(
            "pub seed : Unit -> Unit\nseed value = value\n",
            concat!(
                "type Wrap<A> = Wrap(A)\n\n",
                "interface Relate<Left, Right> {\n",
                "relate<X> : (Left, Right, X) -> Bool\n",
                "}\n\n",
                "impl Relate<Int, Bool> {\n",
                "relate (left, right, ignored) = right\n",
                "}\n\n",
                "impl<A, Right> Relate<Wrap<A>, Right> where Relate<A, Right> {\n",
                "relate (Wrap(left), right, ignored) = relate((left, right, ignored))\n",
                "}\n\n",
                "forward<Left, Right> : (Left, Right) -> Bool where Relate<Left, Right>\n",
                "forward (left, right) = relate((left, right, ()))\n\n",
                "main : Unit -> Bool\n",
                "main () = forward((Wrap(1), true))\n",
            ),
            &[],
        )
    }

    fn monomorphic_adapter_edge_fixture() -> LinkedCoreValidationFixture {
        LinkedCoreValidationFixture::compile(
            "pub seed : Unit -> Unit\nseed value = value\n",
            concat!(
                "type Wrap<A> = Wrap(A)\n\n",
                "interface Base<I> {\nbase : I -> I\n}\n\n",
                "interface Spare<I> {\nspare : I -> I\n}\n\n",
                "interface Convert<I> {\nconvert<X> : (I, X) -> I\n}\n\n",
                "impl Base<Int> {\nbase value = value\n}\n\n",
                "impl Spare<Int> {\nspare value = value\n}\n\n",
                "impl<A> Convert<Wrap<A>> where Base<A> {\n",
                "convert (Wrap(value), ignored) = Wrap(base(value))\n",
                "}\n\n",
                "probe : Wrap<Int> -> Wrap<Int> where Base<Int>, Spare<Int>\n",
                "probe value = {\nlet ignored = spare(0)\nconvert((value, true))\n}\n\n",
                "main : Unit -> Wrap<Int>\n",
                "main () = probe(Wrap(42))\n",
            ),
            &[],
        )
    }

    fn concrete_monomorphic_adapter_edge_fixture() -> LinkedCoreValidationFixture {
        LinkedCoreValidationFixture::compile(
            "pub seed : Unit -> Unit\nseed value = value\n",
            concat!(
                "type Wrap<A> = Wrap(A)\n\n",
                "interface Base<I> {\nbase : I -> I\n}\n\n",
                "interface Convert<I> {\nconvert<X> : (I, X) -> I\n}\n\n",
                "impl Base<Int> {\nbase value = value\n}\n\n",
                "impl<A> Convert<Wrap<A>> where Base<A> {\n",
                "convert (Wrap(value), ignored) = Wrap(base(value))\n",
                "}\n\n",
                "fake : Int -> Int\nfake value = value\n\n",
                "main : Unit -> Wrap<Int>\n",
                "main () = {\nlet ignored = fake(0)\nconvert((Wrap(42), true))\n}\n",
            ),
            &[],
        )
    }

    fn concrete_source_with_wide_abstract_prerequisite_fixture() -> LinkedCoreValidationFixture {
        LinkedCoreValidationFixture::compile(
            "pub seed : Unit -> Unit\nseed value = value\n",
            concat!(
                "type Wrap<A> = Wrap(A)\n\n",
                "interface Leaf<I> {\nfirst : I -> I\nsecond : I -> I\n}\n\n",
                "interface Base<I> {\nbase : I -> I\n}\n\n",
                "interface Convert<I> {\nconvert<X> : (I, X) -> I\n}\n\n",
                "impl<A> Base<Wrap<A>> where Leaf<A> {\n",
                "base (Wrap(value)) = Wrap(first(value))\n",
                "}\n\n",
                "impl<A> Convert<Wrap<Wrap<A>>> where Base<Wrap<A>> {\n",
                "convert (Wrap(value), ignored) = Wrap(base(value))\n",
                "}\n\n",
                "probe<A> : Wrap<Wrap<A>> -> Wrap<Wrap<A>> where Leaf<A>\n",
                "probe value = convert((value, true))\n\n",
                "impl Leaf<Int> {\n",
                "first value = value\n",
                "second value = value\n",
                "}\n\n",
                "main : Unit -> Wrap<Wrap<Int>>\n",
                "main () = probe(Wrap(Wrap(42)))\n",
            ),
            &[],
        )
    }

    fn concrete_source_with_distinct_keys_instantiated_to_same_type_fixture()
    -> LinkedCoreValidationFixture {
        LinkedCoreValidationFixture::compile(
            "pub seed : Unit -> Unit\nseed value = value\n",
            concat!(
                "type Wrap<A> = Wrap(A)\n\n",
                "interface Leaf<I> {\nfirst : I -> I\nsecond : I -> I\n}\n\n",
                "interface Base<I> {\nbase : I -> I\n}\n\n",
                "interface Convert<I> {\nconvert<X> : (I, X) -> I\n}\n\n",
                "impl<A, B> Base<Wrap<(A, B)>> where Leaf<A>, Leaf<B> {\n",
                "base (Wrap((left, right))) = Wrap((first(left), first(right)))\n",
                "}\n\n",
                "impl<A, B> Convert<Wrap<Wrap<(A, B)>>> where Base<Wrap<(A, B)>> {\n",
                "convert (Wrap(value), ignored) = Wrap(base(value))\n",
                "}\n\n",
                "probe<A, B> : Wrap<Wrap<(A, B)>> -> Wrap<Wrap<(A, B)>> where Leaf<A>, Leaf<B>\n",
                "probe value = convert((value, true))\n\n",
                "impl Leaf<Int> {\n",
                "first value = value\n",
                "second value = value\n",
                "}\n\n",
                "main : Unit -> Wrap<Wrap<(Int, Int)>>\n",
                "main () = probe(Wrap(Wrap((42, 42))))\n",
            ),
            &[],
        )
    }

    fn substitute_concrete_source_direct_selection_node(program: &mut UnvalidatedProgram) {
        let (source_selection_node, implementation, first_node, sibling_node) = program
            .method_evidence
            .concrete_sources()
            .iter()
            .find_map(|source| {
                let occurrence = program.method_evidence.occurrence(source.occurrence)?;
                let EvidenceNode::Implementation { prerequisites, .. } =
                    occurrence.selection.node(source.selection_node)?
                else {
                    return None;
                };
                let [first_node, sibling_node] = prerequisites else {
                    return None;
                };
                let EvidenceNode::Abstract {
                    requirement: first_requirement,
                    methods: first_methods,
                } = occurrence.selection.node(*first_node)?
                else {
                    return None;
                };
                let EvidenceNode::Abstract {
                    requirement: sibling_requirement,
                    methods: sibling_methods,
                } = occurrence.selection.node(*sibling_node)?
                else {
                    return None;
                };
                (*first_node != *sibling_node
                    && first_requirement != sibling_requirement
                    && first_methods == sibling_methods)
                    .then_some((
                        source.selection_node,
                        source.implementation,
                        *first_node,
                        *sibling_node,
                    ))
            })
            .expect("the fixture has distinct requirement identities on same-typed direct nodes");
        let concrete_sources = Arc::get_mut(&mut program.method_evidence)
            .expect("the rebuilt program uniquely owns its catalog")
            .concrete_sources_mut_for_core_test();
        let source = concrete_sources
            .iter_mut()
            .find(|source| {
                source.selection_node == source_selection_node
                    && source.implementation == implementation
            })
            .expect("the concrete source row remains retained");
        let retained = source
            .prerequisites
            .iter_mut()
            .find(|prerequisite| prerequisite.selection_node == first_node)
            .expect("the concrete source retains the first direct prerequisite");
        retained.selection_node = sibling_node;
    }

    #[test]
    fn source_distinct_prerequisites_match_same_typed_nodes_after_every_rebuild() {
        for rebuild in 0..3 {
            let fixture = concrete_source_with_distinct_keys_instantiated_to_same_type_fixture();
            let LinkedCoreValidationFixture {
                directory,
                graph,
                mut program,
                module_sources,
                globals: _,
            } = fixture;
            let sources = graph
                .modules()
                .iter()
                .map(|module| module.source())
                .collect::<Vec<_>>();
            if rebuild != 0 {
                let validated = validate_modules(program, &sources, &module_sources)
                    .expect("the original direct prerequisite nodes validate");
                program = if rebuild == 1 {
                    identity_traversal(&validated).expect("identity rebuild")
                } else {
                    fold_literal_primitives(&validated).expect("literal-fold rebuild")
                };
                drop(validated);
            }
            substitute_concrete_source_direct_selection_node(&mut program);
            assert!(
                validate_modules(program, &sources, &module_sources).is_err(),
                "same-typed sibling-node substitution must reject after rebuild {rebuild}",
            );
            drop(directory);
        }
    }

    fn swap_concrete_source_prerequisite_method_order(program: &mut UnvalidatedProgram) {
        let (selection_node, implementation) = program
            .method_evidence
            .concrete_sources()
            .iter()
            .find_map(|source| {
                let [first, second] = source.prerequisites.as_ref() else {
                    return None;
                };
                (first.selection_node == second.selection_node && first.method != second.method)
                    .then_some((source.selection_node, source.implementation))
            })
            .expect("the fixture has one concrete source with two ordered Leaf methods");
        let source_node = program
            .method_evidence_anchors
            .iter()
            .find_map(|anchor| match anchor.role {
                MethodEvidenceAnchorRole::AdapterEdge {
                    producer_node,
                    producer_selection_node,
                    producer:
                        MethodEvidenceProducer::Adapter {
                            implementation: actual,
                        },
                    ..
                } if producer_selection_node == selection_node && actual == implementation => {
                    Some(producer_node)
                }
                _ => None,
            })
            .expect("the concrete source has one retained adapter-edge use");
        let source_index = source_node
            .index()
            .expect("the source node belongs to the fixture");
        let PureExprKind::Computation(PureComputation::Apply(outer)) =
            program.nodes[source_index].kind
        else {
            panic!("the concrete source applies its second Leaf method")
        };
        let inner_node = outer.function();
        let inner_index = inner_node
            .index()
            .expect("the inner source node belongs to the fixture");
        let PureExprKind::Computation(PureComputation::Apply(inner)) =
            program.nodes[inner_index].kind
        else {
            panic!("the concrete source applies its first Leaf method")
        };
        program.nodes[inner_index].kind = PureExprKind::Computation(PureComputation::Apply(
            ApplicationNode::new(inner.function(), outer.argument()),
        ));
        program.nodes[source_index].kind = PureExprKind::Computation(PureComputation::Apply(
            ApplicationNode::new(inner_node, inner.argument()),
        ));
        Arc::get_mut(&mut program.method_evidence)
            .expect("the rebuilt program uniquely owns its catalog")
            .concrete_sources_mut_for_core_test()
            .iter_mut()
            .find(|source| {
                source.selection_node == selection_node
                    && source.implementation == implementation
                    && source.prerequisites.len() == 2
            })
            .expect("the concrete source row remains retained")
            .prerequisites
            .swap(0, 1);
    }

    #[test]
    fn concrete_source_prerequisites_match_selected_method_order_after_every_rebuild() {
        for rebuild in 0..3 {
            let fixture = concrete_source_with_wide_abstract_prerequisite_fixture();
            let LinkedCoreValidationFixture {
                directory,
                graph,
                mut program,
                module_sources,
                globals: _,
            } = fixture;
            let sources = graph
                .modules()
                .iter()
                .map(|module| module.source())
                .collect::<Vec<_>>();
            if rebuild != 0 {
                let validated = validate_modules(program, &sources, &module_sources)
                    .expect("the original prerequisite sequence validates");
                program = if rebuild == 1 {
                    identity_traversal(&validated).expect("identity rebuild")
                } else {
                    fold_literal_primitives(&validated).expect("literal-fold rebuild")
                };
                drop(validated);
            }
            swap_concrete_source_prerequisite_method_order(&mut program);
            assert!(
                validate_modules(program, &sources, &module_sources).is_err(),
                "coordinated Leaf method-order tampering must reject after rebuild {rebuild}",
            );
            drop(directory);
        }
    }

    fn replace_concrete_monomorphic_adapter_edge_source_with_global(
        program: &mut UnvalidatedProgram,
    ) {
        let edge = program
            .method_evidence_anchors
            .iter()
            .find(|anchor| {
                let Some(MethodEvidenceExpectedRole::AdapterEdge { adapter, ordinal }) = program
                    .method_evidence
                    .expectations()
                    .get(anchor.expectation)
                    .map(|expected| expected.role)
                else {
                    return false;
                };
                matches!(
                    program.method_evidence.adapters()[adapter].prerequisites[ordinal].producer,
                    super::super::dialect::MethodEvidenceExpectedProducer::Monomorphic {
                        producer: MethodEvidenceProducer::Adapter { .. },
                        ..
                    }
                )
            })
            .expect("the fixture has a concrete monomorphic adapter edge")
            .node;
        let edge_index = edge.index().expect("the edge belongs to the fixture");
        let PureExprKind::Computation(PureComputation::Apply(application)) =
            program.nodes[edge_index].kind
        else {
            panic!("the authenticated edge is an application")
        };
        let original_argument = application.argument();
        let original = &program.nodes[original_argument.index().expect("argument index")];
        let wrong_argument = program
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match node.kind {
                PureExprKind::Variable(variable)
                    if matches!(variable.binder(), BinderId::Resolved { .. })
                        && crate::types::same_type(&node.ty, &original.ty) =>
                {
                    Some(NodeId::new(
                        program.arena,
                        u32::try_from(index).expect("fixture index"),
                    ))
                }
                _ => None,
            })
            .expect("the fixture has a same-typed ordinary global producer");
        let swapped_use = program
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                let PureExprKind::Computation(PureComputation::Apply(other)) = node.kind else {
                    return None;
                };
                (other.function() == wrong_argument && index != edge_index)
                    .then_some((index, other.argument()))
            })
            .expect("the wrong global producer has an ordinary same-typed use");
        program.nodes[swapped_use.0].kind = PureExprKind::Computation(PureComputation::Apply(
            ApplicationNode::new(original_argument, swapped_use.1),
        ));
        program.nodes[edge_index].kind = PureExprKind::Computation(PureComputation::Apply(
            ApplicationNode::new(application.function(), wrong_argument),
        ));
        let anchor = program
            .method_evidence_anchors
            .iter_mut()
            .find(|anchor| anchor.node == edge)
            .expect("the exact edge anchor is retained");
        let MethodEvidenceAnchorRole::AdapterEdge {
            adapter,
            adapter_selection_node,
            ordinal,
            producer_selection_node,
            producer,
            ..
        } = anchor.role
        else {
            unreachable!()
        };
        anchor.role = MethodEvidenceAnchorRole::AdapterEdge {
            adapter,
            adapter_selection_node,
            ordinal,
            producer_node: wrong_argument,
            producer_selection_node,
            producer_binder: None,
            producer,
        };
    }

    #[test]
    fn concrete_monomorphic_adapter_edges_reject_same_typed_global_sources_after_every_rebuild() {
        for rebuild in 0..3 {
            let fixture = concrete_monomorphic_adapter_edge_fixture();
            let LinkedCoreValidationFixture {
                directory,
                graph,
                mut program,
                module_sources,
                globals: _,
            } = fixture;
            let sources = graph
                .modules()
                .iter()
                .map(|module| module.source())
                .collect::<Vec<_>>();
            if rebuild != 0 {
                let validated = validate_modules(program, &sources, &module_sources)
                    .expect("the concrete monomorphic source validates");
                program = if rebuild == 1 {
                    identity_traversal(&validated).expect("identity rebuild")
                } else {
                    fold_literal_primitives(&validated).expect("literal-fold rebuild")
                };
            }
            replace_concrete_monomorphic_adapter_edge_source_with_global(&mut program);
            assert!(
                validate_modules(program, &sources, &module_sources).is_err(),
                "same-typed ordinary global source must reject after rebuild {rebuild}",
            );
            drop(directory);
        }
    }

    #[test]
    fn concrete_monomorphic_source_validation_has_an_exact_retry_boundary() {
        let fixture = concrete_monomorphic_adapter_edge_fixture();
        let sources = fixture
            .graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let measured = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the concrete source fixture is canonical");
        measured
            .validate_method_evidence_authority()
            .expect("the concrete source topology validates");
        // The complete-application authority graph costs 632 units. Its one concrete source
        // adds S=1 catalog lookup, one fallible pending slot, and M=1 exact
        // selected-method membership cell. The checked type walkers reserve
        // 45 root/child stack slots separately from their existing visits.
        const CHECKED_STACK_CAPACITY_WORK: usize = 45;
        const EXACT_WORK: usize = 632 + 1 + 1 + 1 + 1 + CHECKED_STACK_CAPACITY_WORK;
        assert_eq!(measured.type_work.get(), EXACT_WORK);

        let short = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the one-short concrete source fixture is canonical");
        short
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - (EXACT_WORK - 1))
            .expect("the one-short prefix fits");
        assert_eq!(
            short
                .validate_method_evidence_authority()
                .expect_err("one missing concrete-source unit rejects")
                .reason(),
            ValidationReason::Resource,
        );
        for _ in 0..2 {
            let exact = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
                .expect("the exact concrete source fixture is canonical");
            exact
                .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - EXACT_WORK)
                .expect("the exact prefix fits");
            exact
                .validate_method_evidence_authority()
                .expect("a fresh exact concrete-source pass retries");
            assert_eq!(exact.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);
        }
    }

    #[test]
    fn concrete_source_with_wide_abstract_prerequisite_has_an_exact_retry_boundary() {
        let fixture = concrete_source_with_wide_abstract_prerequisite_fixture();
        let sources = fixture
            .graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let source = fixture
            .program
            .method_evidence
            .concrete_sources()
            .iter()
            .find(|source| !source.prerequisites.is_empty())
            .expect("the concrete source retains its abstract prerequisite chain");
        assert_eq!(source.prerequisites.len(), 2);

        let measured = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the widened abstract-prerequisite fixture is canonical");
        measured
            .validate_method_evidence_authority()
            .expect("the widened concrete source topology validates");
        // The owner, occurrence, carrier, source-chain, and checked-Type
        // relations consume 1,175 units for this complete-application graph. The concrete
        // source has Q=2 retained prerequisite method rows, each of which
        // independently reads the W=2 abstract method list before membership.
        // Exact sequence comparison also visits R=2 retained rows and the W=2
        // methods of D=1 direct selected prerequisite:
        // 1,175 + Q*W + R + D*W = 1,183.
        const FIXED_AUTHORITY_AND_SOURCE_WORK: usize = 1_175;
        const PREREQUISITE_METHOD_LIST_WORK: usize = 2 * 2;
        const EXACT_PREREQUISITE_SEQUENCE_WORK: usize = 2 + 2;
        const EXACT_WORK: usize = FIXED_AUTHORITY_AND_SOURCE_WORK
            + PREREQUISITE_METHOD_LIST_WORK
            + EXACT_PREREQUISITE_SEQUENCE_WORK;
        assert_eq!(measured.type_work.get(), EXACT_WORK);

        let short = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the one-short widened source fixture is canonical");
        short
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - (EXACT_WORK - 1))
            .expect("the one-short widened-source prefix fits");
        assert_eq!(
            short
                .validate_method_evidence_authority()
                .expect_err("one missing abstract method-list capacity unit rejects")
                .reason(),
            ValidationReason::Resource,
        );
        for _ in 0..2 {
            let exact = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
                .expect("the exact widened source fixture is canonical");
            exact
                .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - EXACT_WORK)
                .expect("the exact widened-source prefix fits");
            exact
                .validate_method_evidence_authority()
                .expect("a fresh exact widened-source pass retries");
        }
        drop(fixture);
    }

    fn replace_monomorphic_adapter_edge_with_same_typed_wrong_producer(
        program: &mut UnvalidatedProgram,
        coordinate_anchor_source: bool,
    ) {
        let edge = program
            .method_evidence_anchors
            .iter()
            .find(|anchor| {
                let Some(MethodEvidenceExpectedRole::AdapterEdge { adapter, ordinal }) = program
                    .method_evidence
                    .expectations()
                    .get(anchor.expectation)
                    .map(|expected| expected.role)
                else {
                    return false;
                };
                matches!(
                    program.method_evidence.adapters()[adapter].prerequisites[ordinal].producer,
                    super::super::dialect::MethodEvidenceExpectedProducer::Monomorphic { .. }
                )
            })
            .expect("the fixture has a monomorphic adapter edge")
            .node;
        let edge_index = edge.index().expect("the edge belongs to the fixture");
        let PureExprKind::Computation(PureComputation::Apply(application)) =
            program.nodes[edge_index].kind
        else {
            panic!("the authenticated edge is an application")
        };
        let original_argument = application.argument();
        let original = &program.nodes[original_argument.index().expect("argument index")];
        let PureExprKind::Variable(original_variable) = original.kind else {
            panic!("the monomorphic concrete producer is a variable")
        };
        let wrong_argument = program
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| match node.kind {
                PureExprKind::Variable(variable)
                    if variable.binder() != original_variable.binder()
                        && matches!(variable.binder(), BinderId::Generated(_))
                        && crate::types::same_type(&node.ty, &original.ty) =>
                {
                    Some(NodeId::new(
                        program.arena,
                        u32::try_from(index).expect("fixture index"),
                    ))
                }
                _ => None,
            })
            .expect("the fixture has a same-typed wrong global producer");
        let swapped_use = program
            .nodes
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                let PureExprKind::Computation(PureComputation::Apply(other)) = node.kind else {
                    return None;
                };
                (other.function() == wrong_argument && index != edge_index)
                    .then_some((index, other.argument()))
            })
            .expect("the wrong global producer has an ordinary same-typed use");
        program.nodes[swapped_use.0].kind = PureExprKind::Computation(PureComputation::Apply(
            ApplicationNode::new(original_argument, swapped_use.1),
        ));
        program.nodes[edge_index].kind = PureExprKind::Computation(PureComputation::Apply(
            ApplicationNode::new(application.function(), wrong_argument),
        ));
        if coordinate_anchor_source {
            let wrong_binder =
                match program.nodes[wrong_argument.index().expect("wrong argument index")].kind {
                    PureExprKind::Variable(variable) => variable.binder(),
                    _ => unreachable!(),
                };
            let anchor = program
                .method_evidence_anchors
                .iter_mut()
                .find(|anchor| anchor.node == edge)
                .expect("the exact edge anchor is retained");
            let MethodEvidenceAnchorRole::AdapterEdge {
                adapter,
                adapter_selection_node,
                ordinal,
                producer_selection_node,
                producer,
                ..
            } = anchor.role
            else {
                unreachable!()
            };
            anchor.role = MethodEvidenceAnchorRole::AdapterEdge {
                adapter,
                adapter_selection_node,
                ordinal,
                producer_node: wrong_argument,
                producer_selection_node,
                producer_binder: Some(wrong_binder),
                producer,
            };
        }
    }

    #[test]
    fn monomorphic_adapter_edges_reject_same_typed_wrong_producers_after_every_rebuild() {
        for (rebuild, coordinate_anchor_source) in
            (0..3).flat_map(|rebuild| [(rebuild, false), (rebuild, true)])
        {
            let fixture = monomorphic_adapter_edge_fixture();
            let LinkedCoreValidationFixture {
                directory,
                graph,
                mut program,
                module_sources,
                globals: _,
            } = fixture;
            let sources = graph
                .modules()
                .iter()
                .map(|module| module.source())
                .collect::<Vec<_>>();
            if rebuild != 0 {
                let validated = validate_modules(program, &sources, &module_sources)
                    .expect("the original monomorphic adapter edge validates");
                program = if rebuild == 1 {
                    identity_traversal(&validated).expect("identity rebuild")
                } else {
                    fold_literal_primitives(&validated).expect("literal-fold rebuild")
                };
            }
            replace_monomorphic_adapter_edge_with_same_typed_wrong_producer(
                &mut program,
                coordinate_anchor_source,
            );
            assert!(
                validate_modules(program, &sources, &module_sources).is_err(),
                "same-typed wrong producer must reject after rebuild {rebuild} with coordinated anchor {coordinate_anchor_source}",
            );
            drop(directory);
        }
    }

    #[test]
    fn monomorphic_adapter_edge_identity_has_an_exact_validation_boundary() {
        let fixture = monomorphic_adapter_edge_fixture();
        let sources = fixture
            .graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let measured = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the monomorphic source relation is canonical");
        measured
            .validate_method_evidence_authority()
            .expect("the exact monomorphic producer identity validates");
        let exact_work = measured.type_work.get();
        // The complete-application authenticated graph costs 705 units. The exact abstract
        // producer adds one owner-envelope pass: N=49 nodes, R=5 recursive
        // members, p=0 preceding evidence functions, and one selected binder.
        // Its checked type walks independently reserve 45 root/child stack
        // slots in addition to their existing visits.
        const EXACT_SOURCE_ENVELOPE_WORK: usize = 49 + 5 + 1;
        const CHECKED_STACK_CAPACITY_WORK: usize = 45;
        const EXACT_WORK: usize = 705 + EXACT_SOURCE_ENVELOPE_WORK + CHECKED_STACK_CAPACITY_WORK;
        assert_eq!(exact_work, EXACT_WORK);

        let short = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the one-short monomorphic source relation is canonical");
        short
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - (EXACT_WORK - 1))
            .expect("the one-short prefix fits");
        assert_eq!(
            short
                .validate_method_evidence_authority()
                .expect_err("one missing exact-producer unit rejects")
                .reason(),
            ValidationReason::Resource,
        );

        for _ in 0..2 {
            let exact = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
                .expect("the exact monomorphic source relation is canonical");
            exact
                .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - EXACT_WORK)
                .expect("the exact prefix fits");
            exact
                .validate_method_evidence_authority()
                .expect("a fresh exact producer stage retries reproducibly");
        }
        drop(fixture);
    }

    #[test]
    fn independent_method_evidence_authority_has_an_exact_retry_boundary() {
        let fixture = method_evidence_validation_fixture();
        let sources = fixture
            .graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();

        let measured = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the source relation should be canonical");
        measured
            .validate_method_evidence_authority()
            .expect("the measured linked authority should validate");
        let exact_work = measured.type_work.get();
        // The complete-application authority walk costs 2,284 units. This fixture then
        // exercises 22 independently retained replacement-map, fresh-ID-set,
        // source-map, and parameter-vector capacity rows which must be admitted
        // before their respective reserves. Its A=3 adapters and Q=2 edges add
        // 28 exact-identity units: matcher A+2Q, initial role A+4Q,
        // detailed-edge 4Q, and prerequisite-sequence Q.
        const PRECHARGED_CARRIER_ROWS: usize = 22;
        const EXACT_IDENTITY_WORK: usize = 28;
        // Full and early-exit checked type walks reserve 92 exact root/child
        // stack slots independently from their already charged node visits.
        const CHECKED_STACK_CAPACITY_WORK: usize = 92;
        const EXACT_WORK: usize =
            2_284 + PRECHARGED_CARRIER_ROWS + EXACT_IDENTITY_WORK + CHECKED_STACK_CAPACITY_WORK;
        assert_eq!(exact_work, EXACT_WORK);

        let short = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the one-short source relation should be canonical");
        short
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - (exact_work - 1))
            .expect("the one-short prefix should fit");
        assert_eq!(
            short
                .validate_method_evidence_authority()
                .expect_err("one missing independent authority unit must reject")
                .reason(),
            ValidationReason::Resource,
        );

        for _ in 0..2 {
            let exact = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
                .expect("the exact source relation should be canonical");
            exact
                .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - exact_work)
                .expect("the exact prefix should fit");
            exact
                .validate_method_evidence_authority()
                .expect("a fresh exact authority stage should retry reproducibly");
            assert_eq!(exact.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);
        }
        drop(fixture.directory);
    }

    fn clone_method_evidence_anchor(anchor: &MethodEvidenceAnchor) -> MethodEvidenceAnchor {
        MethodEvidenceAnchor {
            node: anchor.node,
            owner: anchor.owner,
            requirement: anchor.requirement,
            method: anchor.method,
            application: anchor.application.clone(),
            role: anchor.role,
            occurrence: anchor.occurrence,
            expectation: anchor.expectation,
        }
    }

    #[test]
    fn linked_method_evidence_rejects_private_anchor_tampering() {
        enum Case {
            Missing,
            Duplicate,
            WrongIndex,
            StaleNode,
            WrongOwner,
            WrongRequirement,
            WrongMethod,
            WrongInterface,
            WrongOrdinal,
            WrongScheme,
            WrongApplicationProducer,
            WrongAdapterEdgeProducer,
            WrongInstantiationOwner,
            WrongInstantiationInterface,
            WrongApplicationOwner,
            WrongApplicationRequirement,
            WrongApplicationInterface,
        }

        for case in [
            Case::Missing,
            Case::Duplicate,
            Case::WrongIndex,
            Case::StaleNode,
            Case::WrongOwner,
            Case::WrongRequirement,
            Case::WrongMethod,
            Case::WrongInterface,
            Case::WrongOrdinal,
            Case::WrongScheme,
            Case::WrongApplicationProducer,
            Case::WrongAdapterEdgeProducer,
            Case::WrongInstantiationOwner,
            Case::WrongInstantiationInterface,
            Case::WrongApplicationOwner,
            Case::WrongApplicationRequirement,
            Case::WrongApplicationInterface,
        ] {
            let mut fixture = method_evidence_validation_fixture();
            let mut anchors =
                std::mem::take(&mut fixture.program.method_evidence_anchors).into_vec();
            match case {
                Case::Missing => {
                    anchors
                        .pop()
                        .expect("the fixture has authenticated anchors");
                }
                Case::Duplicate => {
                    let duplicate = clone_method_evidence_anchor(&anchors[0]);
                    anchors.push(duplicate);
                }
                Case::WrongIndex => anchors[0].expectation = usize::MAX,
                Case::StaleNode => {
                    anchors[0].node = NodeId::new(fixture.program.arena, u32::MAX);
                }
                Case::WrongOwner => {
                    let anchor = anchors
                        .iter_mut()
                        .find(|anchor| {
                            matches!(anchor.role, MethodEvidenceAnchorRole::Domain { .. })
                        })
                        .expect("the fixture has an abstract domain");
                    anchor.owner = None;
                }
                Case::WrongRequirement => {
                    let anchor = anchors
                        .iter_mut()
                        .find(|anchor| {
                            matches!(anchor.role, MethodEvidenceAnchorRole::Domain { .. })
                        })
                        .expect("the fixture has an abstract domain");
                    anchor.requirement = None;
                }
                Case::WrongMethod => {
                    let anchor = &mut anchors[0];
                    anchor.method = crate::interface::MethodId::new(
                        anchor.method.interface(),
                        anchor.method.declaration().saturating_add(1),
                    );
                }
                Case::WrongInterface => {
                    anchors[0].application = InterfaceApplication::new(
                        anchors[0].application.interface(),
                        Box::new([Type::Bool]),
                    );
                }
                Case::WrongOrdinal => {
                    let anchor = anchors
                        .iter_mut()
                        .find(|anchor| {
                            matches!(anchor.role, MethodEvidenceAnchorRole::AdapterEdge { .. })
                        })
                        .expect("the fixture has an adapter prerequisite");
                    let MethodEvidenceAnchorRole::AdapterEdge {
                        adapter,
                        adapter_selection_node,
                        ordinal,
                        producer_node,
                        producer_selection_node,
                        producer_binder,
                        producer,
                    } = anchor.role
                    else {
                        unreachable!()
                    };
                    anchor.role = MethodEvidenceAnchorRole::AdapterEdge {
                        adapter,
                        adapter_selection_node,
                        ordinal: ordinal.saturating_add(1),
                        producer_node,
                        producer_selection_node,
                        producer_binder,
                        producer,
                    };
                }
                Case::WrongScheme => {
                    let anchor = anchors
                        .iter()
                        .find(|anchor| {
                            matches!(anchor.role, MethodEvidenceAnchorRole::Adapter { .. })
                        })
                        .expect("the fixture has an adapter");
                    fixture.program.nodes[anchor.node.index().expect("adapter index")].ty =
                        Type::Bool;
                }
                Case::WrongApplicationProducer => {
                    let anchor = anchors
                        .iter_mut()
                        .find(|anchor| {
                            matches!(anchor.role, MethodEvidenceAnchorRole::Application { .. })
                        })
                        .expect("the fixture has a forwarding application");
                    let MethodEvidenceAnchorRole::Application { producer } = anchor.role else {
                        unreachable!()
                    };
                    anchor.role = MethodEvidenceAnchorRole::Application {
                        producer: match producer {
                            MethodEvidenceProducer::Abstract { requirement } => {
                                MethodEvidenceProducer::Abstract {
                                    requirement: crate::interface::RequirementId::new(
                                        requirement.owner(),
                                        requirement.declaration().saturating_add(1),
                                    ),
                                }
                            }
                            MethodEvidenceProducer::Adapter { implementation } => {
                                MethodEvidenceProducer::Abstract {
                                    requirement: crate::interface::RequirementId::new(
                                        crate::interface::RequirementOwner::Impl(
                                            implementation.implementation(),
                                        ),
                                        0,
                                    ),
                                }
                            }
                        },
                    };
                }
                Case::WrongAdapterEdgeProducer => {
                    let anchor = anchors
                        .iter_mut()
                        .find(|anchor| {
                            matches!(anchor.role, MethodEvidenceAnchorRole::AdapterEdge { .. })
                        })
                        .expect("the fixture has an adapter edge");
                    let MethodEvidenceAnchorRole::AdapterEdge {
                        adapter,
                        adapter_selection_node,
                        ordinal,
                        producer_node,
                        producer_selection_node,
                        producer_binder,
                        producer,
                    } = anchor.role
                    else {
                        unreachable!()
                    };
                    let producer = match producer {
                        MethodEvidenceProducer::Abstract { requirement } => {
                            MethodEvidenceProducer::Abstract {
                                requirement: crate::interface::RequirementId::new(
                                    requirement.owner(),
                                    requirement.declaration().saturating_add(1),
                                ),
                            }
                        }
                        MethodEvidenceProducer::Adapter { implementation } => {
                            MethodEvidenceProducer::Adapter { implementation }
                        }
                    };
                    anchor.role = MethodEvidenceAnchorRole::AdapterEdge {
                        adapter,
                        adapter_selection_node,
                        ordinal,
                        producer_node,
                        producer_selection_node,
                        producer_binder,
                        producer,
                    };
                }
                Case::WrongInstantiationOwner => {
                    let anchor = anchors
                        .iter_mut()
                        .find(|anchor| {
                            matches!(anchor.role, MethodEvidenceAnchorRole::Instantiation { .. })
                        })
                        .expect("the fixture has an instantiation");
                    anchor.owner = None;
                }
                Case::WrongInstantiationInterface => {
                    let anchor = anchors
                        .iter_mut()
                        .find(|anchor| {
                            matches!(anchor.role, MethodEvidenceAnchorRole::Instantiation { .. })
                        })
                        .expect("the fixture has an instantiation");
                    anchor.application = InterfaceApplication::new(
                        anchor.application.interface(),
                        Box::new([Type::Bool]),
                    );
                }
                Case::WrongApplicationOwner => {
                    let anchor = anchors
                        .iter_mut()
                        .find(|anchor| {
                            matches!(anchor.role, MethodEvidenceAnchorRole::Application { .. })
                        })
                        .expect("the fixture has an application");
                    anchor.owner = None;
                }
                Case::WrongApplicationRequirement => {
                    let anchor = anchors
                        .iter_mut()
                        .find(|anchor| {
                            matches!(anchor.role, MethodEvidenceAnchorRole::Application { .. })
                        })
                        .expect("the fixture has an application");
                    anchor.requirement = None;
                }
                Case::WrongApplicationInterface => {
                    let anchor = anchors
                        .iter_mut()
                        .find(|anchor| {
                            matches!(anchor.role, MethodEvidenceAnchorRole::Application { .. })
                        })
                        .expect("the fixture has an application");
                    anchor.application = InterfaceApplication::new(
                        anchor.application.interface(),
                        Box::new([Type::Bool]),
                    );
                }
            }
            fixture.program.method_evidence_anchors = anchors.into_boxed_slice();
            assert!(
                fixture.validate().is_err(),
                "tampered linked method evidence must reject"
            );
        }
    }

    #[test]
    fn linked_method_evidence_rejects_private_catalog_tampering() {
        use super::super::dialect::MethodEvidenceCatalogMutationForTest as Mutation;

        for mutation in [
            Mutation::WrongRequirementPosition,
            Mutation::WrongMethodPosition,
            Mutation::WrongMethodScheme,
            Mutation::WrongCanonicalMethodParameter,
            Mutation::WrongAdapterBinder,
            Mutation::WrongAdapterSourceParameter,
            Mutation::WrongOwnerSourceParameter,
            Mutation::WrongHeadCount,
            Mutation::WrongHeadArgument,
            Mutation::MissingPrerequisite,
            Mutation::WrongPrerequisiteProducer,
            Mutation::MissingExpectation,
            Mutation::ExtraExpectation,
        ] {
            let mut fixture = method_evidence_validation_fixture();
            assert!(
                Arc::get_mut(&mut fixture.program.method_evidence)
                    .expect("each fixture uniquely owns its catalog")
                    .corrupt_for_core_test(mutation),
                "the requested private catalog mutation must apply",
            );
            assert!(
                fixture.validate().is_err(),
                "tampered linked method-evidence authority must reject: {mutation:?}",
            );
        }
    }

    #[derive(Clone, Copy, Debug)]
    enum VectorApplicationMutation {
        Missing,
        Extra,
        Reordered,
        WrongKind,
        WrongArgumentIdentity,
        WrongInterface,
    }

    fn mutate_vector_application_for_test(
        application: &mut InterfaceApplication,
        mutation: VectorApplicationMutation,
    ) -> bool {
        let mut interface = application.interface();
        let mut arguments = application.arguments().to_vec();
        match mutation {
            VectorApplicationMutation::Missing => {
                if arguments.len() < 2 {
                    return false;
                }
                arguments.pop();
            }
            VectorApplicationMutation::Extra => arguments.push(Type::Unit),
            VectorApplicationMutation::Reordered => {
                if arguments.len() < 2 {
                    return false;
                }
                arguments.swap(0, 1);
            }
            VectorApplicationMutation::WrongKind => {
                let Some(first) = arguments.first_mut() else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(
                    first,
                    Type::Forall(Box::new([]), Box::new(Type::Unit)),
                ));
            }
            VectorApplicationMutation::WrongArgumentIdentity => {
                let Some(first) = arguments.first_mut() else {
                    return false;
                };
                discard_type_iteratively(std::mem::replace(
                    first,
                    Type::Variable(crate::types::TypeVariableId::generated(u32::MAX)),
                ));
            }
            VectorApplicationMutation::WrongInterface => {
                interface = crate::interface::InterfaceId::new(ModuleId::new(u32::MAX - 1), 0);
            }
        }
        *application = InterfaceApplication::new(interface, arguments.into_boxed_slice());
        true
    }

    #[derive(Clone, Copy, Debug)]
    enum VectorApplicationTarget {
        ImplementationOwner,
        Domain,
        Occurrence,
        AdapterEdge,
        Anchor,
    }

    #[test]
    fn independent_core_rejects_every_complete_application_vector_tamper() {
        let fixture = vector_method_evidence_validation_fixture();
        let LinkedCoreValidationFixture {
            directory,
            graph,
            program,
            module_sources,
            globals: _,
        } = fixture;
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let validated = validate_modules(program, &sources, &module_sources)
            .expect("the complete-vector fixture should validate before tampering");

        for target in [
            VectorApplicationTarget::ImplementationOwner,
            VectorApplicationTarget::Domain,
            VectorApplicationTarget::Occurrence,
            VectorApplicationTarget::AdapterEdge,
            VectorApplicationTarget::Anchor,
        ] {
            for mutation in [
                VectorApplicationMutation::Missing,
                VectorApplicationMutation::Extra,
                VectorApplicationMutation::Reordered,
                VectorApplicationMutation::WrongKind,
                VectorApplicationMutation::WrongArgumentIdentity,
                VectorApplicationMutation::WrongInterface,
            ] {
                let mut tampered = identity_traversal(&validated)
                    .expect("the validated vector fixture should rebuild independently");
                let changed = match target {
                    VectorApplicationTarget::ImplementationOwner => {
                        let catalog = Arc::make_mut(&mut tampered.method_evidence);
                        catalog
                            .implementation_owners_mut_for_core_test()
                            .iter_mut()
                            .find(|row| row.application.arguments().len() == 2)
                            .is_some_and(|row| {
                                mutate_vector_application_for_test(&mut row.application, mutation)
                            })
                    }
                    VectorApplicationTarget::Domain => {
                        let catalog = Arc::make_mut(&mut tampered.method_evidence);
                        catalog
                            .domains_mut_for_core_test()
                            .iter_mut()
                            .find(|row| row.application.arguments().len() == 2)
                            .is_some_and(|row| {
                                mutate_vector_application_for_test(&mut row.application, mutation)
                            })
                    }
                    VectorApplicationTarget::Occurrence => {
                        let catalog = Arc::make_mut(&mut tampered.method_evidence);
                        catalog
                            .occurrences_mut_for_core_test()
                            .iter_mut()
                            .find(|row| row.checked_application.arguments().len() == 2)
                            .is_some_and(|row| {
                                mutate_vector_application_for_test(
                                    &mut row.checked_application,
                                    mutation,
                                )
                            })
                    }
                    VectorApplicationTarget::AdapterEdge => {
                        let catalog = Arc::make_mut(&mut tampered.method_evidence);
                        catalog
                            .adapters_mut_for_core_test()
                            .iter_mut()
                            .flat_map(|adapter| &mut adapter.prerequisites)
                            .find(|edge| edge.application.arguments().len() == 2)
                            .is_some_and(|edge| {
                                mutate_vector_application_for_test(&mut edge.application, mutation)
                            })
                    }
                    VectorApplicationTarget::Anchor => tampered
                        .method_evidence_anchors
                        .iter_mut()
                        .find(|anchor| anchor.application.arguments().len() == 2)
                        .is_some_and(|anchor| {
                            mutate_vector_application_for_test(&mut anchor.application, mutation)
                        }),
                };
                assert!(
                    changed,
                    "the {target:?} fixture must expose a width-two carrier"
                );
                assert!(
                    validate_modules(tampered, &sources, &module_sources).is_err(),
                    "independent Core accepted {target:?} {mutation:?}",
                );
            }
        }
        drop(directory);
    }

    #[test]
    fn independent_core_rejects_interface_parameter_vector_tampering() {
        #[derive(Clone, Copy, Debug)]
        enum Mutation {
            Missing,
            Extra,
            Reordered,
            WrongIdentity,
        }

        let fixture = vector_method_evidence_validation_fixture();
        let LinkedCoreValidationFixture {
            directory,
            graph,
            program,
            module_sources,
            globals: _,
        } = fixture;
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let validated = validate_modules(program, &sources, &module_sources)
            .expect("the complete-vector fixture should validate before parameter tampering");

        for mutation in [
            Mutation::Missing,
            Mutation::Extra,
            Mutation::Reordered,
            Mutation::WrongIdentity,
        ] {
            let mut tampered = identity_traversal(&validated)
                .expect("the validated vector fixture should rebuild independently");
            let catalog = Arc::make_mut(&mut tampered.method_evidence);
            let method = catalog
                .methods_mut_for_core_test()
                .iter_mut()
                .find(|method| method.interface_parameters.len() == 2)
                .expect("the fixture retains a width-two method parameter row");
            let mut parameters = method.interface_parameters.to_vec();
            match mutation {
                Mutation::Missing => {
                    parameters.pop();
                }
                Mutation::Extra => {
                    parameters.push(crate::types::TypeVariableId::generated(u32::MAX));
                }
                Mutation::Reordered => parameters.swap(0, 1),
                Mutation::WrongIdentity => {
                    parameters[0] = crate::types::TypeVariableId::generated(u32::MAX);
                }
            }
            method.interface_parameters = parameters.into_boxed_slice();
            assert!(
                validate_modules(tampered, &sources, &module_sources).is_err(),
                "independent Core accepted {mutation:?} interface parameters",
            );
        }
        drop(directory);
    }

    fn replace_recursive_initializer_for_method_evidence_test(
        program: &mut UnvalidatedProgram,
        binder: BinderId,
        initializer: NodeId,
    ) -> Option<NodeId> {
        for node in &mut program.nodes {
            let PureExprKind::Computation(PureComputation::RecursiveBind(group)) = &mut node.kind
            else {
                continue;
            };
            if let Some(member) = group
                .members_mut()
                .iter_mut()
                .find(|member| member.binder().id() == binder)
            {
                return Some(member.replace_initializer_for_core_test(initializer));
            }
        }
        None
    }

    #[test]
    fn linked_method_evidence_rejects_wrong_owner_envelopes() {
        enum Case {
            UnanchoredWrapper,
            MovedToDifferentOwner,
            SharedByUnrelatedRecursiveBinder,
        }

        for case in [
            Case::UnanchoredWrapper,
            Case::MovedToDifferentOwner,
            Case::SharedByUnrelatedRecursiveBinder,
        ] {
            let mut fixture = method_evidence_validation_fixture();
            let owners = fixture
                .program
                .method_evidence_anchors
                .iter()
                .filter_map(|anchor| match anchor.role {
                    MethodEvidenceAnchorRole::ImplementationOwner { binder, .. } => {
                        Some((binder, anchor.node))
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            match case {
                Case::UnanchoredWrapper => {
                    let domain = fixture
                        .program
                        .method_evidence_anchors
                        .iter()
                        .find(|anchor| {
                            matches!(anchor.role, MethodEvidenceAnchorRole::Domain { .. })
                                && matches!(anchor.owner, Some(MethodEvidenceOwner::Global(_)))
                        })
                        .expect("the fixture has a polymorphic global domain");
                    let Some(MethodEvidenceOwner::Global(binder)) = domain.owner else {
                        unreachable!()
                    };
                    let domain_node = domain.node;
                    let domain_type = fixture.program.nodes
                        [domain_node.index().expect("domain index")]
                    .ty
                    .clone();
                    let origin = fixture.program.nodes[domain_node.index().expect("domain index")]
                        .origin
                        .clone();
                    let fresh = crate::types::TypeVariableId::generated(u32::MAX);
                    let wrapper = NodeId::new(
                        fixture.program.arena,
                        u32::try_from(fixture.program.nodes.len()).expect("fixture size"),
                    );
                    fixture.program.nodes.push(StoredNode {
                        dialect: DialectId::PURE,
                        effects: (),
                        ty: Type::Forall(
                            vec![(fresh, Kind::Type)].into_boxed_slice(),
                            Box::new(domain_type),
                        ),
                        kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                            TypeAbstractionNode::new(vec![(fresh, Kind::Type)], domain_node),
                        )),
                        origin,
                    });
                    replace_recursive_initializer_for_method_evidence_test(
                        &mut fixture.program,
                        binder,
                        wrapper,
                    )
                    .expect("the global owner is recursively bound");
                }
                Case::MovedToDifferentOwner => {
                    let [(first_binder, _), (_, second_root), ..] = owners.as_slice() else {
                        panic!("the fixture has two implementation owners")
                    };
                    replace_recursive_initializer_for_method_evidence_test(
                        &mut fixture.program,
                        *first_binder,
                        *second_root,
                    )
                    .expect("the first implementation owner is recursively bound");
                }
                Case::SharedByUnrelatedRecursiveBinder => {
                    let &(owner_binder, owner_root) = owners
                        .first()
                        .expect("the fixture has an implementation owner");
                    let unrelated = fixture
                        .program
                        .nodes
                        .iter()
                        .find_map(|node| {
                            let PureExprKind::Computation(PureComputation::RecursiveBind(group)) =
                                &node.kind
                            else {
                                return None;
                            };
                            group
                                .members()
                                .iter()
                                .map(|member| member.binder().id())
                                .find(|binder| *binder != owner_binder)
                        })
                        .expect("the fixture has an unrelated recursive owner");
                    replace_recursive_initializer_for_method_evidence_test(
                        &mut fixture.program,
                        unrelated,
                        owner_root,
                    )
                    .expect("the unrelated owner is recursively bound");
                }
            }
            assert!(
                fixture.validate().is_err(),
                "an authenticated method domain must remain in its exact declared owner envelope",
            );
        }
    }

    fn zero_parameter_implementation_owner_fixture() -> LinkedCoreValidationFixture {
        LinkedCoreValidationFixture::compile(
            "pub seed : Unit -> Unit\nseed value = value\n",
            concat!(
                "interface Poly<A> {\n",
                "poly<X> : (A, X) -> Int\n",
                "}\n\n",
                "interface Use<A> {\n",
                "left : A -> Int\n",
                "right : A -> Int\n",
                "}\n\n",
                "impl Poly<Int> {\n",
                "poly (value, ignored) = value\n",
                "}\n\n",
                "impl Use<Int> where Poly<Int> {\n",
                "left value = poly((value, true))\n",
                "right value = poly((value, ()))\n",
                "}\n\n",
                "main : Unit -> Int\n",
                "main () = 0\n",
            ),
            &[],
        )
    }

    #[test]
    fn zero_parameter_implementation_domains_have_exact_owner_envelopes() {
        let positive = zero_parameter_implementation_owner_fixture();
        positive
            .validate()
            .expect("nongeneric implementation methods may own polymorphic prerequisite domains");

        let mut swapped = zero_parameter_implementation_owner_fixture();
        let owners = swapped
            .program
            .method_evidence_anchors
            .iter()
            .filter_map(|anchor| match anchor.role {
                MethodEvidenceAnchorRole::ImplementationOwner { binder, .. } => {
                    Some((binder, anchor.node))
                }
                _ => None,
            })
            .filter(|(_, node)| {
                !matches!(
                    swapped.program.nodes[node.index().expect("owner index")].kind,
                    PureExprKind::Computation(PureComputation::TypeAbstraction(_))
                )
            })
            .collect::<Vec<_>>();
        let [(first_binder, first_root), (second_binder, second_root), ..] = owners.as_slice()
        else {
            panic!("the fixture has two zero-parameter implementation owners")
        };
        replace_recursive_initializer_for_method_evidence_test(
            &mut swapped.program,
            *first_binder,
            *second_root,
        );
        replace_recursive_initializer_for_method_evidence_test(
            &mut swapped.program,
            *second_binder,
            *first_root,
        );
        assert!(
            swapped.validate().is_err(),
            "domain chains cannot move between implementation-method initializers",
        );
    }

    #[derive(Clone, Copy)]
    enum ExtraCarrierUse {
        BindStorage,
        Return,
    }

    fn add_extra_carrier_use_for_test(
        program: &mut UnvalidatedProgram,
        source: NodeId,
        use_kind: ExtraCarrierUse,
    ) {
        let old_root = program.root;
        let old_root_index = old_root.index().expect("root index");
        let root_type = program.nodes[old_root_index].ty.clone();
        let root_origin = program.nodes[old_root_index].origin.clone();
        let binder = program
            .nodes
            .iter()
            .find_map(|node| match &node.kind {
                PureExprKind::Value(PureValue::Function(function)) => {
                    Some(function.parameter().clone())
                }
                _ => None,
            })
            .expect("the fixture has a function binder");
        let node = NodeId::new(
            program.arena,
            u32::try_from(program.nodes.len()).expect("fixture size"),
        );
        let (ty, kind) = match use_kind {
            ExtraCarrierUse::BindStorage => (
                root_type,
                PureExprKind::Computation(PureComputation::Bind(BindingNode::new(
                    binder, source, old_root,
                ))),
            ),
            ExtraCarrierUse::Return => (
                Type::Function(
                    Box::new(binder.ty().clone()),
                    Box::new(
                        program.nodes[source.index().expect("source index")]
                            .ty
                            .clone(),
                    ),
                ),
                PureExprKind::Value(PureValue::Function(FunctionNode::new(binder, source))),
            ),
        };
        program.nodes.push(StoredNode {
            dialect: DialectId::PURE,
            effects: (),
            ty,
            origin: root_origin,
            kind,
        });
        program.root = node;
    }

    #[test]
    fn authenticated_method_schemes_reject_every_extra_incoming_use() {
        for use_kind in [ExtraCarrierUse::BindStorage, ExtraCarrierUse::Return] {
            let mut fixture = method_evidence_validation_fixture();
            let adapter = fixture
                .program
                .method_evidence_anchors
                .iter()
                .find(|anchor| matches!(anchor.role, MethodEvidenceAnchorRole::Adapter { .. }))
                .expect("the fixture has an adapter")
                .node;
            add_extra_carrier_use_for_test(&mut fixture.program, adapter, use_kind);
            assert!(
                fixture.validate().is_err(),
                "an authenticated adapter cannot be stored or returned in addition to its exact consumer",
            );
        }

        let mut domain = method_evidence_validation_fixture();
        let source = domain
            .program
            .method_evidence_anchors
            .iter()
            .find_map(|anchor| match anchor.role {
                MethodEvidenceAnchorRole::Instantiation { binder: Some(_) } => {
                    let PureExprKind::Computation(PureComputation::TypeApplication(application)) =
                        &domain.program.nodes[anchor.node.index().expect("instantiation index")]
                            .kind
                    else {
                        return None;
                    };
                    Some(application.function())
                }
                _ => None,
            })
            .expect("the fixture has an abstract domain scheme variable");
        add_extra_carrier_use_for_test(&mut domain.program, source, ExtraCarrierUse::BindStorage);
        assert!(
            domain.validate().is_err(),
            "an authenticated domain scheme variable cannot gain an extra use",
        );
    }

    #[test]
    fn transformed_method_schemes_reject_extra_incoming_use() {
        let fixture = method_evidence_validation_fixture();
        let LinkedCoreValidationFixture {
            directory,
            graph,
            program,
            module_sources,
            globals: _,
        } = fixture;
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let validated = validate_modules(program, &sources, &module_sources)
            .expect("the authenticated fixture validates before transforms");
        for mut transformed in [
            identity_traversal(&validated).expect("identity rebuild"),
            fold_literal_primitives(&validated).expect("literal-fold rebuild"),
        ] {
            let adapter = transformed
                .method_evidence_anchors
                .iter()
                .find(|anchor| matches!(anchor.role, MethodEvidenceAnchorRole::Adapter { .. }))
                .expect("the transformed fixture has an adapter")
                .node;
            add_extra_carrier_use_for_test(&mut transformed, adapter, ExtraCarrierUse::BindStorage);
            assert!(
                validate_modules(transformed, &sources, &module_sources).is_err(),
                "fresh validation rejects an extra adapter use after every transform",
            );
        }
        drop(directory);
    }

    fn coordinated_adapter_interface_fixture() -> LinkedCoreValidationFixture {
        LinkedCoreValidationFixture::compile(
            "pub seed : Unit -> Unit\nseed value = value\n",
            concat!(
                "interface Token<I> {\n",
                "token<X> : (I, X) -> Unit\n",
                "}\n\n",
                "impl Token<Int> {\n",
                "token value = ()\n",
                "}\n\n",
                "probe : Int -> Unit\n",
                "probe value = token((value, true))\n\n",
                "main : Unit -> Unit\n",
                "main () = ()\n",
            ),
            &[],
        )
    }

    fn rewrite_int_to_bool_for_test(ty: &mut Type) {
        enum Task<'a> {
            Visit(&'a Type),
            Application,
            Function,
            EffectfulFunction(crate::types::EffectRow),
            Tuple(usize),
            Forall(Box<[(crate::types::TypeVariableId, Kind)]>),
        }
        let mut pending = vec![Task::Visit(ty)];
        let mut output = Vec::new();
        while let Some(task) = pending.pop() {
            match task {
                Task::Visit(Type::Int) => output.push(Type::Bool),
                Task::Visit(Type::Bool) => output.push(Type::Bool),
                Task::Visit(Type::Unit) => output.push(Type::Unit),
                Task::Visit(Type::Nominal(id)) => output.push(Type::Nominal(*id)),
                Task::Visit(Type::Variable(id)) => output.push(Type::Variable(*id)),
                Task::Visit(Type::Inference(id)) => output.push(Type::Inference(*id)),
                Task::Visit(Type::Application(function, argument)) => {
                    pending.push(Task::Application);
                    pending.push(Task::Visit(argument));
                    pending.push(Task::Visit(function));
                }
                Task::Visit(Type::Function(domain, codomain)) => {
                    pending.push(Task::Function);
                    pending.push(Task::Visit(codomain));
                    pending.push(Task::Visit(domain));
                }
                Task::Visit(Type::EffectfulFunction(domain, codomain)) => {
                    pending.push(Task::EffectfulFunction(codomain.effects().clone()));
                    pending.push(Task::Visit(codomain.value()));
                    pending.push(Task::Visit(domain));
                }
                Task::Visit(Type::Tuple(elements)) => {
                    pending.push(Task::Tuple(elements.len()));
                    pending.extend(elements.iter().rev().map(Task::Visit));
                }
                Task::Visit(Type::Forall(parameters, body)) => {
                    pending.push(Task::Forall(parameters.clone()));
                    pending.push(Task::Visit(body));
                }
                Task::Application | Task::Function => {
                    let argument = output.pop().expect("binary argument");
                    let function = output.pop().expect("binary function");
                    output.push(if matches!(task, Task::Application) {
                        Type::Application(Box::new(function), Box::new(argument))
                    } else {
                        Type::Function(Box::new(function), Box::new(argument))
                    });
                }
                Task::EffectfulFunction(effects) => {
                    let value = output.pop().expect("effectful function value");
                    let domain = output.pop().expect("effectful function domain");
                    output.push(Type::function_computation(
                        domain,
                        crate::types::ComputationType::new(value, effects),
                    ));
                }
                Task::Tuple(len) => {
                    let start = output.len().checked_sub(len).expect("tuple children");
                    let elements = output.split_off(start).into_boxed_slice();
                    output.push(Type::Tuple(elements));
                }
                Task::Forall(parameters) => {
                    let body = output.pop().expect("forall body");
                    output.push(Type::Forall(parameters, Box::new(body)));
                }
            }
        }
        crate::types::replace_type_iteratively(ty, output.pop().expect("rewritten type"));
    }

    fn coordinate_forged_adapter_interface_for_test(program: &mut UnvalidatedProgram) {
        let occurrence = program
            .method_evidence_anchors
            .iter()
            .find(|anchor| matches!(anchor.role, MethodEvidenceAnchorRole::Adapter { .. }))
            .and_then(|anchor| anchor.occurrence)
            .expect("the fixture has an authenticated adapter occurrence");
        for anchor in &mut program.method_evidence_anchors {
            if anchor.occurrence == Some(occurrence)
                && matches!(
                    anchor.role,
                    MethodEvidenceAnchorRole::Adapter { .. }
                        | MethodEvidenceAnchorRole::Instantiation { .. }
                )
            {
                anchor.application = InterfaceApplication::new(
                    anchor.application.interface(),
                    Box::new([Type::Bool]),
                );
            }
        }
        let catalog = Arc::make_mut(&mut program.method_evidence);
        let occurrence = catalog
            .occurrences_mut_for_core_test()
            .iter_mut()
            .find(|row| row.slot == occurrence)
            .expect("the catalog retains the adapter occurrence");
        let mut rewritten_arguments = occurrence.checked_application.arguments().to_vec();
        for argument in &mut rewritten_arguments {
            rewrite_int_to_bool_for_test(argument);
        }
        occurrence.checked_application = InterfaceApplication::new(
            occurrence.checked_application.interface(),
            rewritten_arguments.into_boxed_slice(),
        );
        if let Some(checked) = occurrence.checked_value_type.as_mut() {
            rewrite_int_to_bool_for_test(checked);
        }
        for argument in &mut occurrence.method_arguments {
            rewrite_int_to_bool_for_test(argument);
        }
        for node in &mut program.nodes {
            rewrite_int_to_bool_for_test(&mut node.ty);
            match &mut node.kind {
                PureExprKind::Value(PureValue::Function(function)) => {
                    let mut ty = function.parameter().ty().clone();
                    rewrite_int_to_bool_for_test(&mut ty);
                    function.parameter_mut().replace_type(ty);
                }
                PureExprKind::Computation(PureComputation::Bind(binding)) => {
                    let mut ty = binding.binder().ty().clone();
                    rewrite_int_to_bool_for_test(&mut ty);
                    binding.binder_mut().replace_type(ty);
                }
                PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
                    for member in group.members_mut() {
                        let mut ty = member.binder().ty().clone();
                        rewrite_int_to_bool_for_test(&mut ty);
                        member.binder_mut().replace_type(ty);
                    }
                }
                PureExprKind::Computation(PureComputation::TypeApplication(application)) => {
                    application
                        .rewrite_types(&mut |ty| {
                            let mut rewritten = ty.clone();
                            rewrite_int_to_bool_for_test(&mut rewritten);
                            Ok(rewritten)
                        })
                        .expect("fixture type arguments remain representable");
                }
                PureExprKind::Computation(PureComputation::Match(matched)) => {
                    for arm in matched.arms_mut() {
                        arm.pattern_mut()
                            .rewrite_types(&mut |ty| {
                                let mut rewritten = ty.clone();
                                rewrite_int_to_bool_for_test(&mut rewritten);
                                Ok(rewritten)
                            })
                            .expect("fixture patterns remain representable");
                    }
                }
                PureExprKind::Value(_)
                | PureExprKind::Variable(_)
                | PureExprKind::Computation(
                    PureComputation::Apply(_)
                    | PureComputation::Primitive(_)
                    | PureComputation::Tuple(_)
                    | PureComputation::NewtypeConversion(_)
                    | PureComputation::TypeAbstraction(_),
                ) => {}
            }
        }
    }

    #[test]
    fn adapter_interface_is_derived_after_coordinated_core_scheme_forgery() {
        let mut original = coordinated_adapter_interface_fixture();
        coordinate_forged_adapter_interface_for_test(&mut original.program);
        assert!(
            original.validate().is_err(),
            "the adapter interface argument is derived from its exact implementation head",
        );

        let fixture = coordinated_adapter_interface_fixture();
        let LinkedCoreValidationFixture {
            directory,
            graph,
            program,
            module_sources,
            globals: _,
        } = fixture;
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let validated = validate_modules(program, &sources, &module_sources)
            .expect("the independent-interface adapter validates before transforms");
        for mut transformed in [
            identity_traversal(&validated).expect("identity rebuild"),
            fold_literal_primitives(&validated).expect("literal-fold rebuild"),
        ] {
            coordinate_forged_adapter_interface_for_test(&mut transformed);
            assert!(
                validate_modules(transformed, &sources, &module_sources).is_err(),
                "fresh validation re-derives adapter interface arguments after transforms",
            );
        }
        drop(directory);
    }

    fn method_adapter_nodes(program: &UnvalidatedProgram) -> Vec<NodeId> {
        program
            .method_evidence_anchors
            .iter()
            .filter_map(|anchor| {
                matches!(anchor.role, MethodEvidenceAnchorRole::Adapter { .. })
                    .then_some(anchor.node)
            })
            .collect()
    }

    fn replace_adapter_parameter_only_for_test(
        program: &mut UnvalidatedProgram,
        adapter: NodeId,
        replacement: crate::types::TypeVariableId,
    ) {
        let node = &mut program.nodes[adapter.index().expect("adapter index")];
        let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
            &mut node.kind
        else {
            panic!("an adapter is a type abstraction")
        };
        let parameters = abstraction
            .parameters()
            .iter()
            .enumerate()
            .map(|(index, (_, kind))| {
                (
                    if index == 0 {
                        replacement
                    } else {
                        abstraction.parameters()[index].0
                    },
                    kind.clone(),
                )
            })
            .collect();
        *abstraction = TypeAbstractionNode::new(parameters, abstraction.body());
    }

    #[test]
    fn method_adapter_alpha_renaming_is_complete_capture_free_and_local() {
        let mut complete = method_evidence_validation_fixture();
        let adapter = method_adapter_nodes(&complete.program)[0];
        let fresh = fresh_generated_identity(&complete.program);
        rename_generated_abstraction(&mut complete.program, adapter, fresh);
        complete
            .validate()
            .expect("a complete capture-free adapter-local alpha rename validates");

        let mut partial = method_evidence_validation_fixture();
        let adapter = method_adapter_nodes(&partial.program)[0];
        let fresh = fresh_generated_identity(&partial.program);
        replace_adapter_parameter_only_for_test(&mut partial.program, adapter, fresh);
        assert!(
            partial.validate().is_err(),
            "a partial adapter rename rejects"
        );

        let mut captured = method_evidence_validation_fixture();
        let adapter = captured
            .program
            .method_evidence_anchors
            .iter()
            .find(|anchor| {
                matches!(anchor.role, MethodEvidenceAnchorRole::Adapter { .. })
                    && matches!(anchor.owner, Some(MethodEvidenceOwner::Implementation(_)))
            })
            .expect("the fixture has an adapter nested in an implementation")
            .node;
        let implementation = captured
            .program
            .method_evidence_anchors
            .iter()
            .find(|anchor| {
                matches!(
                    anchor.role,
                    MethodEvidenceAnchorRole::ImplementationOwner { .. }
                )
            })
            .expect("the fixture has an implementation owner")
            .node;
        let PureExprKind::Computation(PureComputation::TypeAbstraction(owner)) =
            &captured.program.nodes[implementation.index().expect("owner index")].kind
        else {
            panic!("the generic implementation owner is an abstraction")
        };
        let enclosing = owner.parameters()[0].0;
        rename_generated_abstraction(&mut captured.program, adapter, enclosing);
        assert!(
            captured.validate().is_err(),
            "an adapter parameter cannot capture an enclosing generated parameter",
        );

        let mut sibling = method_evidence_validation_fixture();
        let adapters = method_adapter_nodes(&sibling.program);
        let reused = generated_parameter(&sibling.program, adapters[1]);
        rename_generated_abstraction(&mut sibling.program, adapters[0], reused);
        assert!(
            sibling.validate().is_err(),
            "adapter-local binders cannot be reused by a sibling adapter",
        );

        let mut escaped = method_evidence_validation_fixture();
        let adapter = method_adapter_nodes(&escaped.program)[0];
        let fresh = fresh_generated_identity(&escaped.program);
        rewrite_generated_body_occurrences_without_binder(&mut escaped.program, adapter, fresh);
        assert!(
            escaped.validate().is_err(),
            "an adapter body binder cannot escape"
        );

        let fixture = method_evidence_validation_fixture();
        let LinkedCoreValidationFixture {
            directory,
            graph,
            program,
            module_sources,
            globals: _,
        } = fixture;
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let validated = validate_modules(program, &sources, &module_sources)
            .expect("the adapter fixture validates before transformation");
        let mut transformed = identity_traversal(&validated).expect("identity rebuild");
        let adapter = method_adapter_nodes(&transformed)[0];
        let fresh = fresh_generated_identity(&transformed);
        replace_adapter_parameter_only_for_test(&mut transformed, adapter, fresh);
        assert!(
            validate_modules(transformed, &sources, &module_sources).is_err(),
            "fresh post-transform validation rejects a partial adapter rename",
        );
        drop(directory);
    }

    #[test]
    fn linked_method_evidence_transforms_remap_and_revalidate_every_anchor() {
        let fixture = method_evidence_validation_fixture();
        let LinkedCoreValidationFixture {
            directory,
            graph,
            program,
            module_sources,
            globals: _,
        } = fixture;
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let original = validate_modules(program, &sources, &module_sources)
            .expect("the authenticated method-evidence fixture validates");
        let anchor_count = original.method_evidence_anchors().len();
        for transformed in [
            identity_traversal(&original).expect("identity rebuild"),
            fold_literal_primitives(&original).expect("literal-fold rebuild"),
        ] {
            assert_eq!(transformed.method_evidence_anchors.len(), anchor_count);
            validate_modules(transformed, &sources, &module_sources)
                .expect("every remapped method-evidence anchor freshly validates");
        }
        let mut tampered = identity_traversal(&original).expect("post-transform tamper rebuild");
        tampered.method_evidence_anchors[0].expectation = usize::MAX;
        assert!(
            validate_modules(tampered, &sources, &module_sources).is_err(),
            "a freshly remapped sidecar must remain independently authenticated",
        );
        drop(directory);
    }

    #[test]
    fn complete_application_vectors_survive_both_core_transforms() {
        let fixture = vector_method_evidence_validation_fixture();
        let LinkedCoreValidationFixture {
            directory,
            graph,
            program,
            module_sources,
            globals: _,
        } = fixture;
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let original = validate_modules(program, &sources, &module_sources)
            .expect("the authenticated vector fixture should validate");
        let expected_widths = original
            .method_evidence_anchors()
            .iter()
            .map(|anchor| anchor.application.arguments().len())
            .collect::<Vec<_>>();
        assert!(expected_widths.contains(&2));

        for transformed in [
            identity_traversal(&original).expect("identity vector rebuild"),
            fold_literal_primitives(&original).expect("literal-fold vector rebuild"),
        ] {
            assert_eq!(
                transformed
                    .method_evidence_anchors
                    .iter()
                    .map(|anchor| anchor.application.arguments().len())
                    .collect::<Vec<_>>(),
                expected_widths,
            );
            validate_modules(transformed, &sources, &module_sources)
                .expect("every transformed complete application should freshly validate");
        }
        drop(directory);
    }

    fn checked_linked_validation_graph(graph: &ModuleGraph) -> Vec<CheckedModule> {
        let mut checked = Vec::new();
        for module in graph.modules() {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    let dependency = checked
                        .iter()
                        .find(|checked: &&CheckedModule| checked.module() == edge.target())
                        .expect("dependency order should check the target first");
                    DependencyExports::new(edge, dependency.exports())
                        .expect("checked dependency exports should authenticate their edge")
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module(module, &dependencies)
                .expect("the linked Core authority graph should resolve");
            checked.push(
                check_module(resolved).expect("the linked Core authority graph should check"),
            );
        }
        checked
    }

    fn linked_global_abstraction(program: &UnvalidatedProgram, global: BinderId) -> NodeId {
        let mut result = None;
        for node in &program.nodes {
            let PureExprKind::Computation(PureComputation::RecursiveBind(group)) = &node.kind
            else {
                continue;
            };
            for member in group.members() {
                if member.binder().id() == global {
                    assert!(
                        result.replace(member.initializer()).is_none(),
                        "a linked global should have exactly one recursive member",
                    );
                }
            }
        }
        let abstraction = result.expect("the linked global recursive member should exist");
        let node = program
            .nodes
            .get(
                abstraction
                    .index()
                    .expect("the abstraction index should fit"),
            )
            .expect("the linked global initializer should belong to its arena");
        assert!(
            matches!(
                node.kind,
                PureExprKind::Computation(PureComputation::TypeAbstraction(_))
            ),
            "a polymorphic linked global should own a type abstraction",
        );
        abstraction
    }

    fn linked_global_type_application(program: &UnvalidatedProgram, global: BinderId) -> NodeId {
        let mut result = None;
        for (index, node) in program.nodes.iter().enumerate() {
            let PureExprKind::Computation(PureComputation::TypeApplication(application)) =
                &node.kind
            else {
                continue;
            };
            let function = &program.nodes[application
                .function()
                .index()
                .expect("the linked type-application function index should fit")];
            if matches!(
                function.kind,
                PureExprKind::Variable(variable) if variable.binder() == global
            ) {
                let id = NodeId::new(
                    program.arena,
                    u32::try_from(index).expect("the linked type-application index should fit"),
                );
                assert!(
                    result.replace(id).is_none(),
                    "the selected global should have one linked type application",
                );
            }
        }
        result.expect("the selected linked global should be type-applied")
    }

    fn swap_type_variable_identity(
        identity: &mut crate::types::TypeVariableId,
        left: crate::types::TypeVariableId,
        right: crate::types::TypeVariableId,
    ) {
        if *identity == left {
            *identity = right;
        } else if *identity == right {
            *identity = left;
        }
    }

    fn swap_type_variable_identities(
        root: &mut Type,
        left: crate::types::TypeVariableId,
        right: crate::types::TypeVariableId,
    ) {
        let mut work = vec![root];
        while let Some(ty) = work.pop() {
            match ty {
                Type::Variable(identity) => swap_type_variable_identity(identity, left, right),
                Type::Tuple(elements) => work.extend(elements.iter_mut()),
                Type::Application(function, argument) | Type::Function(function, argument) => {
                    work.push(argument);
                    work.push(function);
                }
                Type::EffectfulFunction(_, _) => {}
                Type::Forall(parameters, body) => {
                    for (parameter, _) in parameters {
                        swap_type_variable_identity(parameter, left, right);
                    }
                    work.push(body);
                }
                Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) | Type::Inference(_) => {}
            }
        }
    }

    fn swap_binder_type_variables(
        binder: &mut crate::core::TypedBinder,
        left: crate::types::TypeVariableId,
        right: crate::types::TypeVariableId,
    ) {
        let mut ty = binder.ty().clone();
        swap_type_variable_identities(&mut ty, left, right);
        binder.replace_type(ty);
    }

    fn coherently_swap_core_type_variables(
        program: &mut UnvalidatedProgram,
        left: crate::types::TypeVariableId,
        right: crate::types::TypeVariableId,
    ) {
        for node in &mut program.nodes {
            swap_type_variable_identities(&mut node.ty, left, right);
            match &mut node.kind {
                PureExprKind::Value(PureValue::Function(function)) => {
                    swap_binder_type_variables(function.parameter_mut(), left, right);
                }
                PureExprKind::Computation(PureComputation::Bind(binding)) => {
                    swap_binder_type_variables(binding.binder_mut(), left, right);
                }
                PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
                    for member in group.members_mut() {
                        swap_binder_type_variables(member.binder_mut(), left, right);
                    }
                }
                PureExprKind::Computation(PureComputation::Match(match_expression)) => {
                    for arm in match_expression.arms_mut() {
                        arm.pattern_mut()
                            .rewrite_types(&mut |ty| {
                                let mut rewritten = ty.clone();
                                swap_type_variable_identities(&mut rewritten, left, right);
                                Ok(rewritten)
                            })
                            .expect(
                                "the admitted linked pattern types should remain representable",
                            );
                    }
                }
                PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) => {
                    let parameters = abstraction
                        .parameters()
                        .iter()
                        .map(|(parameter, kind)| {
                            let mut parameter = *parameter;
                            swap_type_variable_identity(&mut parameter, left, right);
                            (parameter, kind.clone())
                        })
                        .collect();
                    *abstraction = TypeAbstractionNode::new(parameters, abstraction.body());
                }
                PureExprKind::Computation(PureComputation::TypeApplication(application)) => {
                    application
                        .rewrite_types(&mut |ty| {
                            let mut rewritten = ty.clone();
                            swap_type_variable_identities(&mut rewritten, left, right);
                            Ok(rewritten)
                        })
                        .expect("the admitted linked type arguments should remain representable");
                }
                PureExprKind::Value(
                    PureValue::Integer(_)
                    | PureValue::Boolean(_)
                    | PureValue::Unit(_)
                    | PureValue::Constructor(_),
                )
                | PureExprKind::Variable(_)
                | PureExprKind::Computation(
                    PureComputation::Apply(_)
                    | PureComputation::Primitive(_)
                    | PureComputation::Tuple(_)
                    | PureComputation::NewtypeConversion(_),
                ) => {}
            }
        }
    }

    #[test]
    fn linked_core_rejects_coherent_resolved_binder_owner_swap() {
        let mut fixture = LinkedCoreValidationFixture::compile(
            concat!(
                "pub first<A : Type> : A -> A\n",
                "first value = value\n\n",
                "pub second<B : Type> : B -> B\n",
                "second value = value\n",
            ),
            concat!(
                "import dependency (first, second)\n",
                "main : Unit -> Int\n",
                "main () = first(second(1))\n",
            ),
            &["first", "second"],
        );
        let (first, first_parameters) = fixture.global("first");
        let first_parameter = first_parameters[0];
        let (second, second_parameters) = fixture.global("second");
        let second_parameter = second_parameters[0];
        assert_ne!(first_parameter, second_parameter);
        let first_abstraction = linked_global_abstraction(&fixture.program, first);
        let second_abstraction = linked_global_abstraction(&fixture.program, second);

        coherently_swap_core_type_variables(
            &mut fixture.program,
            first_parameter,
            second_parameter,
        );
        for (abstraction, expected) in [
            (first_abstraction, second_parameter),
            (second_abstraction, first_parameter),
        ] {
            let node = &fixture.program.nodes[abstraction
                .index()
                .expect("the linked abstraction index should fit")];
            let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                &node.kind
            else {
                panic!("the coherently mutated initializer should remain an abstraction");
            };
            assert_eq!(abstraction.parameters()[0].0, expected);
            let Type::Forall(parameters, _) = &node.ty else {
                panic!("the coherently mutated abstraction should retain its scheme");
            };
            assert_eq!(parameters[0].0, expected);
        }

        let error = fixture
            .validate()
            .expect_err("linked validation must reject resolved binders under the wrong owner");
        assert_eq!(error.reason(), ValidationReason::Registry);
        assert_eq!(error.node(), Some(first_abstraction));
    }

    #[test]
    fn linked_core_rejects_coherent_resolved_binder_reorder() {
        let mut fixture = LinkedCoreValidationFixture::compile(
            concat!(
                "pub choose<A : Type, B : Type> : A -> B -> A\n",
                "choose left right = left\n",
            ),
            concat!(
                "import dependency (choose)\n",
                "main : Unit -> Int\n",
                "main () = choose(1)(true)\n",
            ),
            &["choose"],
        );
        let (choose, parameters) = fixture.global("choose");
        let [first_parameter, second_parameter] = parameters else {
            panic!("choose should retain two checked type parameters");
        };
        let first_parameter = *first_parameter;
        let second_parameter = *second_parameter;
        assert_ne!(first_parameter, second_parameter);
        let choose_abstraction = linked_global_abstraction(&fixture.program, choose);

        coherently_swap_core_type_variables(
            &mut fixture.program,
            first_parameter,
            second_parameter,
        );
        let node = &fixture.program.nodes[choose_abstraction
            .index()
            .expect("the linked abstraction index should fit")];
        let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) = &node.kind
        else {
            panic!("the coherently reordered initializer should remain an abstraction");
        };
        let reordered = [second_parameter, first_parameter];
        assert!(
            abstraction
                .parameters()
                .iter()
                .map(|(parameter, _)| *parameter)
                .eq(reordered),
        );
        let Type::Forall(scheme_parameters, _) = &node.ty else {
            panic!("the coherently reordered abstraction should retain its scheme");
        };
        assert!(
            scheme_parameters
                .iter()
                .map(|(parameter, _)| *parameter)
                .eq(reordered),
        );

        let error = fixture
            .validate()
            .expect_err("linked validation must reject reordered resolved global binders");
        assert_eq!(error.reason(), ValidationReason::Registry);
        assert_eq!(error.node(), Some(choose_abstraction));
    }

    #[test]
    fn linked_core_rejects_row_position_cardinality_before_later_node_type() {
        let mut fixture = LinkedCoreValidationFixture::compile(
            concat!(
                "pub identity<A : Type> : A -> A\n",
                "identity value = value\n",
            ),
            concat!(
                "import dependency (identity)\n",
                "main : Unit -> Int\n",
                "main () = identity(1)\n",
            ),
            &["identity"],
        );
        Arc::get_mut(&mut fixture.program.registry)
            .expect("the unchecked fixture owns the linked registry")
            .clear_global_parameter_positions_for_core_test();
        fixture
            .program
            .nodes
            .last_mut()
            .expect("the linked fixture has a root")
            .ty = Type::Bool;

        let error = fixture
            .validate()
            .expect_err("row/index cardinality must be authenticated before node types");
        assert_eq!(error.reason(), ValidationReason::Registry);
        assert_eq!(error.node(), None);
    }

    #[test]
    fn linked_core_sequential_bind_cannot_claim_a_resolved_global_row() {
        let mut fixture = LinkedCoreValidationFixture::compile(
            concat!(
                "pub identity<A : Type> : A -> A\n",
                "identity value = value\n",
            ),
            concat!(
                "import dependency (identity)\n",
                "main : Unit -> Int\n",
                "main () = identity(1)\n",
            ),
            &["identity"],
        );
        let (identity, _) = fixture.global("identity");
        let abstraction = linked_global_abstraction(&fixture.program, identity);
        let group_index = fixture
            .program
            .nodes
            .iter()
            .position(|node| {
                let PureExprKind::Computation(PureComputation::RecursiveBind(group)) = &node.kind
                else {
                    return false;
                };
                group.members().len() == 1 && group.members()[0].binder().id() == identity
            })
            .expect("the dependency global owns a singleton recursive group");
        let PureExprKind::Computation(PureComputation::RecursiveBind(group)) =
            fixture.program.nodes[group_index].kind.clone()
        else {
            unreachable!("the selected node is a recursive group")
        };
        let member = &group.members()[0];
        fixture.program.nodes[group_index].kind = PureExprKind::Computation(PureComputation::Bind(
            super::super::binding::BindingNode::new(
                member.binder().clone(),
                member.initializer(),
                group.body(),
            ),
        ));

        let error = fixture
            .validate()
            .expect_err("a sequential bind must not authenticate a linked global row");
        assert_eq!(error.reason(), ValidationReason::Registry);
        assert_eq!(error.node(), Some(abstraction));
    }

    #[test]
    fn linked_core_rejects_a_recursive_abstraction_shared_with_a_sequential_bind() {
        let mut fixture = LinkedCoreValidationFixture::compile(
            concat!(
                "pub identity<A : Type> : A -> A\n",
                "identity value = value\n",
            ),
            concat!(
                "import dependency (identity)\n",
                "main : Unit -> Int\n",
                "main () = identity(1)\n",
            ),
            &["identity"],
        );
        let (identity, _) = fixture.global("identity");
        let abstraction = linked_global_abstraction(&fixture.program, identity);
        let abstraction_node = &fixture.program.nodes[abstraction.value() as usize];
        let binder = TypedBinder::new(
            fixture.program.arena,
            BinderId::generated(u32::MAX),
            abstraction_node.ty.clone(),
            abstraction_node
                .origin
                .clone()
                .expect("the linked abstraction retains an origin"),
        );
        let previous_root = fixture.program.root;
        let root_node = &fixture.program.nodes[previous_root.value() as usize];
        let shared_root = NodeId::new(
            fixture.program.arena,
            u32::try_from(fixture.program.nodes.len()).expect("the fixture fits one arena"),
        );
        fixture.program.nodes.push(StoredNode {
            dialect: DialectId::PURE,
            effects: (),
            ty: root_node.ty.clone(),
            origin: root_node.origin.clone(),
            kind: PureExprKind::Computation(PureComputation::Bind(
                super::super::binding::BindingNode::new(binder, abstraction, previous_root),
            )),
        });
        fixture.program.root = shared_root;

        let error = fixture
            .validate()
            .expect_err("a resolved abstraction must have only its recursive owner");
        assert_eq!(error.reason(), ValidationReason::Registry);
        assert_eq!(error.node(), Some(abstraction));
    }

    fn linked_row_structure_fixture() -> LinkedCoreValidationFixture {
        LinkedCoreValidationFixture::compile(
            concat!(
                "pub type Holder<N : Type> = Holder(N)\n\n",
                "pub interface Witness<I : Type> {\n",
                "witness : I -> Bool\n",
                "}\n\n",
                "pub first<A : Type, B : Type> : A -> B -> A\n",
                "first left right = left\n\n",
                "pub second<C : Type> : C -> C\n",
                "second value = value\n\n",
                "pub plain : Unit -> Int\n",
                "plain () = 1\n",
            ),
            concat!(
                "import dependency (first, second, plain)\n",
                "main : Unit -> Int\n",
                "main () = first(second(1))(plain())\n",
            ),
            &["first", "second", "plain"],
        )
    }

    type GlobalRowShape = (BinderId, Vec<crate::types::TypeVariableId>);

    fn global_row_shape(registry: &crate::resolved::ResolvedRegistry) -> Vec<GlobalRowShape> {
        registry
            .global_parameter_rows()
            .iter()
            .map(|row| (row.owner(), row.parameters().to_vec()))
            .collect()
    }

    fn canonical_type_variable_shape(
        registry: &crate::resolved::ResolvedRegistry,
    ) -> HashMap<crate::types::TypeVariableId, crate::resolved::ResolvedTypeVariable> {
        registry
            .type_variables()
            .map(|parameter| (parameter.id, parameter.clone()))
            .collect()
    }

    #[test]
    fn linked_core_rejects_each_independent_registry_row_structure_mutation() {
        #[derive(Clone, Copy, Debug)]
        enum Case {
            Empty,
            GeneratedOwner,
            ForeignOwner,
            GeneratedParameter,
            ForeignParameter,
            MissingCanonical,
            NominalParameter,
            DuplicateWithinRow,
            DuplicateAcrossRows,
            WrongPosition,
            DuplicateOwner,
            MissingRow,
            ExtraUnconsumedRow,
            SurplusPosition,
        }

        for case in [
            Case::Empty,
            Case::GeneratedOwner,
            Case::ForeignOwner,
            Case::GeneratedParameter,
            Case::ForeignParameter,
            Case::MissingCanonical,
            Case::NominalParameter,
            Case::DuplicateWithinRow,
            Case::DuplicateAcrossRows,
            Case::WrongPosition,
            Case::DuplicateOwner,
            Case::MissingRow,
            Case::ExtraUnconsumedRow,
            Case::SurplusPosition,
        ] {
            let mut fixture = linked_row_structure_fixture();
            let (first_owner, first_parameters) = fixture.global("first");
            let (second_owner, second_parameters) = fixture.global("second");
            let (plain_owner, plain_parameters) = fixture.global("plain");
            assert!(plain_parameters.is_empty());
            let second_abstraction = linked_global_abstraction(&fixture.program, second_owner);
            let registry = fixture.program.registry.as_ref();
            let nominal_parameter = registry
                .nominal_parameter_entries()
                .flat_map(|(_, parameters)| parameters)
                .next()
                .expect("the structure fixture retains one nominal parameter")
                .id;
            let row_parameters = registry
                .global_parameter_rows()
                .iter()
                .flat_map(|row| row.parameters().iter().copied())
                .collect::<HashSet<_>>();
            let unowned_parameter = registry
                .type_variables()
                .map(|parameter| parameter.id)
                .find(|parameter| {
                    !row_parameters.contains(parameter) && *parameter != nominal_parameter
                })
                .expect("the structure fixture retains one interface-only parameter");
            let owner_module = first_owner
                .module()
                .expect("linked global owners are resolved");
            let foreign_module = ModuleId::new(owner_module.value().saturating_add(10_000));
            let generated_owner = BinderId::generated(u32::MAX);
            let foreign_owner = BinderId::resolved(foreign_module, 0);
            let generated_parameter = crate::types::TypeVariableId::generated(u32::MAX);
            let foreign_parameter = crate::types::TypeVariableId::resolved(foreign_module, 0);
            let registry = fixture.program.registry.as_ref();
            let original_rows = global_row_shape(registry);
            let original_positions = original_rows
                .iter()
                .enumerate()
                .map(|(position, (owner, _))| (*owner, position))
                .collect::<HashMap<_, _>>();
            let original_canonical = canonical_type_variable_shape(registry);
            assert_eq!(original_rows.len(), 2);
            assert_eq!(original_rows[0].0, first_owner);
            assert_eq!(original_rows[0].1, first_parameters);
            assert_eq!(original_rows[1].0, second_owner);
            assert_eq!(original_rows[1].1, second_parameters);

            let mut expected_rows = original_rows.clone();
            let mut expected_positions = original_positions.clone();
            let mut expected_canonical = original_canonical.clone();
            let mutation = match case {
                Case::Empty => {
                    expected_rows[0].1.clear();
                    CoreGlobalParameterRowMutationForTest::EmptyFirstRow
                }
                Case::GeneratedOwner => {
                    expected_rows[0].0 = generated_owner;
                    expected_positions.remove(&first_owner);
                    expected_positions.insert(generated_owner, 0);
                    CoreGlobalParameterRowMutationForTest::ReplaceFirstOwner(generated_owner)
                }
                Case::ForeignOwner => {
                    expected_rows[0].0 = foreign_owner;
                    expected_positions.remove(&first_owner);
                    expected_positions.insert(foreign_owner, 0);
                    CoreGlobalParameterRowMutationForTest::ReplaceFirstOwner(foreign_owner)
                }
                Case::GeneratedParameter => {
                    expected_rows[0].1[0] = generated_parameter;
                    CoreGlobalParameterRowMutationForTest::ReplaceFirstParameter(
                        generated_parameter,
                    )
                }
                Case::ForeignParameter => {
                    expected_rows[0].1[0] = foreign_parameter;
                    CoreGlobalParameterRowMutationForTest::ReplaceFirstParameter(foreign_parameter)
                }
                Case::MissingCanonical => {
                    assert!(expected_canonical.remove(&second_parameters[0]).is_some());
                    CoreGlobalParameterRowMutationForTest::RemoveCanonicalParameter(
                        second_parameters[0],
                    )
                }
                Case::NominalParameter => {
                    expected_rows[0].1[0] = nominal_parameter;
                    CoreGlobalParameterRowMutationForTest::ReplaceFirstParameter(nominal_parameter)
                }
                Case::DuplicateWithinRow => {
                    expected_rows[0].1[1] = expected_rows[0].1[0];
                    CoreGlobalParameterRowMutationForTest::DuplicateFirstParameter
                }
                Case::DuplicateAcrossRows => {
                    expected_rows[1].1[0] = expected_rows[0].1[0];
                    CoreGlobalParameterRowMutationForTest::DuplicateAcrossRows
                }
                Case::WrongPosition => {
                    expected_positions.insert(first_owner, 1);
                    expected_positions.insert(second_owner, 0);
                    CoreGlobalParameterRowMutationForTest::SwapFirstOwnerPositions
                }
                Case::DuplicateOwner => {
                    expected_rows[1].0 = first_owner;
                    expected_positions.remove(&second_owner);
                    expected_positions.insert(generated_owner, usize::MAX);
                    CoreGlobalParameterRowMutationForTest::DuplicateFirstOwner {
                        filler: generated_owner,
                    }
                }
                Case::MissingRow => {
                    let (removed_owner, _) = expected_rows
                        .pop()
                        .expect("the structure fixture has a last row");
                    expected_positions.remove(&removed_owner);
                    CoreGlobalParameterRowMutationForTest::RemoveLastRow
                }
                Case::ExtraUnconsumedRow => {
                    let position = expected_rows.len();
                    expected_rows.push((plain_owner, vec![unowned_parameter]));
                    expected_positions.insert(plain_owner, position);
                    CoreGlobalParameterRowMutationForTest::AppendRow {
                        owner: plain_owner,
                        parameter: unowned_parameter,
                    }
                }
                Case::SurplusPosition => {
                    expected_positions.insert(generated_owner, usize::MAX);
                    CoreGlobalParameterRowMutationForTest::AddSurplusPosition(generated_owner)
                }
            };
            assert_eq!(first_parameters.len(), 2);
            assert!(
                Arc::get_mut(&mut fixture.program.registry)
                    .expect("each unchecked fixture uniquely owns its registry")
                    .corrupt_global_parameter_rows_for_core_test(mutation)
            );

            let registry = fixture.program.registry.as_ref();
            assert_eq!(
                global_row_shape(registry),
                expected_rows,
                "the mutation must change exactly its intended ordered row cells: {case:?}",
            );
            assert_eq!(
                registry.global_parameter_position_count(),
                expected_positions.len(),
                "the mutation must retain the exact intended index cardinality: {case:?}",
            );
            let position_probes = original_positions
                .keys()
                .chain(expected_positions.keys())
                .copied()
                .chain([plain_owner, generated_owner, foreign_owner])
                .collect::<HashSet<_>>();
            for owner in position_probes {
                assert_eq!(
                    registry.global_parameter_position_for_core_test(owner),
                    expected_positions.get(&owner).copied(),
                    "the mutation must preserve every unrelated raw owner position: {case:?}",
                );
                let expected_row = expected_positions
                    .get(&owner)
                    .and_then(|position| expected_rows.get(*position))
                    .filter(|(row_owner, _)| *row_owner == owner);
                assert_eq!(
                    registry
                        .global_parameter_row(owner)
                        .map(|row| { (row.owner(), row.parameters().to_vec()) }),
                    expected_row.cloned(),
                    "the mutation must preserve every unrelated exact owner lookup: {case:?}",
                );
            }
            assert_eq!(
                canonical_type_variable_shape(registry),
                expected_canonical,
                "the mutation must preserve every unrelated canonical record: {case:?}",
            );

            let error = fixture
                .validate()
                .expect_err("every structural mutation must reject linked Core");
            assert_eq!(error.reason(), ValidationReason::Registry, "{case:?}");
            assert_eq!(
                error.node(),
                matches!(case, Case::MissingRow).then_some(second_abstraction),
                "{case:?}",
            );
        }
    }

    fn linked_fixture_sources(fixture: &LinkedCoreValidationFixture) -> Vec<&SourceFile> {
        fixture
            .graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect()
    }

    fn nominal_parameter_owner_fixture(
        fixture: &LinkedCoreValidationFixture,
    ) -> RegistryParameterOwners {
        fixture
            .program
            .registry
            .nominal_parameter_entries()
            .flat_map(|(owner, parameters)| {
                parameters
                    .iter()
                    .map(move |parameter| (parameter.id, RegistryParameterOwner::Nominal(owner)))
            })
            .collect()
    }

    fn kind_node_count(root: &Kind) -> usize {
        let mut count = 0_usize;
        let mut pending = vec![root];
        while let Some(kind) = pending.pop() {
            count += 1;
            if let Kind::Arrow(domain, codomain) = kind {
                pending.push(codomain);
                pending.push(domain);
            }
        }
        count
    }

    struct ConsumingModuleValidationAttempt {
        result: Result<ValidatedProgram, ValidationError>,
        type_work: usize,
    }

    fn run_module_validation_phases_for_test(
        validator: &mut Validator<'_, '_>,
    ) -> Result<(), ValidationError> {
        let nominal_parameter_owners = validator.validate_registry()?;
        let authenticated = HashSet::new();
        validator.validate_envelopes(&authenticated)?;
        validator.validate_graph()?;
        let abstraction_owners = validator.collect_binders(&authenticated)?;
        let type_binders =
            validator.collect_type_binders(&nominal_parameter_owners, &abstraction_owners)?;
        validator.validate_node_types(&nominal_parameter_owners, &type_binders, &authenticated)?;
        validator.validate_scopes()?;
        validator.validate_type_scopes()
    }

    fn validate_modules_with_initial_type_work_for_test(
        program: UnvalidatedProgram,
        sources: &[&SourceFile],
        module_sources: &[(ModuleId, SourceId)],
        initial_type_work: usize,
    ) -> ConsumingModuleValidationAttempt {
        let mut validator = match Validator::new_modules(&program, sources, module_sources) {
            Ok(validator) => validator,
            Err(error) => {
                program.discard_iteratively();
                return ConsumingModuleValidationAttempt {
                    result: Err(error),
                    type_work: 0,
                };
            }
        };
        if let Err(error) = validator.charge_type_work(initial_type_work) {
            let type_work = validator.type_work.get();
            drop(validator);
            program.discard_iteratively();
            return ConsumingModuleValidationAttempt {
                result: Err(error),
                type_work,
            };
        }
        if let Err(error) = run_module_validation_phases_for_test(&mut validator) {
            let type_work = validator.type_work.get();
            drop(validator);
            program.discard_iteratively();
            return ConsumingModuleValidationAttempt {
                result: Err(error),
                type_work,
            };
        }
        let type_work = validator.type_work.get();
        drop(validator);

        let (registry, method_evidence, method_evidence_anchors, arena, stored_nodes, root) =
            program.into_parts();
        let mut nodes = Vec::with_capacity(stored_nodes.len());
        for (index, stored) in stored_nodes.into_iter().enumerate() {
            let node = match node_id(arena, index) {
                Ok(node) => node,
                Err(error) => {
                    return ConsumingModuleValidationAttempt {
                        result: Err(error),
                        type_work,
                    };
                }
            };
            let Some(origin) = stored.origin else {
                return ConsumingModuleValidationAttempt {
                    result: Err(ValidationError::new(
                        ValidationReason::Provenance,
                        Some(node),
                    )),
                    type_work,
                };
            };
            nodes.push(TypedExpr {
                effects: (),
                ty: stored.ty,
                origin,
                kind: stored.kind,
            });
        }

        ConsumingModuleValidationAttempt {
            result: Ok(ValidatedProgram::new(PureProgram::new(
                registry,
                method_evidence,
                method_evidence_anchors,
                arena,
                nodes,
                root,
            ))),
            type_work,
        }
    }

    #[derive(Debug, Eq, PartialEq)]
    struct CompleteModuleValidationWork {
        ordinary_registry: usize,
        row_structure: usize,
        envelopes: usize,
        graph: usize,
        ordinary_binders: usize,
        initializer_owners: usize,
        resolved_matching: usize,
        generated_matching: usize,
        node_types: usize,
        term_scopes: usize,
        type_scopes: usize,
    }

    impl CompleteModuleValidationWork {
        fn total(&self) -> usize {
            self.ordinary_registry
                + self.row_structure
                + self.envelopes
                + self.graph
                + self.ordinary_binders
                + self.initializer_owners
                + self.resolved_matching
                + self.generated_matching
                + self.node_types
                + self.term_scopes
                + self.type_scopes
        }
    }

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    struct LinkedValidationTerms {
        rows: usize,
        resolved_parameters: usize,
        resolved_kind_nodes: usize,
        initializer_owners: usize,
        generated_parameters: usize,
        generated_kind_nodes: usize,
    }

    impl LinkedValidationTerms {
        fn row_structure(self) -> usize {
            2 * self.rows + 2 * self.resolved_parameters
        }

        fn resolved_matching(self) -> usize {
            2 * self.resolved_parameters + self.resolved_kind_nodes + self.rows
        }

        fn generated_matching(self) -> usize {
            self.generated_parameters + self.generated_kind_nodes
        }
    }

    fn linked_validation_terms(program: &UnvalidatedProgram) -> LinkedValidationTerms {
        let rows = program.registry.global_parameter_rows();
        let resolved_parameters = rows.iter().map(|row| row.parameters().len()).sum();
        let resolved_kind_nodes = rows
            .iter()
            .flat_map(|row| row.parameters())
            .map(|parameter| {
                kind_node_count(
                    &program
                        .registry
                        .type_variable(*parameter)
                        .expect("each row parameter has a canonical record")
                        .kind,
                )
            })
            .sum();
        let initializer_owners = program
            .nodes
            .iter()
            .filter_map(|node| {
                let PureExprKind::Computation(PureComputation::RecursiveBind(group)) = &node.kind
                else {
                    return None;
                };
                Some(
                    group
                        .members()
                        .iter()
                        .filter(|member| {
                            matches!(
                                program.nodes[member
                                    .initializer()
                                    .index()
                                    .expect("initializer index fits")]
                                .kind,
                                PureExprKind::Computation(PureComputation::TypeAbstraction(_))
                            )
                        })
                        .count(),
                )
            })
            .sum();
        let mut generated_parameters = 0;
        let mut generated_kind_nodes = 0;
        for node in &program.nodes {
            let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                &node.kind
            else {
                continue;
            };
            for (parameter, kind) in abstraction.parameters() {
                if matches!(parameter, crate::types::TypeVariableId::Generated(_)) {
                    generated_parameters += 1;
                    generated_kind_nodes += kind_node_count(kind);
                }
            }
        }
        LinkedValidationTerms {
            rows: rows.len(),
            resolved_parameters,
            resolved_kind_nodes,
            initializer_owners,
            generated_parameters,
            generated_kind_nodes,
        }
    }

    fn arrow_kind(depth: usize) -> Kind {
        let mut kind = Kind::Type;
        for _ in 0..depth {
            kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
        }
        kind
    }

    fn linked_complete_validation_fixture(
        generated_kind_depth: usize,
        generated_type_depth: usize,
        generated_origin_depth: usize,
    ) -> LinkedCoreValidationFixture {
        let mut fixture = LinkedCoreValidationFixture::compile(
            concat!(
                "pub relay<F : Type -> Type> : F<Unit> -> F<Unit>\n",
                "relay value = value\n",
            ),
            concat!(
                "import dependency (relay)\n",
                "main : Unit -> Unit\n",
                "main () = ()\n",
            ),
            &["relay"],
        );
        let (owner, parameters) = fixture.global("relay");
        let [resolved_parameter] = parameters else {
            panic!("the cumulative fixture retains one resolved parameter");
        };
        let resolved_parameter = *resolved_parameter;
        let resolved_kind = fixture
            .program
            .registry
            .type_variable(resolved_parameter)
            .expect("the resolved parameter has one canonical record")
            .kind
            .clone();
        let owner_module = owner
            .module()
            .expect("the resolved global owner belongs to a module");
        let owner_source = fixture
            .graph
            .modules()
            .iter()
            .find(|module| module.id() == owner_module)
            .expect("the owner module belongs to the fixture graph")
            .source();
        let owner_origin = Origin::Source(
            owner_source
                .span(ByteRange::new(0, 1).expect("the owner range is ordered"))
                .expect("the owner span belongs to its source"),
        );
        let generated_origin = generated_origin(owner_source, generated_origin_depth);

        let mut builder = CoreBuilder::with_registry(Arc::clone(&fixture.program.registry));
        builder
            .reserve_resolved_binders([owner])
            .expect("the authentic resolved owner reserves once");
        let resolved_value_type = Type::Application(
            Box::new(Type::Variable(resolved_parameter)),
            Box::new(Type::Unit),
        );
        let resolved_argument = builder
            .binder(resolved_value_type.clone(), owner_origin.clone())
            .expect("the resolved function argument fits");
        let resolved_body = builder
            .variable(
                resolved_argument.id(),
                resolved_value_type.clone(),
                owner_origin.clone(),
            )
            .expect("the resolved function body fits");
        let resolved_function_type = Type::Function(
            Box::new(resolved_value_type.clone()),
            Box::new(resolved_value_type),
        );
        let resolved_function = builder
            .function(
                resolved_argument,
                resolved_body,
                resolved_function_type.clone(),
                owner_origin.clone(),
            )
            .expect("the resolved function fits");
        let resolved_scheme = Type::Forall(
            Box::new([(resolved_parameter, resolved_kind.clone())]),
            Box::new(resolved_function_type),
        );
        let resolved_abstraction = builder
            .type_abstraction(
                vec![(resolved_parameter, resolved_kind)],
                resolved_function,
                resolved_scheme.clone(),
                owner_origin.clone(),
            )
            .expect("the resolved abstraction fits");
        let global = builder
            .resolved_binder(owner, resolved_scheme, owner_origin.clone())
            .expect("the authentic resolved owner materializes once");

        let generated_value_type = function_type(generated_type_depth);
        let generated_argument = builder
            .binder(generated_value_type.clone(), generated_origin.clone())
            .expect("the generated function argument fits");
        let generated_body = builder
            .variable(
                generated_argument.id(),
                generated_value_type.clone(),
                generated_origin.clone(),
            )
            .expect("the generated function body fits");
        let generated_body_type = Type::Function(
            Box::new(generated_value_type.clone()),
            Box::new(generated_value_type),
        );
        let generated_body = builder
            .function(
                generated_argument,
                generated_body,
                generated_body_type.clone(),
                generated_origin.clone(),
            )
            .expect("the generated function fits");
        let generated_parameter = crate::types::TypeVariableId::generated(90_000);
        let generated_kind = arrow_kind(generated_kind_depth);
        let generated_scheme = Type::Forall(
            Box::new([(generated_parameter, generated_kind.clone())]),
            Box::new(generated_body_type),
        );
        let generated_abstraction = builder
            .type_abstraction(
                vec![(generated_parameter, generated_kind)],
                generated_body,
                generated_scheme.clone(),
                generated_origin.clone(),
            )
            .expect("the generated abstraction fits");
        let root = builder
            .recursive_binding(
                vec![(global, resolved_abstraction)],
                generated_abstraction,
                generated_scheme,
                generated_origin,
            )
            .expect("the cumulative recursive group fits");
        fixture.program = builder
            .finish(root)
            .expect("the cumulative validation fixture finishes");
        fixture
    }

    fn run_complete_module_validation_phases(
        validator: &mut Validator<'_, '_>,
        terms: LinkedValidationTerms,
    ) -> Result<CompleteModuleValidationWork, ValidationError> {
        let mut previous = validator.type_work.get();
        let nominal_parameter_owners = validator.validate_registry()?;
        let registry_total = validator.type_work.get() - previous;
        let ordinary_registry = registry_total
            .checked_sub(terms.row_structure())
            .expect("row structure is part of registry work");

        previous = validator.type_work.get();
        let authenticated = HashSet::new();
        validator.validate_envelopes(&authenticated)?;
        let envelopes = validator.type_work.get() - previous;

        previous = validator.type_work.get();
        validator.validate_graph()?;
        let graph = validator.type_work.get() - previous;

        previous = validator.type_work.get();
        let abstraction_owners = validator.collect_binders(&authenticated)?;
        let binder_total = validator.type_work.get() - previous;
        let ordinary_binders = binder_total
            .checked_sub(terms.initializer_owners)
            .expect("initializer owners are part of binder collection");

        previous = validator.type_work.get();
        let type_binders =
            validator.collect_type_binders(&nominal_parameter_owners, &abstraction_owners)?;
        assert_eq!(
            validator.type_work.get() - previous,
            terms.resolved_matching() + terms.generated_matching(),
            "resolved and generated matching are the complete type-binder phase",
        );

        previous = validator.type_work.get();
        validator.validate_node_types(&nominal_parameter_owners, &type_binders, &authenticated)?;
        let node_types = validator.type_work.get() - previous;

        previous = validator.type_work.get();
        validator.validate_scopes()?;
        let term_scopes = validator.type_work.get() - previous;

        previous = validator.type_work.get();
        validator.validate_type_scopes()?;
        let type_scopes = validator.type_work.get() - previous;

        Ok(CompleteModuleValidationWork {
            ordinary_registry,
            row_structure: terms.row_structure(),
            envelopes,
            graph,
            ordinary_binders,
            initializer_owners: terms.initializer_owners,
            resolved_matching: terms.resolved_matching(),
            generated_matching: terms.generated_matching(),
            node_types,
            term_scopes,
            type_scopes,
        })
    }

    #[test]
    fn complete_linked_core_validation_work_is_additive_exact_and_retryable() {
        const S: usize = 1;
        const R: usize = 1;
        const K_R: usize = 3;
        const O: usize = 1;
        const G: usize = 1;
        const K_G: usize = 3;
        // The ordinary module-registry scan visits the one canonical global
        // parameter record before row authentication begins.
        const CANONICAL_REGISTRY_RECORDS: usize = R;
        const ROW_STRUCTURE: usize = 2 * S + 2 * R;
        // The seven stored envelopes contain 42 Type/binder-Kind cells:
        // 3 + 7 + 12 for the resolved value/function/scheme, 1 + 3 + 8 for
        // the generated value/function/scheme, and 8 for the group envelope.
        const ENVELOPE_TYPE_AND_KIND_CELLS: usize = 42;
        const GRAPH_TYPE_WORK: usize = 0;
        // Ordinary binder admission revisits the resolved argument (3), the
        // resolved global scheme (12), and the generated argument (1).
        const BINDER_TYPE_AND_KIND_CELLS: usize = 16;
        // Resolved matching fuses R identity-class visits, K_R canonical Kind
        // comparisons, and R ordered-row identity visits. The final S is only
        // a scalar consumed-row count; the validator retains no S-cell set.
        const RESOLVED_MATCHING: usize = 2 * R + K_R + S;
        const GENERATED_MATCHING: usize = G + K_G;
        // Per-node Kind synthesis and structural agreement are independently
        // additive: resolved variable/function/abstraction 10 + 22 + 32,
        // generated variable/function/abstraction 3 + 8 + 18, and the
        // recursive root 34.
        const RESOLVED_VARIABLE_NODE_WORK: usize = 10;
        const RESOLVED_FUNCTION_NODE_WORK: usize = 22;
        const RESOLVED_ABSTRACTION_NODE_WORK: usize = 32;
        const GENERATED_VARIABLE_NODE_WORK: usize = 3;
        const GENERATED_FUNCTION_NODE_WORK: usize = 8;
        const GENERATED_ABSTRACTION_NODE_WORK: usize = 18;
        const RECURSIVE_ROOT_NODE_WORK: usize = 34;
        const NODE_KIND_AND_TYPE_WORK: usize = RESOLVED_VARIABLE_NODE_WORK
            + RESOLVED_FUNCTION_NODE_WORK
            + RESOLVED_ABSTRACTION_NODE_WORK
            + GENERATED_VARIABLE_NODE_WORK
            + GENERATED_FUNCTION_NODE_WORK
            + GENERATED_ABSTRACTION_NODE_WORK
            + RECURSIVE_ROOT_NODE_WORK;
        // Graph and term-scope analysis retain no Type-work cells for this
        // closed tree. Type-scope analysis consumes 42 envelope cells, 16
        // binder cells, and 5 free-variable set entries.
        const TERM_SCOPE_TYPE_WORK: usize = 0;
        const TYPE_SCOPE_WORK: usize = 42 + 16 + 5;
        const EXPECTED: CompleteModuleValidationWork = CompleteModuleValidationWork {
            ordinary_registry: CANONICAL_REGISTRY_RECORDS,
            row_structure: ROW_STRUCTURE,
            envelopes: ENVELOPE_TYPE_AND_KIND_CELLS,
            graph: GRAPH_TYPE_WORK,
            ordinary_binders: BINDER_TYPE_AND_KIND_CELLS,
            initializer_owners: O,
            resolved_matching: RESOLVED_MATCHING,
            generated_matching: GENERATED_MATCHING,
            node_types: NODE_KIND_AND_TYPE_WORK,
            term_scopes: TERM_SCOPE_TYPE_WORK,
            type_scopes: TYPE_SCOPE_WORK,
        };

        assert_eq!(CORE_VALIDATION_TYPE_WORK_LIMIT, 983_040);
        let fixture = linked_complete_validation_fixture(1, 0, 1);
        let sources = linked_fixture_sources(&fixture);
        let terms = linked_validation_terms(&fixture.program);
        assert_eq!(
            terms,
            LinkedValidationTerms {
                rows: S,
                resolved_parameters: R,
                resolved_kind_nodes: K_R,
                initializer_owners: O,
                generated_parameters: G,
                generated_kind_nodes: K_G,
            }
        );

        let mut measured =
            Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
                .expect("the measured module/source relation is canonical");
        assert_eq!(
            run_complete_module_validation_phases(&mut measured, terms)
                .expect("the measured cumulative fixture validates"),
            EXPECTED,
        );

        let exact_work = EXPECTED.total();
        assert_eq!(exact_work, 264);
        let mut exact = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the exact module/source relation is canonical");
        exact
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - exact_work)
            .expect("the exact cumulative precharge fits");
        assert_eq!(
            run_complete_module_validation_phases(&mut exact, terms)
                .expect("the complete additive allowance fits"),
            EXPECTED,
        );
        assert_eq!(exact.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);

        let rows_before = global_row_shape(&fixture.program.registry);
        let owners_before = Arc::strong_count(&fixture.program.registry);
        let mut short = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the one-short module/source relation is canonical");
        short
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - (exact_work - 1))
            .expect("the one-short cumulative precharge fits");
        let error = run_complete_module_validation_phases(&mut short, terms)
            .expect_err("one missing cumulative unit rejects without a validated capability");
        assert_eq!(error.reason(), ValidationReason::Resource);
        assert_eq!(short.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);
        drop(short);
        assert_eq!(Arc::strong_count(&fixture.program.registry), owners_before);
        assert_eq!(global_row_shape(&fixture.program.registry), rows_before);

        let mut retry = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the retry module/source relation is canonical");
        retry
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - exact_work)
            .expect("the retry cumulative precharge fits");
        assert_eq!(
            run_complete_module_validation_phases(&mut retry, terms)
                .expect("the same fixture succeeds with its exact allowance on retry"),
            EXPECTED,
        );
    }

    #[test]
    fn deep_linked_core_validator_states_are_disposed_on_a_small_stack() {
        const KIND_DEPTH: usize = 4_096;
        const TYPE_DEPTH: usize = super::super::dialect::CORE_PAYLOAD_DEPTH_LIMIT - 2;
        const ORIGIN_DEPTH: usize = super::super::dialect::CORE_PAYLOAD_DEPTH_LIMIT;
        const DEEP_KIND_NODES: usize = 2 * KIND_DEPTH + 1;

        fn validate_fixture_with_initial_type_work(
            fixture: LinkedCoreValidationFixture,
            initial_type_work: usize,
        ) -> ConsumingModuleValidationAttempt {
            let LinkedCoreValidationFixture {
                directory,
                graph,
                program,
                module_sources,
                globals,
            } = fixture;
            let sources = graph
                .modules()
                .iter()
                .map(|module| module.source())
                .collect::<Vec<_>>();
            let attempt = validate_modules_with_initial_type_work_for_test(
                program,
                &sources,
                &module_sources,
                initial_type_work,
            );
            drop(sources);
            drop(globals);
            drop(graph);
            drop(directory);
            attempt
        }

        std::thread::Builder::new()
            .name("deep-linked-core-validation-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let accepted_fixture =
                    linked_complete_validation_fixture(KIND_DEPTH, TYPE_DEPTH, ORIGIN_DEPTH);
                let sources = linked_fixture_sources(&accepted_fixture);
                let terms = linked_validation_terms(&accepted_fixture.program);
                assert_eq!(terms.rows, 1);
                assert_eq!(terms.resolved_parameters, 1);
                assert_eq!(terms.resolved_kind_nodes, 3);
                assert_eq!(terms.initializer_owners, 1);
                assert_eq!(terms.generated_parameters, 1);
                assert_eq!(terms.generated_kind_nodes, DEEP_KIND_NODES);
                assert_eq!(terms.row_structure(), 4);
                assert_eq!(terms.resolved_matching(), 6);
                assert_eq!(terms.generated_matching(), DEEP_KIND_NODES + 1);

                let mut measured = Validator::new_modules(
                    &accepted_fixture.program,
                    &sources,
                    &accepted_fixture.module_sources,
                )
                .expect("the deep measured relation is canonical");
                let expected = run_complete_module_validation_phases(&mut measured, terms)
                    .expect("the deep row-bearing validator state is accepted");
                let exact_work = expected.total();
                assert_eq!(measured.type_work.get(), exact_work);
                assert!(exact_work < CORE_VALIDATION_TYPE_WORK_LIMIT);
                drop(measured);
                drop(sources);

                let accepted_registry = Arc::clone(&accepted_fixture.program.registry);
                let accepted_rows = global_row_shape(&accepted_registry);
                let accepted = validate_fixture_with_initial_type_work(
                    accepted_fixture,
                    CORE_VALIDATION_TYPE_WORK_LIMIT - exact_work,
                );
                assert_eq!(accepted.type_work, CORE_VALIDATION_TYPE_WORK_LIMIT);
                let accepted = accepted
                    .result
                    .expect("the owned deep fixture validates with its exact allowance");
                assert!(Arc::ptr_eq(accepted.registry(), &accepted_registry));
                assert_eq!(global_row_shape(accepted.registry()), accepted_rows);
                drop(accepted);
                drop(accepted_registry);

                let rejected_fixture =
                    linked_complete_validation_fixture(KIND_DEPTH, TYPE_DEPTH, ORIGIN_DEPTH);
                assert_eq!(linked_validation_terms(&rejected_fixture.program), terms,);
                let rejected_registry = Arc::downgrade(&rejected_fixture.program.registry);
                let rejected = validate_fixture_with_initial_type_work(
                    rejected_fixture,
                    CORE_VALIDATION_TYPE_WORK_LIMIT - (exact_work - 1),
                );
                assert_eq!(rejected.type_work, CORE_VALIDATION_TYPE_WORK_LIMIT);
                assert_eq!(
                    rejected
                        .result
                        .expect_err("one missing unit must consume and reject the deep program")
                        .reason(),
                    ValidationReason::Resource,
                );
                assert!(
                    rejected_registry.upgrade().is_none(),
                    "rejection must release the program's registry and its retained row",
                );

                let retry_fixture =
                    linked_complete_validation_fixture(KIND_DEPTH, TYPE_DEPTH, ORIGIN_DEPTH);
                assert_eq!(linked_validation_terms(&retry_fixture.program), terms);
                let retry_registry = Arc::clone(&retry_fixture.program.registry);
                let retry_rows = global_row_shape(&retry_registry);
                let retry = validate_fixture_with_initial_type_work(
                    retry_fixture,
                    CORE_VALIDATION_TYPE_WORK_LIMIT - exact_work,
                );
                assert_eq!(retry.type_work, CORE_VALIDATION_TYPE_WORK_LIMIT);
                let retry = retry
                    .result
                    .expect("a fresh owned deep fixture retries with its exact allowance");
                assert!(Arc::ptr_eq(retry.registry(), &retry_registry));
                assert_eq!(global_row_shape(retry.registry()), retry_rows);
                drop(retry);
                drop(retry_registry);
            })
            .expect("the deep linked validation worker should start")
            .join()
            .expect("accepted and rejected deep row states dismantle on 256 KiB");
    }

    #[test]
    fn linked_core_row_structure_work_is_exact_atomic_and_retryable() {
        let fixture = linked_row_structure_fixture();
        let sources = linked_fixture_sources(&fixture);
        let nominal_owners = nominal_parameter_owner_fixture(&fixture);
        let rows = fixture.program.registry.global_parameter_rows();
        let row_count = rows.len();
        let parameter_count = rows.iter().map(|row| row.parameters().len()).sum::<usize>();
        // Each row and parameter has one visit and one uniqueness cell.
        let expected_work = 2 * row_count + 2 * parameter_count;

        let exact = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the fixture module/source relation is canonical");
        exact
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - expected_work)
            .expect("the exact row-structure allowance fits");
        exact
            .validate_global_parameter_rows(&nominal_owners)
            .expect("row visits and uniqueness storage fit exactly");
        assert_eq!(exact.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);

        let short = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the one-short relation is canonical");
        short
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - (expected_work - 1))
            .expect("the one-short row allowance fits");
        let error = short
            .validate_global_parameter_rows(&nominal_owners)
            .expect_err("row storage and visits must precharge atomically");
        assert_eq!(error.reason(), ValidationReason::Resource);
        assert_eq!(
            short.type_work.get(),
            CORE_VALIDATION_TYPE_WORK_LIMIT - (expected_work - 1),
            "the aggregate row precharge publishes no partial ledger work",
        );

        let retry = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the retry relation is canonical");
        retry
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - expected_work)
            .expect("the retry exact allowance fits");
        retry
            .validate_global_parameter_rows(&nominal_owners)
            .expect("a failed attempt publishes no row-validation state");
    }

    #[test]
    fn linked_core_owner_map_and_scalar_row_consumption_are_exact_and_retryable() {
        let fixture = linked_row_structure_fixture();
        let sources = linked_fixture_sources(&fixture);
        let nominal_owners = nominal_parameter_owner_fixture(&fixture);
        let row_count = fixture.program.registry.global_parameter_rows().len();
        let parameter_count = fixture
            .program
            .registry
            .global_parameter_rows()
            .iter()
            .map(|row| row.parameters().len())
            .sum::<usize>();

        let mut direct = Validator::new(&fixture.program, &sources);
        let direct_owners = direct
            .collect_binders(&HashSet::new())
            .expect("the direct scan validates the same binder metadata");
        assert!(direct_owners.is_empty());
        let direct_work = direct.type_work.get();

        let mut measured =
            Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
                .expect("the measured relation is canonical");
        let measured_owners = measured
            .collect_binders(&HashSet::new())
            .expect("the linked scan retains immediate recursive owners");
        let owner_count = measured_owners.len();
        assert_eq!(measured.type_work.get() - direct_work, owner_count);

        let exact_owner_work = direct_work + owner_count;
        let mut exact_owner =
            Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
                .expect("the exact owner relation is canonical");
        exact_owner
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - exact_owner_work)
            .expect("the exact owner-map allowance fits");
        assert_eq!(
            exact_owner
                .collect_binders(&HashSet::new())
                .expect("each owner entry is charged before retention")
                .len(),
            owner_count,
        );
        assert_eq!(exact_owner.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);

        let mut short_owner =
            Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
                .expect("the one-short owner relation is canonical");
        short_owner
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - (exact_owner_work - 1))
            .expect("the one-short owner-map allowance fits");
        let error = short_owner
            .collect_binders(&HashSet::new())
            .expect_err("one missing owner-entry unit must reject before publication");
        assert_eq!(error.reason(), ValidationReason::Resource);
        assert_eq!(short_owner.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);

        // Linked resolved matching charges one class visit, canonical Kind
        // comparison, and row-identity comparison per parameter, then one
        // scalar consumption unit per row. It retains no S-cell bitmap/set.
        let matching_work = 3 * parameter_count + row_count;
        let mut exact_match =
            Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
                .expect("the exact matching relation is canonical");
        let exact_match_owners = exact_match
            .collect_binders(&HashSet::new())
            .expect("the exact matching fixture retains owners");
        exact_match
            .charge_type_work(
                CORE_VALIDATION_TYPE_WORK_LIMIT - exact_match.type_work.get() - matching_work,
            )
            .expect("the exact row-matching allowance fits");
        exact_match
            .collect_type_binders(&nominal_owners, &exact_match_owners)
            .expect("identity, Kind, and scalar consumption work fits exactly");
        assert_eq!(exact_match.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);

        let mut short_match =
            Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
                .expect("the one-short matching relation is canonical");
        let short_match_owners = short_match
            .collect_binders(&HashSet::new())
            .expect("the one-short matching fixture retains owners");
        short_match
            .charge_type_work(
                CORE_VALIDATION_TYPE_WORK_LIMIT - short_match.type_work.get() - (matching_work - 1),
            )
            .expect("the one-short matching allowance fits");
        let error = short_match
            .collect_type_binders(&nominal_owners, &short_match_owners)
            .expect_err("the final scalar consumption unit is required");
        assert_eq!(error.reason(), ValidationReason::Resource);
        assert_eq!(short_match.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);

        let mut retry = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the retry relation is canonical");
        let retry_owners = retry
            .collect_binders(&HashSet::new())
            .expect("the retry fixture retains owners");
        retry
            .collect_type_binders(&nominal_owners, &retry_owners)
            .expect("failed owner and consumption attempts publish no retained state");
    }

    #[test]
    fn linked_arrow_kind_row_matching_work_is_exact_atomic_and_retryable() {
        let fixture = LinkedCoreValidationFixture::compile(
            concat!(
                "pub relay<F : Type -> Type, A : Type> : F<A> -> F<A>\n",
                "relay value = value\n",
            ),
            concat!(
                "import dependency (relay)\n",
                "main : Unit -> Unit\n",
                "main () = ()\n",
            ),
            &["relay"],
        );
        let sources = linked_fixture_sources(&fixture);
        let nominal_owners = nominal_parameter_owner_fixture(&fixture);
        let rows = fixture.program.registry.global_parameter_rows();
        let row_count = rows.len();
        let parameter_count = rows.iter().map(|row| row.parameters().len()).sum::<usize>();
        let canonical_kind_work = rows
            .iter()
            .flat_map(|row| row.parameters())
            .map(|parameter| {
                let canonical = fixture
                    .program
                    .registry
                    .type_variable(*parameter)
                    .expect("each retained row parameter has a canonical record");
                kind_node_count(&canonical.kind)
            })
            .sum::<usize>();
        assert_eq!(parameter_count, 2);
        assert_eq!(
            canonical_kind_work, 4,
            "the fixture includes one Arrow Kind"
        );

        // R class visits, K_R canonical Kind nodes, R row-identity visits,
        // and S scalar row consumptions: 2R + K_R + S.
        let matching_work = 2 * parameter_count + canonical_kind_work + row_count;
        let mut exact = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the exact Arrow-Kind relation is canonical");
        let exact_owners = exact
            .collect_binders(&HashSet::new())
            .expect("the exact Arrow-Kind fixture retains its owner");
        exact
            .charge_type_work(
                CORE_VALIDATION_TYPE_WORK_LIMIT - exact.type_work.get() - matching_work,
            )
            .expect("the exact Arrow-Kind matching allowance fits");
        exact
            .collect_type_binders(&nominal_owners, &exact_owners)
            .expect("the exact Arrow-Kind matching work fits");
        assert_eq!(exact.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);

        let mut short = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the one-short Arrow-Kind relation is canonical");
        let short_owners = short
            .collect_binders(&HashSet::new())
            .expect("the one-short Arrow-Kind fixture retains its owner");
        short
            .charge_type_work(
                CORE_VALIDATION_TYPE_WORK_LIMIT - short.type_work.get() - (matching_work - 1),
            )
            .expect("the one-short Arrow-Kind matching allowance fits");
        let error = short
            .collect_type_binders(&nominal_owners, &short_owners)
            .expect_err("one missing scalar consumption unit must reject");
        assert_eq!(error.reason(), ValidationReason::Resource);
        assert_eq!(short.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);

        let mut retry = Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
            .expect("the Arrow-Kind retry relation is canonical");
        let retry_owners = retry
            .collect_binders(&HashSet::new())
            .expect("the Arrow-Kind retry retains its owner");
        retry
            .collect_type_binders(&nominal_owners, &retry_owners)
            .expect("a failed Arrow-Kind attempt publishes no retained state");
    }

    #[test]
    fn linked_generated_only_matching_has_no_identity_class_delta() {
        let file = SourceFile::new("generated-work.ash", "Generated")
            .expect("the generated-work source fits");
        let origin = Origin::Source(
            file.span(ByteRange::new(0, 9).expect("the generated-work range is ordered"))
                .expect("the generated-work span fits"),
        );
        let first = crate::types::TypeVariableId::generated(73);
        let second = crate::types::TypeVariableId::generated(74);
        let parameters = vec![
            (first, Kind::Type),
            (
                second,
                Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
            ),
        ];
        let scheme_parameters = parameters.clone().into_boxed_slice();
        let mut builder = CoreBuilder::new();
        let body = builder
            .unit(Type::Unit, origin.clone())
            .expect("the generated-work body fits");
        let root = builder
            .type_abstraction(
                parameters,
                body,
                Type::Forall(scheme_parameters, Box::new(Type::Unit)),
                origin,
            )
            .expect("the generated-work abstraction fits");
        let program = builder
            .finish(root)
            .expect("the generated-work program finishes");
        let root_node = &program.nodes[root.index().expect("the generated-work root index fits")];
        let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
            &root_node.kind
        else {
            panic!("the generated-work root remains a type abstraction");
        };
        let parameter_count = abstraction.parameters().len();
        let kind_work = abstraction
            .parameters()
            .iter()
            .map(|(_, kind)| kind_node_count(kind))
            .sum::<usize>();
        let expected_work = parameter_count + kind_work;
        let sources = [&file];
        let module_sources = [(ModuleId::new(7_732), file.id())];
        let nominal_owners = HashMap::new();
        let abstraction_owners = CoreAbstractionOwners::new();

        let direct = Validator::new(&program, &sources);
        direct
            .collect_type_binders(&nominal_owners, &abstraction_owners)
            .expect("direct generated-only binders are structurally valid");
        assert_eq!(direct.type_work.get(), expected_work);

        let measured = Validator::new_modules(&program, &sources, &module_sources)
            .expect("the measured generated-only relation is canonical");
        measured
            .collect_type_binders(&nominal_owners, &abstraction_owners)
            .expect("linked generated-only binders are structurally valid");
        assert_eq!(
            measured.type_work.get(),
            expected_work,
            "module awareness must not add a second generated-parameter visit",
        );

        let exact = Validator::new_modules(&program, &sources, &module_sources)
            .expect("the exact generated-only relation is canonical");
        exact
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - expected_work)
            .expect("the exact generated-only allowance fits");
        exact
            .collect_type_binders(&nominal_owners, &abstraction_owners)
            .expect("G + K_G work fits exactly");
        assert_eq!(exact.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);

        let short = Validator::new_modules(&program, &sources, &module_sources)
            .expect("the one-short generated-only relation is canonical");
        short
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - (expected_work - 1))
            .expect("the one-short generated-only allowance fits");
        let error = short
            .collect_type_binders(&nominal_owners, &abstraction_owners)
            .expect_err("one missing generated Kind unit must reject");
        assert_eq!(error.reason(), ValidationReason::Resource);
        assert_eq!(short.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);

        let retry = Validator::new_modules(&program, &sources, &module_sources)
            .expect("the generated-only retry relation is canonical");
        retry
            .collect_type_binders(&nominal_owners, &abstraction_owners)
            .expect("a failed generated-only attempt publishes no retained state");
    }

    #[test]
    fn linked_core_rejects_a_shared_recursive_abstraction_initializer() {
        let mut fixture = LinkedCoreValidationFixture::compile(
            concat!(
                "pub first<A : Type> : A -> A\n",
                "first value = value\n\n",
                "pub second<B : Type> : B -> B\n",
                "second value = value\n",
            ),
            concat!(
                "import dependency (first, second)\n",
                "main : Unit -> Int\n",
                "main () = first(second(1))\n",
            ),
            &["first", "second"],
        );
        let (first, _) = fixture.global("first");
        let (second, _) = fixture.global("second");
        let first_abstraction = linked_global_abstraction(&fixture.program, first);
        let second_abstraction = linked_global_abstraction(&fixture.program, second);
        let group_index = fixture
            .program
            .nodes
            .iter()
            .position(|node| {
                let PureExprKind::Computation(PureComputation::RecursiveBind(group)) = &node.kind
                else {
                    return false;
                };
                group
                    .members()
                    .iter()
                    .any(|member| member.binder().id() == first)
                    && group
                        .members()
                        .iter()
                        .any(|member| member.binder().id() == second)
            })
            .expect("the linked globals share one recursive module group");
        let PureExprKind::Computation(PureComputation::RecursiveBind(group)) =
            fixture.program.nodes[group_index].kind.clone()
        else {
            unreachable!("the selected node is a recursive group")
        };
        let connector = NodeId::new(
            fixture.program.arena,
            u32::try_from(fixture.program.nodes.len()).expect("the connector index fits"),
        );
        let old_body = group.body();
        let connector_origin = fixture.program.nodes[group_index]
            .origin
            .clone()
            .expect("the linked group has provenance");
        fixture.program.nodes.push(StoredNode {
            dialect: DialectId::PURE,
            effects: (),
            ty: Type::Tuple(Box::new([Type::Unit, Type::Unit])),
            origin: Some(connector_origin),
            kind: PureExprKind::Computation(PureComputation::Tuple(
                super::super::data::TupleNode::new(vec![second_abstraction, old_body]),
            )),
        });
        let members = group
            .members()
            .iter()
            .map(|member| {
                super::super::recursion::RecursiveBindingMember::new(
                    member.binder().clone(),
                    first_abstraction,
                )
            })
            .collect();
        fixture.program.nodes[group_index].kind =
            PureExprKind::Computation(PureComputation::RecursiveBind(
                super::super::recursion::RecursiveBindingNode::new(members, connector),
            ));

        let error = fixture
            .validate()
            .expect_err("two recursive owners cannot share one abstraction initializer");
        assert_eq!(error.reason(), ValidationReason::Registry);
        assert_eq!(error.node(), Some(first_abstraction));
    }

    #[test]
    fn linked_resolved_abstractions_reject_mixed_identity_classes_and_kind_mismatch() {
        #[derive(Clone, Copy, Debug)]
        enum Mutation {
            MixedIdentity,
            CanonicalKind,
        }

        for mutation in [Mutation::MixedIdentity, Mutation::CanonicalKind] {
            let mut fixture = LinkedCoreValidationFixture::compile(
                concat!(
                    "pub choose<A : Type, B : Type> : A -> B -> A\n",
                    "choose left right = left\n",
                ),
                concat!(
                    "import dependency (choose)\n",
                    "main : Unit -> Int\n",
                    "main () = choose(1)(true)\n",
                ),
                &["choose"],
            );
            let (choose, _) = fixture.global("choose");
            let abstraction_id = linked_global_abstraction(&fixture.program, choose);
            let node = &mut fixture.program.nodes
                [abstraction_id.index().expect("the abstraction index fits")];
            let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                &mut node.kind
            else {
                unreachable!("the linked initializer is a type abstraction")
            };
            let mut abstraction_parameters = abstraction.parameters().to_vec();
            let abstraction_body = abstraction.body();
            let Type::Forall(scheme_parameters, body) = &node.ty else {
                unreachable!("the linked abstraction has an outer scheme")
            };
            let mut scheme_parameters = scheme_parameters.to_vec();
            let body = body.clone();
            match mutation {
                Mutation::MixedIdentity => {
                    let generated = crate::types::TypeVariableId::generated(u32::MAX);
                    abstraction_parameters[1].0 = generated;
                    scheme_parameters[1].0 = generated;
                }
                Mutation::CanonicalKind => {
                    let mismatched = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
                    abstraction_parameters[0].1 = mismatched.clone();
                    scheme_parameters[0].1 = mismatched;
                }
            }
            *abstraction = TypeAbstractionNode::new(abstraction_parameters, abstraction_body);
            node.ty = Type::Forall(scheme_parameters.into_boxed_slice(), body);

            let error = fixture
                .validate()
                .expect_err("linked resolved abstractions require one canonical row class");
            assert_eq!(error.reason(), ValidationReason::Registry, "{mutation:?}");
            assert_eq!(error.node(), Some(abstraction_id), "{mutation:?}");
        }
    }

    #[test]
    fn linked_resolved_abstraction_source_must_match_its_parameter_module() {
        let mut fixture = LinkedCoreValidationFixture::compile(
            concat!(
                "pub identity<A : Type> : A -> A\n",
                "identity value = value\n",
            ),
            concat!(
                "import dependency (identity)\n",
                "main : Unit -> Int\n",
                "main () = identity(1)\n",
            ),
            &["identity"],
        );
        let (identity, parameters) = fixture.global("identity");
        let abstraction = linked_global_abstraction(&fixture.program, identity);
        let parameter_source = fixture
            .module_sources
            .iter()
            .find(|(module, _)| Some(*module) == parameters[0].module())
            .map(|(_, source)| *source)
            .expect("the parameter module has a canonical source");
        let foreign_origin = fixture
            .program
            .nodes
            .iter()
            .filter_map(|node| node.origin.as_ref())
            .find(|origin| origin.primary_span().source() != parameter_source)
            .expect("the entry module supplies a distinct valid origin")
            .clone();
        fixture.program.nodes[abstraction.index().expect("the abstraction index fits")].origin =
            Some(foreign_origin);

        let error = fixture
            .validate()
            .expect_err("a resolved abstraction cannot claim another module's source");
        assert_eq!(error.reason(), ValidationReason::Registry);
        assert_eq!(error.node(), Some(abstraction));
    }

    #[test]
    fn linked_type_application_rejects_argument_order_and_simultaneous_result_mutations() {
        #[derive(Clone, Copy, Debug)]
        enum Mutation {
            ArgumentOrder,
            SimultaneousResult,
        }

        for mutation in [Mutation::ArgumentOrder, Mutation::SimultaneousResult] {
            let mut fixture = LinkedCoreValidationFixture::compile(
                concat!(
                    "pub choose<A : Type, B : Type> : A -> B -> A\n",
                    "choose left right = left\n",
                ),
                concat!(
                    "import dependency (choose)\n",
                    "main : Unit -> Int\n",
                    "main () = choose(1)(true)\n",
                ),
                &["choose"],
            );
            let (choose, _) = fixture.global("choose");
            let application = linked_global_type_application(&fixture.program, choose);
            let application_index = application
                .index()
                .expect("the linked type-application index should fit");
            let registry = Arc::clone(&fixture.program.registry);
            let rows_before = global_row_shape(&registry);
            let module_sources_before = fixture.module_sources.clone();
            let root_before = fixture.program.root;
            let node_count_before = fixture.program.nodes.len();
            let origin_before = fixture.program.nodes[application_index].origin.clone();
            let result_before = fixture.program.nodes[application_index].ty.clone();
            let PureExprKind::Computation(PureComputation::TypeApplication(operation)) =
                &fixture.program.nodes[application_index].kind
            else {
                unreachable!("the selected linked node is a type application")
            };
            assert_eq!(operation.arguments(), &[Type::Int, Type::Bool]);
            let function = operation.function();

            match mutation {
                Mutation::ArgumentOrder => {
                    fixture.program.nodes[application_index].kind =
                        PureExprKind::Computation(PureComputation::TypeApplication(
                            TypeApplicationNode::new(function, vec![Type::Bool, Type::Int]),
                        ));
                    let PureExprKind::Computation(PureComputation::TypeApplication(operation)) =
                        &fixture.program.nodes[application_index].kind
                    else {
                        unreachable!("the reordered carrier remains a type application")
                    };
                    assert_eq!(operation.arguments(), &[Type::Bool, Type::Int]);
                    let mut result_budget =
                        crate::types::TypeWorkBudget::with_limit(TYPE_WORK_LIMIT);
                    assert!(
                        same_type_with_budget(
                            &fixture.program.nodes[application_index].ty,
                            &result_before,
                            &mut result_budget,
                        )
                        .expect("the preserved result comparison should fit"),
                    );
                }
                Mutation::SimultaneousResult => {
                    fixture.program.nodes[application_index].ty = Type::Bool;
                    let PureExprKind::Computation(PureComputation::TypeApplication(operation)) =
                        &fixture.program.nodes[application_index].kind
                    else {
                        unreachable!("the result target remains a type application")
                    };
                    assert_eq!(operation.arguments(), &[Type::Int, Type::Bool]);
                    assert_eq!(fixture.program.nodes[application_index].ty, Type::Bool);
                }
            }

            assert!(Arc::ptr_eq(&registry, &fixture.program.registry));
            assert_eq!(global_row_shape(&fixture.program.registry), rows_before);
            assert_eq!(fixture.module_sources, module_sources_before);
            assert_eq!(fixture.program.root, root_before);
            assert_eq!(fixture.program.nodes.len(), node_count_before);
            assert_eq!(
                fixture.program.nodes[application_index].origin,
                origin_before
            );

            let error = fixture
                .validate()
                .expect_err("each type-application mutation should stop at Core validation");
            assert_eq!(
                error.reason(),
                ValidationReason::TypeOperation,
                "{mutation:?}"
            );
            assert_eq!(error.node(), Some(application), "{mutation:?}");
        }
    }

    #[test]
    fn linked_core_rejects_head_method_argument_swap() {
        let mut fixture = method_evidence_validation_fixture();
        let (source_application, head_argument_count) = fixture
            .program
            .method_evidence_anchors
            .iter()
            .find_map(|anchor| {
                let MethodEvidenceAnchorRole::Adapter {
                    implementation,
                    selection_node,
                } = anchor.role
                else {
                    return None;
                };
                let row = fixture
                    .program
                    .method_evidence
                    .adapters()
                    .iter()
                    .find(|row| {
                        row.implementation == implementation
                            && row.selection_node == selection_node
                            && !row.head_arguments.is_empty()
                    })?;
                let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                    &fixture.program.nodes[anchor.node.index().ok()?].kind
                else {
                    return None;
                };
                if abstraction.parameters().is_empty() {
                    return None;
                }
                let mut current = abstraction.body();
                while let PureExprKind::Computation(PureComputation::Apply(application)) =
                    &fixture.program.nodes[current.index().ok()?].kind
                {
                    current = application.function();
                }
                Some((current, row.head_arguments.len()))
            })
            .expect("the generic implementation adapter should retain head and method arguments");
        let application_index = source_application
            .index()
            .expect("the adapter source application should belong to the linked arena");
        let PureExprKind::Computation(PureComputation::TypeApplication(application)) =
            &fixture.program.nodes[application_index].kind
        else {
            panic!("the adapter should instantiate its implementation method");
        };
        let function = application.function();
        let mut arguments = application.arguments().to_vec();
        assert!(arguments.len() > head_argument_count);
        let last_head = head_argument_count - 1;
        let first_method = head_argument_count;
        assert_ne!(arguments[last_head], arguments[first_method]);
        arguments.swap(last_head, first_method);
        fixture.program.nodes[application_index].kind = PureExprKind::Computation(
            PureComputation::TypeApplication(TypeApplicationNode::new(function, arguments)),
        );

        let error = fixture
            .validate()
            .expect_err("Core must authenticate the head prefix before method-local arguments");
        assert!(matches!(
            error.reason(),
            ValidationReason::NodeType | ValidationReason::ApplicationType
        ));
        assert!(error.node().is_some());
    }

    #[derive(Clone, Copy, Debug)]
    struct LinkedGeneratedAbstractions {
        outer: NodeId,
        inner: NodeId,
        later: NodeId,
    }

    fn linked_generated_abstraction_fixture()
    -> (LinkedCoreValidationFixture, LinkedGeneratedAbstractions) {
        let fixture = LinkedCoreValidationFixture::compile(
            concat!(
                "pub identity<A : Type> : A -> A\n",
                "identity value = value\n",
            ),
            concat!(
                "import dependency (identity)\n",
                "main : Unit -> Int\n",
                "main () = {\n",
                "let outer = fn(value) {\n",
                "let inner = fn(other) {\n",
                "identity(other)\n",
                "}\n",
                "inner(value)\n",
                "}\n",
                "let later = fn(value) {\n",
                "identity(value)\n",
                "}\n",
                "outer(42)\n",
                "}\n",
            ),
            &["identity"],
        );
        let generated = fixture
            .program
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(index, node)| {
                let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                    &node.kind
                else {
                    return None;
                };
                (!abstraction.parameters().is_empty()
                    && abstraction.parameters().iter().all(|(parameter, _)| {
                        matches!(parameter, crate::types::TypeVariableId::Generated(_))
                    }))
                .then(|| {
                    NodeId::new(
                        fixture.program.arena,
                        u32::try_from(index).expect("the generated abstraction index should fit"),
                    )
                })
            })
            .collect::<Vec<_>>();
        assert_eq!(
            generated.len(),
            3,
            "the linked fixture should retain outer, inner, and later generated abstractions",
        );
        let reaches = |root: NodeId, sought: NodeId| {
            let mut visited = HashSet::new();
            let mut work = vec![root];
            while let Some(id) = work.pop() {
                if id == sought {
                    return true;
                }
                if !visited.insert(id) {
                    continue;
                }
                let node = &fixture.program.nodes[id
                    .index()
                    .expect("a linked generated node index should fit")];
                work.extend(
                    (0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)),
                );
            }
            false
        };
        let (outer, inner) = generated
            .iter()
            .copied()
            .find_map(|outer| {
                let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                    &fixture.program.nodes[outer
                        .index()
                        .expect("the outer abstraction index should fit")]
                    .kind
                else {
                    unreachable!("the selected node is a generated abstraction")
                };
                generated
                    .iter()
                    .copied()
                    .find(|inner| *inner != outer && reaches(abstraction.body(), *inner))
                    .map(|inner| (outer, inner))
            })
            .expect("one generated abstraction should lexically contain another");
        let later = generated
            .iter()
            .copied()
            .find(|candidate| *candidate != outer && *candidate != inner)
            .expect("one generated abstraction should follow the outer binding");
        let PureExprKind::Computation(PureComputation::TypeAbstraction(outer_abstraction)) =
            &fixture.program.nodes[outer
                .index()
                .expect("the outer abstraction index should fit")]
            .kind
        else {
            unreachable!("the selected outer node is a type abstraction")
        };
        assert!(reaches(outer_abstraction.body(), inner));
        assert!(!reaches(outer_abstraction.body(), later));
        (
            fixture,
            LinkedGeneratedAbstractions {
                outer,
                inner,
                later,
            },
        )
    }

    fn generated_parameter(
        program: &UnvalidatedProgram,
        abstraction: NodeId,
    ) -> crate::types::TypeVariableId {
        let node = &program.nodes[abstraction
            .index()
            .expect("the generated abstraction index should fit")];
        let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) = &node.kind
        else {
            panic!("the selected generated node should remain an abstraction");
        };
        let [(parameter, Kind::Type)] = abstraction.parameters() else {
            panic!("the generated fixture abstraction should retain one Type parameter");
        };
        assert!(matches!(
            parameter,
            crate::types::TypeVariableId::Generated(_)
        ));
        *parameter
    }

    fn rewrite_type_variable(
        root: &mut Type,
        old: crate::types::TypeVariableId,
        new: crate::types::TypeVariableId,
        rewrite_forall_parameter: bool,
    ) {
        let mut work = vec![root];
        while let Some(ty) = work.pop() {
            match ty {
                Type::Variable(parameter) => {
                    if *parameter == old {
                        *parameter = new;
                    }
                }
                Type::Tuple(elements) => work.extend(elements.iter_mut()),
                Type::Application(function, argument) | Type::Function(function, argument) => {
                    work.push(argument);
                    work.push(function);
                }
                Type::EffectfulFunction(_, _) => {}
                Type::Forall(parameters, body) => {
                    if rewrite_forall_parameter {
                        for (parameter, _) in parameters {
                            if *parameter == old {
                                *parameter = new;
                            }
                        }
                    }
                    work.push(body);
                }
                Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) | Type::Inference(_) => {}
            }
        }
    }

    fn type_quantifies(root: &Type, sought: crate::types::TypeVariableId) -> bool {
        let mut work = vec![root];
        while let Some(ty) = work.pop() {
            match ty {
                Type::Tuple(elements) => work.extend(elements.iter()),
                Type::Application(function, argument) | Type::Function(function, argument) => {
                    work.push(argument);
                    work.push(function);
                }
                Type::EffectfulFunction(_, _) => {}
                Type::Forall(parameters, body) => {
                    if parameters.iter().any(|(parameter, _)| *parameter == sought) {
                        return true;
                    }
                    work.push(body);
                }
                Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_) => {}
            }
        }
        false
    }

    fn type_mentions(root: &Type, sought: crate::types::TypeVariableId) -> bool {
        let mut work = vec![root];
        while let Some(ty) = work.pop() {
            match ty {
                Type::Variable(parameter) if *parameter == sought => return true,
                Type::Tuple(elements) => work.extend(elements.iter()),
                Type::Application(function, argument) | Type::Function(function, argument) => {
                    work.push(argument);
                    work.push(function);
                }
                Type::EffectfulFunction(_, _) => {}
                Type::Forall(parameters, body) => {
                    if parameters.iter().any(|(parameter, _)| *parameter == sought) {
                        return true;
                    }
                    work.push(body);
                }
                Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_) => {}
            }
        }
        false
    }

    fn pattern_mentions(root: &CorePattern, sought: crate::types::TypeVariableId) -> bool {
        let mut work = vec![root];
        while let Some(pattern) = work.pop() {
            if type_mentions(&pattern.ty, sought) {
                return true;
            }
            match &pattern.kind {
                CorePatternKind::Binder(binder) => {
                    if type_mentions(binder.ty(), sought) {
                        return true;
                    }
                }
                CorePatternKind::Tuple(elements) => work.extend(elements.iter()),
                CorePatternKind::Constructor { payload, .. } => {
                    if let Some(payload) = payload.as_deref() {
                        work.push(payload);
                    }
                }
                CorePatternKind::Wildcard | CorePatternKind::Boolean(_) | CorePatternKind::Unit => {
                }
            }
        }
        false
    }

    fn node_type_carriers_mention(
        node: &StoredNode<PureOperationFamily>,
        sought: crate::types::TypeVariableId,
    ) -> bool {
        if type_mentions(&node.ty, sought) {
            return true;
        }
        match &node.kind {
            PureExprKind::Value(PureValue::Function(function)) => {
                type_mentions(function.parameter().ty(), sought)
            }
            PureExprKind::Computation(PureComputation::Bind(binding)) => {
                type_mentions(binding.binder().ty(), sought)
            }
            PureExprKind::Computation(PureComputation::RecursiveBind(group)) => group
                .members()
                .iter()
                .any(|member| type_mentions(member.binder().ty(), sought)),
            PureExprKind::Computation(PureComputation::Match(match_expression)) => match_expression
                .arms()
                .iter()
                .any(|arm| pattern_mentions(arm.pattern(), sought)),
            PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) => abstraction
                .parameters()
                .iter()
                .any(|(parameter, _)| *parameter == sought),
            PureExprKind::Computation(PureComputation::TypeApplication(application)) => application
                .arguments()
                .iter()
                .any(|argument| type_mentions(argument, sought)),
            PureExprKind::Value(
                PureValue::Integer(_)
                | PureValue::Boolean(_)
                | PureValue::Unit(_)
                | PureValue::Constructor(_),
            )
            | PureExprKind::Variable(_)
            | PureExprKind::Computation(
                PureComputation::Apply(_)
                | PureComputation::Primitive(_)
                | PureComputation::Tuple(_)
                | PureComputation::NewtypeConversion(_),
            ) => false,
        }
    }

    fn generated_identity_is_absent(
        program: &UnvalidatedProgram,
        candidate: crate::types::TypeVariableId,
    ) -> bool {
        matches!(candidate, crate::types::TypeVariableId::Generated(_))
            && program
                .nodes
                .iter()
                .all(|node| !node_type_carriers_mention(node, candidate))
            && program.registry.type_variable(candidate).is_none()
            && program
                .registry
                .type_variables()
                .all(|parameter| parameter.id != candidate)
            && program
                .registry
                .nominal_parameter_entries()
                .flat_map(|(_, parameters)| parameters)
                .all(|parameter| parameter.id != candidate)
            && program
                .registry
                .global_parameter_rows()
                .iter()
                .flat_map(|row| row.parameters())
                .all(|parameter| *parameter != candidate)
    }

    fn fresh_generated_identity(program: &UnvalidatedProgram) -> crate::types::TypeVariableId {
        let fresh = (0..u32::MAX)
            .map(crate::types::TypeVariableId::generated)
            .find(|candidate| generated_identity_is_absent(program, *candidate))
            .expect("the complete linked Core and registry should leave one generated identity");

        assert!(matches!(fresh, crate::types::TypeVariableId::Generated(_)));
        for node in &program.nodes {
            assert!(
                !node_type_carriers_mention(node, fresh),
                "the selected identity must be absent from every read-only Core type carrier",
            );
        }
        assert!(program.registry.type_variable(fresh).is_none());
        assert!(
            program
                .registry
                .type_variables()
                .all(|parameter| parameter.id != fresh),
            "the selected identity must be absent from the canonical registry namespace",
        );
        assert!(
            program
                .registry
                .nominal_parameter_entries()
                .flat_map(|(_, parameters)| parameters)
                .all(|parameter| parameter.id != fresh),
            "the selected identity must be absent from the nominal-parameter namespace",
        );
        assert!(
            program
                .registry
                .global_parameter_rows()
                .iter()
                .flat_map(|row| row.parameters())
                .all(|parameter| *parameter != fresh),
            "the selected identity must be absent from every resolved-global row",
        );
        fresh
    }

    fn rewrite_binder_type_variable(
        binder: &mut TypedBinder,
        old: crate::types::TypeVariableId,
        new: crate::types::TypeVariableId,
        rewrite_forall_parameter: bool,
    ) {
        let mut ty = binder.ty().clone();
        rewrite_type_variable(&mut ty, old, new, rewrite_forall_parameter);
        binder.replace_type(ty);
    }

    fn rewrite_node_type_carriers(
        node: &mut StoredNode<PureOperationFamily>,
        old: crate::types::TypeVariableId,
        new: crate::types::TypeVariableId,
        rewrite_forall_parameter: bool,
    ) {
        rewrite_type_variable(&mut node.ty, old, new, rewrite_forall_parameter);
        match &mut node.kind {
            PureExprKind::Value(PureValue::Function(function)) => rewrite_binder_type_variable(
                function.parameter_mut(),
                old,
                new,
                rewrite_forall_parameter,
            ),
            PureExprKind::Computation(PureComputation::Bind(binding)) => {
                rewrite_binder_type_variable(
                    binding.binder_mut(),
                    old,
                    new,
                    rewrite_forall_parameter,
                );
            }
            PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
                for member in group.members_mut() {
                    rewrite_binder_type_variable(
                        member.binder_mut(),
                        old,
                        new,
                        rewrite_forall_parameter,
                    );
                }
            }
            PureExprKind::Computation(PureComputation::Match(match_expression)) => {
                for arm in match_expression.arms_mut() {
                    arm.pattern_mut()
                        .rewrite_types(&mut |ty| {
                            let mut rewritten = ty.clone();
                            rewrite_type_variable(
                                &mut rewritten,
                                old,
                                new,
                                rewrite_forall_parameter,
                            );
                            Ok(rewritten)
                        })
                        .expect("admitted generated pattern types should remain representable");
                }
            }
            PureExprKind::Computation(PureComputation::TypeApplication(application)) => {
                application
                    .rewrite_types(&mut |ty| {
                        let mut rewritten = ty.clone();
                        rewrite_type_variable(&mut rewritten, old, new, rewrite_forall_parameter);
                        Ok(rewritten)
                    })
                    .expect("admitted generated type arguments should remain representable");
            }
            PureExprKind::Value(
                PureValue::Integer(_)
                | PureValue::Boolean(_)
                | PureValue::Unit(_)
                | PureValue::Constructor(_),
            )
            | PureExprKind::Variable(_)
            | PureExprKind::Computation(
                PureComputation::Apply(_)
                | PureComputation::Primitive(_)
                | PureComputation::Tuple(_)
                | PureComputation::NewtypeConversion(_)
                | PureComputation::TypeAbstraction(_),
            ) => {}
        }
    }

    fn lexical_subtree(program: &UnvalidatedProgram, root: NodeId) -> HashSet<NodeId> {
        let mut result = HashSet::new();
        let mut work = vec![root];
        while let Some(id) = work.pop() {
            if !result.insert(id) {
                continue;
            }
            let node = &program.nodes[id.index().expect("the lexical subtree index should fit")];
            work.extend((0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)));
        }
        result
    }

    fn rename_generated_abstraction(
        program: &mut UnvalidatedProgram,
        abstraction_id: NodeId,
        new: crate::types::TypeVariableId,
    ) -> crate::types::TypeVariableId {
        let abstraction_index = abstraction_id
            .index()
            .expect("the generated abstraction index should fit");
        let (old, body) = {
            let node = &program.nodes[abstraction_index];
            let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                &node.kind
            else {
                panic!("the alpha-renamed node should be a type abstraction");
            };
            let [(old, Kind::Type)] = abstraction.parameters() else {
                panic!("the alpha-renamed abstraction should retain one Type parameter");
            };
            (*old, abstraction.body())
        };
        assert_ne!(old, new);
        assert!(matches!(new, crate::types::TypeVariableId::Generated(_)));

        for node in &mut program.nodes {
            if type_quantifies(&node.ty, old) {
                rewrite_type_variable(&mut node.ty, old, new, true);
            }
            match &mut node.kind {
                PureExprKind::Value(PureValue::Function(function))
                    if type_quantifies(function.parameter().ty(), old) =>
                {
                    rewrite_binder_type_variable(function.parameter_mut(), old, new, true);
                }
                PureExprKind::Computation(PureComputation::Bind(binding))
                    if type_quantifies(binding.binder().ty(), old) =>
                {
                    rewrite_binder_type_variable(binding.binder_mut(), old, new, true);
                }
                PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
                    for member in group.members_mut() {
                        if type_quantifies(member.binder().ty(), old) {
                            rewrite_binder_type_variable(member.binder_mut(), old, new, true);
                        }
                    }
                }
                PureExprKind::Value(_)
                | PureExprKind::Variable(_)
                | PureExprKind::Computation(
                    PureComputation::Bind(_)
                    | PureComputation::Apply(_)
                    | PureComputation::Primitive(_)
                    | PureComputation::Tuple(_)
                    | PureComputation::Match(_)
                    | PureComputation::NewtypeConversion(_)
                    | PureComputation::TypeAbstraction(_)
                    | PureComputation::TypeApplication(_),
                ) => {}
            }
        }

        let subtree = lexical_subtree(program, body);
        for id in subtree {
            rewrite_node_type_carriers(
                &mut program.nodes[id.index().expect("the lexical node index should fit")],
                old,
                new,
                true,
            );
        }
        let node = &mut program.nodes[abstraction_index];
        let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
            &mut node.kind
        else {
            unreachable!("the alpha-renamed node remains an abstraction")
        };
        let parameters = abstraction
            .parameters()
            .iter()
            .map(|(parameter, kind)| {
                (
                    if *parameter == old { new } else { *parameter },
                    kind.clone(),
                )
            })
            .collect();
        *abstraction = TypeAbstractionNode::new(parameters, body);
        old
    }

    fn rewrite_generated_body_occurrences_without_binder(
        program: &mut UnvalidatedProgram,
        abstraction_id: NodeId,
        new: crate::types::TypeVariableId,
    ) -> crate::types::TypeVariableId {
        let abstraction_index = abstraction_id
            .index()
            .expect("the generated abstraction index should fit");
        let (old, body) = {
            let node = &program.nodes[abstraction_index];
            let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                &node.kind
            else {
                panic!("the escaped node should be a type abstraction");
            };
            (abstraction.parameters()[0].0, abstraction.body())
        };
        for node in &mut program.nodes {
            if type_quantifies(&node.ty, old) {
                rewrite_type_variable(&mut node.ty, old, new, false);
            }
            match &mut node.kind {
                PureExprKind::Value(PureValue::Function(function))
                    if type_quantifies(function.parameter().ty(), old) =>
                {
                    rewrite_binder_type_variable(function.parameter_mut(), old, new, false);
                }
                PureExprKind::Computation(PureComputation::Bind(binding))
                    if type_quantifies(binding.binder().ty(), old) =>
                {
                    rewrite_binder_type_variable(binding.binder_mut(), old, new, false);
                }
                PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
                    for member in group.members_mut() {
                        if type_quantifies(member.binder().ty(), old) {
                            rewrite_binder_type_variable(member.binder_mut(), old, new, false);
                        }
                    }
                }
                PureExprKind::Value(_)
                | PureExprKind::Variable(_)
                | PureExprKind::Computation(
                    PureComputation::Bind(_)
                    | PureComputation::Apply(_)
                    | PureComputation::Primitive(_)
                    | PureComputation::Tuple(_)
                    | PureComputation::Match(_)
                    | PureComputation::NewtypeConversion(_)
                    | PureComputation::TypeAbstraction(_)
                    | PureComputation::TypeApplication(_),
                ) => {}
            }
        }
        for id in lexical_subtree(program, body) {
            rewrite_node_type_carriers(
                &mut program.nodes[id.index().expect("the escaped node index should fit")],
                old,
                new,
                false,
            );
        }
        old
    }

    #[test]
    fn linked_core_accepts_capture_free_generated_alpha_renaming() {
        let (valid_fixture, _) = linked_generated_abstraction_fixture();
        valid_fixture
            .validate()
            .expect("an independently compiled generated fixture should validate before mutation");
        let (mut fixture, targets) = linked_generated_abstraction_fixture();
        let old = generated_parameter(&fixture.program, targets.outer);
        let inner = generated_parameter(&fixture.program, targets.inner);
        let later = generated_parameter(&fixture.program, targets.later);
        let fresh = fresh_generated_identity(&fixture.program);
        let registry = Arc::clone(&fixture.program.registry);
        let rows_before = global_row_shape(&registry);
        let module_sources_before = fixture.module_sources.clone();
        let root_before = fixture.program.root;
        let node_count_before = fixture.program.nodes.len();
        let later_type_before = fixture.program.nodes[targets
            .later
            .index()
            .expect("the later abstraction index should fit")]
        .ty
        .clone();

        assert_eq!(
            rename_generated_abstraction(&mut fixture.program, targets.outer, fresh),
            old
        );

        let outer_node = &fixture.program.nodes[targets
            .outer
            .index()
            .expect("the outer abstraction index should fit")];
        let PureExprKind::Computation(PureComputation::TypeAbstraction(outer)) = &outer_node.kind
        else {
            panic!("the renamed outer node should remain a type abstraction");
        };
        assert_eq!(outer.parameters(), &[(fresh, Kind::Type)]);
        let Type::Forall(parameters, _) = &outer_node.ty else {
            panic!("the renamed outer abstraction should retain its scheme");
        };
        assert_eq!(parameters.as_ref(), &[(fresh, Kind::Type)]);
        let outer_body = &fixture.program.nodes[outer
            .body()
            .index()
            .expect("the outer body index should fit")]
        .ty;
        assert!(type_mentions(outer_body, fresh));
        assert!(!type_mentions(outer_body, old));
        assert!(
            fixture
                .program
                .nodes
                .iter()
                .any(|node| node_type_carriers_mention(node, fresh)),
        );
        assert!(
            !fixture
                .program
                .nodes
                .iter()
                .any(|node| node_type_carriers_mention(node, old)),
            "the original generated identity must remain no external or cloned scheme authority",
        );
        let owning_binding = fixture
            .program
            .nodes
            .iter()
            .find_map(|node| {
                let PureExprKind::Computation(PureComputation::Bind(binding)) = &node.kind else {
                    return None;
                };
                (binding.initializer() == targets.outer).then_some(binding)
            })
            .expect("the outer local abstraction should retain one sequential owner");
        assert!(type_quantifies(owning_binding.binder().ty(), fresh));
        assert!(!type_mentions(owning_binding.binder().ty(), old));
        let renamed_subtree = lexical_subtree(&fixture.program, outer.body());
        assert!(renamed_subtree.iter().any(|id| {
            let node = &fixture.program.nodes[id
                .index()
                .expect("the renamed lexical node index should fit")];
            matches!(
                &node.kind,
                PureExprKind::Computation(PureComputation::TypeApplication(application))
                    if application
                        .arguments()
                        .iter()
                        .any(|argument| type_mentions(argument, fresh))
            )
        }));
        assert_eq!(generated_parameter(&fixture.program, targets.inner), inner);
        assert_eq!(generated_parameter(&fixture.program, targets.later), later);
        let mut unrelated_type_budget = crate::types::TypeWorkBudget::with_limit(TYPE_WORK_LIMIT);
        assert!(
            same_type_with_budget(
                &fixture.program.nodes[targets
                    .later
                    .index()
                    .expect("the later abstraction index should fit")]
                .ty,
                &later_type_before,
                &mut unrelated_type_budget,
            )
            .expect("the unrelated later scheme comparison should fit")
        );
        assert!(Arc::ptr_eq(&registry, &fixture.program.registry));
        assert_eq!(global_row_shape(&fixture.program.registry), rows_before);
        assert!(fixture.program.registry.type_variable(old).is_none());
        assert!(fixture.program.registry.type_variable(fresh).is_none());
        assert_eq!(fixture.module_sources, module_sources_before);
        assert_eq!(fixture.program.root, root_before);
        assert_eq!(fixture.program.nodes.len(), node_count_before);

        let LinkedCoreValidationFixture {
            directory,
            graph,
            program,
            module_sources,
            globals: _,
        } = fixture;
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let original = validate_modules(program, &sources, &module_sources)
            .expect("capture-free generated alpha-renaming should independently validate");
        assert!(Arc::ptr_eq(&registry, original.registry()));
        assert_eq!(
            crate::eval::evaluate(&original)
                .expect("the alpha-renamed linked Core should evaluate")
                .value
                .to_string(),
            "42",
        );
        for transformed in [
            crate::core::transform::identity_traversal(&original)
                .expect("identity traversal should preserve alpha-renamed Core"),
            crate::core::transform::fold_literal_primitives(&original)
                .expect("literal folding should preserve alpha-renamed Core"),
        ] {
            assert!(Arc::ptr_eq(&registry, &transformed.registry));
            let transformed = validate_modules(transformed, &sources, &module_sources)
                .expect("each transformed alpha-renamed Core should freshly revalidate");
            assert!(Arc::ptr_eq(&registry, transformed.registry()));
            assert_eq!(
                crate::eval::evaluate(&transformed)
                    .expect("each transformed alpha-renamed Core should evaluate")
                    .value
                    .to_string(),
                "42",
            );
        }
        drop(directory);
    }

    #[test]
    fn linked_core_rejects_each_independent_generated_binder_mutation() {
        #[derive(Clone, Copy, Debug)]
        enum Mutation {
            AbstractionIdentityOnly,
            KindDisagreement,
            ReusedSiblingIdentity,
            NestedShadowing,
            EscapeToEarlierSibling,
            MissingAbstractionProvenance,
        }

        for (mutation, expected_reason) in [
            (
                Mutation::AbstractionIdentityOnly,
                ValidationReason::TypeScope,
            ),
            (Mutation::KindDisagreement, ValidationReason::TypeOperation),
            (
                Mutation::ReusedSiblingIdentity,
                ValidationReason::TypeOperation,
            ),
            (Mutation::NestedShadowing, ValidationReason::TypeOperation),
            (
                Mutation::EscapeToEarlierSibling,
                ValidationReason::TypeScope,
            ),
            (
                Mutation::MissingAbstractionProvenance,
                ValidationReason::Provenance,
            ),
        ] {
            let (valid_fixture, _) = linked_generated_abstraction_fixture();
            valid_fixture.validate().unwrap_or_else(|error| {
                panic!("the independently compiled {mutation:?} fixture should validate: {error}")
            });
            let (mut fixture, targets) = linked_generated_abstraction_fixture();
            let outer = generated_parameter(&fixture.program, targets.outer);
            let inner = generated_parameter(&fixture.program, targets.inner);
            let later = generated_parameter(&fixture.program, targets.later);
            assert_ne!(outer, inner);
            assert_ne!(outer, later);
            assert_ne!(inner, later);
            let registry = Arc::clone(&fixture.program.registry);
            let rows_before = global_row_shape(&registry);
            let module_sources_before = fixture.module_sources.clone();
            let root_before = fixture.program.root;
            let node_count_before = fixture.program.nodes.len();
            let target = match mutation {
                Mutation::NestedShadowing => targets.inner,
                Mutation::EscapeToEarlierSibling | Mutation::ReusedSiblingIdentity => targets.later,
                Mutation::AbstractionIdentityOnly
                | Mutation::KindDisagreement
                | Mutation::MissingAbstractionProvenance => targets.outer,
            };
            let target_index = target
                .index()
                .expect("the generated mutation target index should fit");
            let origin_before = fixture.program.nodes[target_index].origin.clone();
            let generated_origins_before =
                [targets.outer, targets.inner, targets.later].map(|id| {
                    fixture.program.nodes[id
                        .index()
                        .expect("the generated provenance index should fit")]
                    .origin
                    .clone()
                });

            match mutation {
                Mutation::AbstractionIdentityOnly => {
                    let fresh = fresh_generated_identity(&fixture.program);
                    let node = &mut fixture.program.nodes[target_index];
                    let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                        &mut node.kind
                    else {
                        unreachable!("the identity target is an abstraction")
                    };
                    let body = abstraction.body();
                    *abstraction = TypeAbstractionNode::new(vec![(fresh, Kind::Type)], body);
                    let Type::Forall(parameters, _) = &node.ty else {
                        unreachable!("the identity target retains its scheme")
                    };
                    assert_eq!(parameters.as_ref(), &[(outer, Kind::Type)]);
                    assert_eq!(abstraction.parameters(), &[(fresh, Kind::Type)]);
                }
                Mutation::KindDisagreement => {
                    let node = &mut fixture.program.nodes[target_index];
                    let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                        &node.kind
                    else {
                        unreachable!("the Kind target is an abstraction")
                    };
                    assert_eq!(abstraction.parameters(), &[(outer, Kind::Type)]);
                    let Type::Forall(_, body) = &node.ty else {
                        unreachable!("the Kind target retains its scheme")
                    };
                    let body = body.clone();
                    let mismatched = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
                    node.ty = Type::Forall(Box::new([(outer, mismatched.clone())]), body);
                    let Type::Forall(parameters, _) = &node.ty else {
                        unreachable!("the Kind target remains a scheme")
                    };
                    assert_eq!(parameters.as_ref(), &[(outer, mismatched)]);
                }
                Mutation::ReusedSiblingIdentity => {
                    assert_eq!(
                        rename_generated_abstraction(&mut fixture.program, target, outer),
                        later,
                    );
                    assert_eq!(generated_parameter(&fixture.program, target), outer);
                    assert_eq!(generated_parameter(&fixture.program, targets.outer), outer,);
                }
                Mutation::NestedShadowing => {
                    assert!(
                        lexical_subtree(
                            &fixture.program,
                            match &fixture.program.nodes[targets
                                .outer
                                .index()
                                .expect("the outer abstraction index should fit")]
                            .kind
                            {
                                PureExprKind::Computation(PureComputation::TypeAbstraction(
                                    abstraction,
                                )) => abstraction.body(),
                                _ => unreachable!("the outer node remains an abstraction"),
                            },
                        )
                        .contains(&targets.inner)
                    );
                    assert_eq!(
                        rename_generated_abstraction(&mut fixture.program, target, outer),
                        inner,
                    );
                    assert_eq!(generated_parameter(&fixture.program, target), outer);
                }
                Mutation::EscapeToEarlierSibling => {
                    assert_eq!(
                        rewrite_generated_body_occurrences_without_binder(
                            &mut fixture.program,
                            target,
                            outer,
                        ),
                        later,
                    );
                    assert_eq!(generated_parameter(&fixture.program, target), later);
                    let node = &fixture.program.nodes[target_index];
                    let Type::Forall(parameters, body) = &node.ty else {
                        unreachable!("the escaping abstraction retains its scheme")
                    };
                    assert_eq!(parameters.as_ref(), &[(later, Kind::Type)]);
                    assert!(type_quantifies(&node.ty, later));
                    assert!(type_mentions(body, outer));
                    assert!(!type_mentions(body, later));
                }
                Mutation::MissingAbstractionProvenance => {
                    fixture.program.nodes[target_index].origin = None;
                    assert!(fixture.program.nodes[target_index].origin.is_none());
                }
            }

            match mutation {
                Mutation::AbstractionIdentityOnly => {
                    assert_ne!(generated_parameter(&fixture.program, targets.outer), outer);
                    assert_eq!(generated_parameter(&fixture.program, targets.inner), inner);
                    assert_eq!(generated_parameter(&fixture.program, targets.later), later);
                }
                Mutation::KindDisagreement | Mutation::MissingAbstractionProvenance => {
                    assert_eq!(generated_parameter(&fixture.program, targets.outer), outer);
                    assert_eq!(generated_parameter(&fixture.program, targets.inner), inner);
                    assert_eq!(generated_parameter(&fixture.program, targets.later), later);
                }
                Mutation::ReusedSiblingIdentity => {
                    assert_eq!(generated_parameter(&fixture.program, targets.outer), outer);
                    assert_eq!(generated_parameter(&fixture.program, targets.inner), inner);
                }
                Mutation::NestedShadowing => {
                    assert_eq!(generated_parameter(&fixture.program, targets.outer), outer);
                    assert_eq!(generated_parameter(&fixture.program, targets.later), later);
                }
                Mutation::EscapeToEarlierSibling => {
                    assert_eq!(generated_parameter(&fixture.program, targets.outer), outer);
                    assert_eq!(generated_parameter(&fixture.program, targets.inner), inner);
                    assert_eq!(generated_parameter(&fixture.program, targets.later), later);
                }
            }

            assert!(
                Arc::ptr_eq(&registry, &fixture.program.registry),
                "{mutation:?}"
            );
            assert_eq!(
                global_row_shape(&fixture.program.registry),
                rows_before,
                "{mutation:?}",
            );
            assert_eq!(
                fixture.module_sources, module_sources_before,
                "{mutation:?}"
            );
            assert_eq!(fixture.program.root, root_before, "{mutation:?}");
            assert_eq!(
                fixture.program.nodes.len(),
                node_count_before,
                "{mutation:?}"
            );
            if !matches!(mutation, Mutation::MissingAbstractionProvenance) {
                assert_eq!(
                    fixture.program.nodes[target_index].origin, origin_before,
                    "{mutation:?}",
                );
            }
            let generated_origins_after = [targets.outer, targets.inner, targets.later].map(|id| {
                fixture.program.nodes[id
                    .index()
                    .expect("the generated provenance index should fit")]
                .origin
                .clone()
            });
            if matches!(mutation, Mutation::MissingAbstractionProvenance) {
                assert_eq!(
                    generated_origins_after[1..],
                    generated_origins_before[1..],
                    "the unrelated generated origins should remain unchanged",
                );
            } else {
                assert_eq!(
                    generated_origins_after, generated_origins_before,
                    "{mutation:?}",
                );
            }
            let expected_node = match mutation {
                Mutation::AbstractionIdentityOnly => {
                    let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                        &fixture.program.nodes[targets
                            .outer
                            .index()
                            .expect("the outer abstraction index should fit")]
                        .kind
                    else {
                        unreachable!("the outer mutation target remains an abstraction")
                    };
                    let subtree = lexical_subtree(&fixture.program, abstraction.body());
                    fixture
                        .program
                        .nodes
                        .iter()
                        .enumerate()
                        .find_map(|(index, node)| {
                            let id = NodeId::new(
                                fixture.program.arena,
                                u32::try_from(index).expect("the mentioned node index should fit"),
                            );
                            (subtree.contains(&id) && type_mentions(&node.ty, outer)).then_some(id)
                        })
                        .expect("the unchanged body should retain the old generated identity")
                }
                Mutation::KindDisagreement | Mutation::MissingAbstractionProvenance => target,
                Mutation::ReusedSiblingIdentity => targets.later,
                Mutation::NestedShadowing => targets.outer,
                Mutation::EscapeToEarlierSibling => fixture.program.root,
            };

            let error = fixture
                .validate()
                .expect_err("each generated-binder mutation should stop at Core validation");
            assert_eq!(error.reason(), expected_reason, "{mutation:?}");
            assert_eq!(error.node(), Some(expected_node), "{mutation:?}");
        }
    }

    #[test]
    fn module_validation_accepts_generated_only_abstractions_without_rows() {
        let file = SourceFile::new("generated-only.ash", "Generated")
            .expect("the generated-only source fits");
        let node_origin = Origin::Source(
            file.span(ByteRange::new(0, 9).expect("the generated-only range is ordered"))
                .expect("the generated-only span fits"),
        );
        let parameter = crate::types::TypeVariableId::generated(73);
        let mut builder = CoreBuilder::new();
        let body = builder
            .unit(Type::Unit, node_origin.clone())
            .expect("the generated abstraction body fits");
        let root = builder
            .type_abstraction(
                vec![(parameter, Kind::Type)],
                body,
                Type::Forall(Box::new([(parameter, Kind::Type)]), Box::new(Type::Unit)),
                node_origin,
            )
            .expect("the generated abstraction fits");
        let module = ModuleId::new(7_731);

        validate_modules(
            builder
                .finish(root)
                .expect("the generated program finishes"),
            &[&file],
            &[(module, file.id())],
        )
        .expect("generated-only abstractions never consult resolved owner rows");
    }

    #[test]
    fn single_source_validation_accepts_direct_resolved_abstractions_without_rows() {
        let file = SourceFile::new("direct-resolved.ash", "A direct")
            .expect("the direct resolved source fits");
        let parameter_origin = Origin::Source(
            file.span(ByteRange::new(0, 1).expect("the parameter range is ordered"))
                .expect("the parameter span fits"),
        );
        let body_origin = Origin::Source(
            file.span(ByteRange::new(2, 8).expect("the body range is ordered"))
                .expect("the body span fits"),
        );
        let parameter = crate::types::TypeVariableId::resolved(file.id().into(), 0);
        let registry =
            crate::resolved::ResolvedRegistry::default().with_additional_type_variables([
                crate::resolved::ResolvedTypeVariable {
                    id: parameter,
                    spelling: "A".to_owned(),
                    kind: Kind::Type,
                    origin: parameter_origin,
                },
            ]);
        let mut builder = CoreBuilder::with_registry(Arc::new(registry));
        let body = builder
            .unit(Type::Unit, body_origin.clone())
            .expect("the direct abstraction body fits");
        let root = builder
            .type_abstraction(
                vec![(parameter, Kind::Type)],
                body,
                Type::Forall(Box::new([(parameter, Kind::Type)]), Box::new(Type::Unit)),
                body_origin,
            )
            .expect("the direct resolved abstraction fits");

        validate(
            builder.finish(root).expect("the direct program finishes"),
            &[&file],
        )
        .expect("single-source resolved abstractions retain canonical-map compatibility");
    }

    fn coherently_swapped_linked_owner_fixture()
    -> (LinkedCoreValidationFixture, NodeId, NodeId, BinderId) {
        let mut fixture = LinkedCoreValidationFixture::compile(
            concat!(
                "pub first<A : Type> : A -> A\n",
                "first value = value\n\n",
                "pub second<B : Type> : B -> B\n",
                "second value = value\n",
            ),
            concat!(
                "import dependency (first, second)\n",
                "main : Unit -> Int\n",
                "main () = first(second(1))\n",
            ),
            &["first", "second"],
        );
        let (first, first_parameters) = fixture.global("first");
        let first_parameter = first_parameters[0];
        let (second, second_parameters) = fixture.global("second");
        let second_parameter = second_parameters[0];
        let first_abstraction = linked_global_abstraction(&fixture.program, first);
        let second_abstraction = linked_global_abstraction(&fixture.program, second);
        coherently_swap_core_type_variables(
            &mut fixture.program,
            first_parameter,
            second_parameter,
        );
        (fixture, first_abstraction, second_abstraction, first)
    }

    #[test]
    fn linked_core_preserves_registry_graph_binder_and_abstraction_precedence() {
        let (mut row_first, _, _, _) = coherently_swapped_linked_owner_fixture();
        Arc::get_mut(&mut row_first.program.registry)
            .expect("the row-precedence fixture owns its registry")
            .clear_global_parameter_positions_for_core_test();
        row_first.program.root = NodeId::new(row_first.program.arena, u32::MAX);
        let error = row_first
            .validate()
            .expect_err("registry row structure precedes a malformed graph root");
        assert_eq!(error.reason(), ValidationReason::Registry);
        assert_eq!(error.node(), None);

        let (mut graph_first, _, _, _) = coherently_swapped_linked_owner_fixture();
        graph_first.program.root = NodeId::new(graph_first.program.arena, u32::MAX);
        let error = graph_first
            .validate()
            .expect_err("graph validation precedes owning-abstraction row matching");
        assert_eq!(error.reason(), ValidationReason::Root);
        assert_eq!(error.node(), None);

        let (mut binder_first, _, _, first_owner) = coherently_swapped_linked_owner_fixture();
        let owner_source = binder_first
            .module_sources
            .iter()
            .find(|(module, _)| Some(*module) == first_owner.module())
            .map(|(_, source)| *source)
            .expect("the owner module has a canonical source");
        let foreign_origin = binder_first
            .program
            .nodes
            .iter()
            .filter_map(|node| node.origin.as_ref())
            .find(|origin| origin.primary_span().source() != owner_source)
            .expect("the entry module supplies foreign binder provenance")
            .clone();
        let group_index = binder_first
            .program
            .nodes
            .iter()
            .position(|node| {
                let PureExprKind::Computation(PureComputation::RecursiveBind(group)) = &node.kind
                else {
                    return false;
                };
                group
                    .members()
                    .iter()
                    .any(|member| member.binder().id() == first_owner)
            })
            .expect("the first owner belongs to one recursive group");
        let group_id = NodeId::new(
            binder_first.program.arena,
            u32::try_from(group_index).expect("the group index fits"),
        );
        let PureExprKind::Computation(PureComputation::RecursiveBind(group)) =
            &mut binder_first.program.nodes[group_index].kind
        else {
            unreachable!("the selected node is a recursive group")
        };
        let binder = group
            .members_mut()
            .iter_mut()
            .find(|member| member.binder().id() == first_owner)
            .expect("the group retains the first owner")
            .binder_mut();
        *binder = TypedBinder::new(
            binder_first.program.arena,
            binder.id(),
            binder.ty().clone(),
            foreign_origin,
        );
        let error = binder_first
            .validate()
            .expect_err("binder metadata precedes owning-abstraction row matching");
        assert_eq!(error.reason(), ValidationReason::Registry);
        assert_eq!(error.node(), Some(group_id));

        let (mut node_type_later, first_abstraction, _, _) =
            coherently_swapped_linked_owner_fixture();
        node_type_later
            .program
            .nodes
            .last_mut()
            .expect("the fixture has a root node")
            .ty = Type::Bool;
        let error = node_type_later
            .validate()
            .expect_err("the first owning abstraction precedes later node typing");
        assert_eq!(error.reason(), ValidationReason::Registry);
        assert_eq!(error.node(), Some(first_abstraction));

        let (mut scope_later, first_abstraction, _, _) = coherently_swapped_linked_owner_fixture();
        let later_variable = scope_later
            .program
            .nodes
            .iter_mut()
            .enumerate()
            .rev()
            .find_map(|(index, node)| {
                matches!(node.kind, PureExprKind::Variable(_)).then_some((index, node))
            })
            .expect("the fixture retains a later variable occurrence");
        later_variable.1.kind = PureExprKind::Variable(super::super::variable::VariableNode::new(
            BinderId::generated(u32::MAX),
        ));
        assert!(
            later_variable.0
                > first_abstraction
                    .index()
                    .expect("the first abstraction index fits"),
        );
        let error = scope_later
            .validate()
            .expect_err("the first owning abstraction precedes later term scope");
        assert_eq!(error.reason(), ValidationReason::Registry);
        assert_eq!(error.node(), Some(first_abstraction));
    }

    fn source() -> SourceFile {
        SourceFile::new("test.ash", "()").expect("test source")
    }

    #[test]
    fn effectful_authority_walks_retain_nested_row_variables_without_forall() {
        let file = source();
        let mut builder = crate::core::EffectCoreBuilder::with_effect_registry(Arc::new(
            crate::resolved::ResolvedRegistry::default(),
        ));
        let root = builder
            .unit(Type::Unit, origin(&file))
            .expect("effect authority root");
        let program = builder.finish(root).expect("effect authority program");
        let validator = Validator::new(&program, &[&file]);
        let argument = crate::types::TypeVariableId::generated(70);
        let tail = crate::types::TypeVariableId::generated(71);
        let effect = crate::types::EffectInstance::new(
            crate::types::EffectId::new(file.id().into(), 0),
            Box::new([Type::Variable(argument)]),
        );
        let ty = Type::function_computation(
            Type::Unit,
            crate::types::ComputationType::new(
                Type::Unit,
                EffectRow::with_tail(
                    Box::new([effect]),
                    crate::types::EffectRowVariable::rigid(tail),
                    Box::new([]),
                ),
            ),
        );

        assert_eq!(validator.type_contains_forall_charged(&ty), Ok(false));
        assert_eq!(
            validator.type_contains_variable_charged(&ty, argument),
            Ok(true)
        );
        assert_eq!(
            validator.type_contains_variable_charged(&ty, tail),
            Ok(true)
        );
    }

    #[test]
    fn effect_type_application_authenticates_complete_row_arguments() {
        let file = source();
        let node_origin = origin(&file);
        let fixture = || {
            let mut builder = crate::core::EffectCoreBuilder::with_effect_registry(Arc::new(
                crate::resolved::ResolvedRegistry::default(),
            ));
            let outer = crate::types::TypeVariableId::generated(70);
            let inner = crate::types::TypeVariableId::generated(71);
            let dependent = |variable| {
                Type::function_computation(
                    Type::Unit,
                    crate::types::ComputationType::new(
                        Type::Unit,
                        EffectRow::open(
                            crate::types::EffectRowVariable::rigid(variable),
                            Box::new([]),
                        ),
                    ),
                )
            };
            let identity = |variable| {
                Type::Function(Box::new(dependent(variable)), Box::new(dependent(variable)))
            };
            let parameter = builder
                .binder(dependent(inner), node_origin.clone())
                .unwrap();
            let body = builder
                .variable(parameter.id(), dependent(inner), node_origin.clone())
                .unwrap();
            let function = builder
                .function(parameter, body, identity(inner), node_origin.clone())
                .unwrap();
            let inner_abstraction = builder
                .type_abstraction(
                    vec![(inner, Kind::EffectRow)],
                    function,
                    Type::Forall(
                        Box::new([(inner, Kind::EffectRow)]),
                        Box::new(identity(inner)),
                    ),
                    node_origin.clone(),
                )
                .unwrap();
            let application = builder
                .type_application_with_row_arguments(
                    inner_abstraction,
                    Vec::new(),
                    vec![EffectRow::open(
                        crate::types::EffectRowVariable::rigid(outer),
                        Box::new([]),
                    )],
                    identity(outer),
                    node_origin.clone(),
                )
                .unwrap();
            let root = builder
                .type_abstraction(
                    vec![(outer, Kind::EffectRow)],
                    application,
                    Type::Forall(
                        Box::new([(outer, Kind::EffectRow)]),
                        Box::new(identity(outer)),
                    ),
                    node_origin.clone(),
                )
                .unwrap();
            (
                builder.finish(root).unwrap(),
                application,
                inner_abstraction,
            )
        };

        let (program, _, _) = fixture();
        Validator::new(&program, &[&file])
            .run_effect()
            .expect("the complete open row argument should authenticate");

        let (mut forged, application, function) = fixture();
        forged.nodes[application.index().unwrap()].kind =
            super::super::effect::EffectOperationFamily::from_pure(PureExprKind::Computation(
                PureComputation::TypeApplication(TypeApplicationNode::new_with_row_arguments(
                    function,
                    Vec::new(),
                    vec![EffectRow::empty()],
                )),
            ));
        let error = Validator::new(&forged, &[&file])
            .run_effect()
            .expect_err("a forged complete row argument must be rejected");
        assert_eq!(error.reason(), ValidationReason::TypeOperation);
        assert_eq!(error.node(), Some(application));
    }

    #[test]
    fn type_application_row_argument_scope_work_is_exact_atomic_and_retryable() {
        const WIDTH: usize = 8;
        const DEPTH: usize = 32;
        let file = source();
        let node_origin = origin(&file);
        let closed_argument = || {
            Type::Tuple(
                (0..WIDTH)
                    .map(|_| {
                        (0..DEPTH).fold(Type::Unit, |ty, _| {
                            Type::Application(Box::new(ty), Box::new(Type::Unit))
                        })
                    })
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            )
        };
        let fixture = |argument: Type| {
            let mut builder = crate::core::EffectCoreBuilder::with_effect_registry(Arc::new(
                crate::resolved::ResolvedRegistry::default(),
            ));
            let outer = crate::types::TypeVariableId::generated(72);
            let inner = crate::types::TypeVariableId::generated(73);
            let body = builder.unit(Type::Unit, node_origin.clone()).unwrap();
            let function = builder
                .type_abstraction(
                    vec![(inner, Kind::EffectRow)],
                    body,
                    Type::Forall(Box::new([(inner, Kind::EffectRow)]), Box::new(Type::Unit)),
                    node_origin.clone(),
                )
                .unwrap();
            let row = EffectRow::with_tail(
                Box::new([crate::types::EffectInstance::new(
                    crate::types::EffectId::new(file.id().into(), 0),
                    Box::new([argument.clone()]),
                )]),
                crate::types::EffectRowVariable::rigid(outer),
                Box::new([crate::types::EffectInstance::new(
                    crate::types::EffectId::new(file.id().into(), 1),
                    Box::new([argument]),
                )]),
            );
            let application = builder
                .type_application_with_row_arguments(
                    function,
                    Vec::new(),
                    vec![row],
                    Type::Unit,
                    node_origin.clone(),
                )
                .unwrap();
            let root = builder
                .type_abstraction(
                    vec![(outer, Kind::EffectRow)],
                    application,
                    Type::Forall(Box::new([(outer, Kind::EffectRow)]), Box::new(Type::Unit)),
                    node_origin.clone(),
                )
                .unwrap();
            builder.finish(root).unwrap()
        };

        let shallow = fixture(Type::Unit);
        let shallow_validator = Validator::new(&shallow, &[&file]);
        shallow_validator.validate_type_scopes().unwrap();
        let shallow_work = shallow_validator.type_work.get();

        let argument = closed_argument();
        let mut structural = crate::types::TypeWorkBudget::unbounded();
        crate::types::charge_type_cells(&argument, &mut structural).unwrap();
        let program = fixture(argument);
        let measured = Validator::new(&program, &[&file]);
        measured.validate_type_scopes().unwrap();
        let exact = measured.type_work.get();
        // Canonical open rows retain their known member in the tail's lacks set.
        assert_eq!(exact - shallow_work, 3 * (structural.used() - 1));

        let retained = program.nodes.len();
        let short = Validator::new(&program, &[&file]);
        short
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - (exact - 1))
            .unwrap();
        assert_eq!(
            short.validate_type_scopes().unwrap_err().reason(),
            ValidationReason::Resource
        );
        assert_eq!(program.nodes.len(), retained);
        for _ in 0..2 {
            let retry = Validator::new(&program, &[&file]);
            retry
                .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - exact)
                .unwrap();
            retry.validate_type_scopes().unwrap();
            assert_eq!(retry.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);
        }
    }

    #[test]
    fn least_handler_output_is_iterative_for_deep_nesting() {
        std::thread::Builder::new()
            .name("effect-least-row-deep".to_owned())
            .stack_size(64 * 1024)
            .spawn(|| {
                const DEPTH: u32 = 4_096;
                let file = source();
                let node_origin = origin(&file);
                let mut builder = crate::core::EffectCoreBuilder::with_effect_registry(Arc::new(
                    crate::resolved::ResolvedRegistry::default(),
                ));
                let mut body = builder
                    .unit(Type::Unit, node_origin.clone())
                    .expect("deep handler seed");
                for ordinal in 0..DEPTH {
                    let effect_id = crate::types::EffectId::new(file.id().into(), ordinal);
                    let effect = crate::types::EffectInstance::new(effect_id, Box::new([]));
                    let request = builder
                        .request(
                            crate::types::EffectInstance::new(effect_id, Box::new([])),
                            crate::types::OperationId::new(effect_id, 0),
                            body,
                            Type::Unit,
                            EffectRow::singleton(crate::types::EffectInstance::new(
                                effect_id,
                                Box::new([]),
                            )),
                            node_origin.clone(),
                        )
                        .expect("deep request layer");
                    body = builder
                        .handler(
                            super::super::effect::HandlerId::new(ordinal),
                            request,
                            effect,
                            Vec::new(),
                            Type::Unit,
                            EffectRow::empty(),
                            node_origin.clone(),
                        )
                        .expect("deep handler layer");
                }
                let program = builder.finish(body).expect("deep effect program");
                let validator = Validator::new(&program, &[&file]);
                assert_eq!(validator.least_handler_output(body), Ok(EffectRow::empty()));
            })
            .expect("deep least-row worker")
            .join()
            .expect("least-row analysis must stay iterative");
    }

    #[test]
    fn wide_effect_handler_validation_is_exact_and_retryable() {
        use crate::{core::UnvalidatedEffectProgram, elaborate::EffectElaborator};

        const WIDTH: usize = 32;
        fn fixture() -> (UnvalidatedEffectProgram, SourceFile) {
            let operations = (0..WIDTH)
                .map(|ordinal| format!("op{ordinal} : Unit -> Unit"))
                .collect::<Vec<_>>()
                .join("\n");
            let clauses = (0..WIDTH)
                .map(|ordinal| format!("op{ordinal} ignored => resume ()"))
                .collect::<Vec<_>>()
                .join("\n");
            let directory = LinkedValidationDirectory::create();
            let path = directory.write(
                "wide-effect.ash",
                &format!(
                    "effect Wide {{\n{operations}\n}}\n\nmain : Unit -> Unit\n\
                     main () = handle (perform Wide.op0 ()) with Wide {{\n{clauses}\n}}\n"
                ),
            );
            let graph = load_module_graph(&path, &ModuleRoots::empty()).expect("wide graph");
            let source = graph.module(graph.entry()).unwrap().source().clone();
            let linked = link_modules(checked_linked_validation_graph(&graph), graph.entry())
                .expect("wide linked program");
            let linked = validate_linked_facts_for_test(linked).expect("wide checked program");
            let mut elaborator =
                EffectElaborator::for_module_program(&linked).expect("effect elaborator");
            let typed = elaborator
                .synthesize_effect_module_program(&linked)
                .expect("wide effect lowering");
            (elaborator.finish(typed.node).expect("effect Core"), source)
        }

        let (program, source) = fixture();
        let mut measured = Validator::new(&program, &[&source]);
        measured.run_effect().expect("wide effect Core validates");
        let exact_work = measured.type_work.get();
        assert!(exact_work < CORE_VALIDATION_TYPE_WORK_LIMIT);

        let (program, source) = fixture();
        let mut short = Validator::new(&program, &[&source]);
        short
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - (exact_work - 1))
            .expect("one-short precharge");
        assert_eq!(
            short
                .run_effect()
                .expect_err("one-short must reject")
                .reason(),
            ValidationReason::Resource,
        );
        assert_eq!(short.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);

        for _ in 0..2 {
            let (program, source) = fixture();
            let mut retry = Validator::new(&program, &[&source]);
            retry
                .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - exact_work)
                .expect("exact precharge");
            retry.run_effect().expect("fresh exact retry");
            assert_eq!(retry.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);
        }
    }

    #[test]
    fn effect_registry_rejects_each_forged_authority_class() {
        use crate::{
            core::effect::EffectCoreBuilder,
            resolved::{
                ResolvedConstructor, ResolvedEffectDeclaration, ResolvedEffectOperation,
                ResolvedNominalType, ResolvedType, ResolvedTypeProvenance,
                ResolvedTypeProvenanceNode,
            },
            types::{ConstructorId, EffectId, NominalTypeId, TypeVariableId},
        };

        #[derive(Clone, Copy)]
        enum Mutation {
            Canonical,
            ParameterIdentity,
            ParameterKind,
            OperationIdentity,
            OperationSpelling,
            SignatureScope,
            ForeignSource,
            DuplicateEffectOwner,
            NominalCrossOwner,
        }

        let source = SourceFile::new("effect-registry.ash", "effect Build").unwrap();
        let foreign = SourceFile::new("foreign.ash", "effect Build").unwrap();
        let span = source.span(ByteRange::new(0, 12).unwrap()).unwrap();
        let foreign_span = foreign.span(ByteRange::new(0, 12).unwrap()).unwrap();
        let module = ModuleId::from(source.id());
        let effect = EffectId::new(module, 0);
        let f = TypeVariableId::resolved(module, 0);
        for mutation in [
            Mutation::Canonical,
            Mutation::ParameterIdentity,
            Mutation::ParameterKind,
            Mutation::OperationIdentity,
            Mutation::OperationSpelling,
            Mutation::SignatureScope,
            Mutation::ForeignSource,
            Mutation::DuplicateEffectOwner,
            Mutation::NominalCrossOwner,
        ] {
            let mut parameters = vec![ResolvedTypeVariable {
                id: f,
                spelling: "F".into(),
                kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                origin: Origin::Source(span),
            }];
            let mut operation = ResolvedEffectOperation {
                id: OperationId::new(effect, 0),
                spelling: "build".into(),
                annotation: ResolvedType {
                    ty: Type::Function(
                        Box::new(Type::Unit),
                        Box::new(Type::Application(
                            Box::new(Type::Variable(f)),
                            Box::new(Type::Unit),
                        )),
                    ),
                    provenance: ResolvedTypeProvenance::new(
                        vec![ResolvedTypeProvenanceNode::Fact(span)],
                        0,
                    ),
                    origin: Origin::Source(span),
                    span,
                },
                origin: Origin::Source(span),
                span,
            };
            match mutation {
                Mutation::Canonical => {}
                Mutation::ParameterIdentity => {
                    parameters[0].id = TypeVariableId::resolved(ModuleId::new(91), 0);
                }
                Mutation::ParameterKind => parameters[0].kind = Kind::EffectRow,
                Mutation::OperationIdentity => operation.id = OperationId::new(effect, 1),
                Mutation::OperationSpelling => operation.spelling = "Build".into(),
                Mutation::SignatureScope => {
                    operation.annotation.ty = Type::Function(
                        Box::new(Type::Unit),
                        Box::new(Type::Variable(TypeVariableId::resolved(module, 9))),
                    );
                }
                Mutation::ForeignSource => operation.origin = Origin::Source(foreign_span),
                Mutation::DuplicateEffectOwner | Mutation::NominalCrossOwner => {}
            }
            let mut effects = vec![ResolvedEffectDeclaration {
                id: effect,
                public: false,
                spelling: "Build".into(),
                parameters: parameters.clone().into_boxed_slice(),
                operations: vec![operation.clone()].into_boxed_slice(),
                origin: Origin::Source(span),
                span,
            }];
            if matches!(mutation, Mutation::DuplicateEffectOwner) {
                let second = EffectId::new(module, 1);
                operation.id = OperationId::new(second, 0);
                operation.spelling = "more".into();
                effects.push(ResolvedEffectDeclaration {
                    id: second,
                    public: false,
                    spelling: "More".into(),
                    parameters: parameters.clone().into_boxed_slice(),
                    operations: vec![operation].into_boxed_slice(),
                    origin: Origin::Source(span),
                    span,
                });
            }
            let registry = if matches!(mutation, Mutation::NominalCrossOwner) {
                let nominal = NominalTypeId::new(module, 0);
                let constructor = ConstructorId::new(nominal, 0);
                crate::resolved::ResolvedRegistry::new(
                    vec![ResolvedNominalType {
                        id: nominal,
                        spelling: "Box".into(),
                        constructors: vec![constructor].into_boxed_slice(),
                        declaration_kind: ResolvedNominalDeclarationKind::Data,
                        representation: None,
                        representation_provenance: None,
                        origin: Origin::Source(span),
                    }],
                    vec![ResolvedConstructor {
                        id: constructor,
                        owner: nominal,
                        spelling: "Box".into(),
                        payload: Some(Type::Variable(f)),
                        origin: Origin::Source(span),
                    }],
                )
                .with_type_parameters(vec![(nominal, parameters.clone())])
            } else {
                crate::resolved::ResolvedRegistry::default()
                    .with_additional_type_variables(parameters.iter().cloned())
            }
            .with_effects(effects);
            let mut builder = EffectCoreBuilder::with_effect_registry(Arc::new(registry));
            let root = builder.unit(Type::Unit, Origin::Source(span)).unwrap();
            let program = builder.finish(root).unwrap();
            let validator = Validator::new(&program, &[&source]);
            let result = validator
                .validate_registry()
                .and_then(|mut owners| validator.validate_effect_registry(None, &mut owners));
            if matches!(mutation, Mutation::Canonical) {
                result.expect("canonical effect facts authenticate");
            } else {
                assert_eq!(result.unwrap_err().reason(), ValidationReason::Registry);
            }
        }
    }

    fn origin(source: &SourceFile) -> Origin {
        let range = ByteRange::new(0, 2).expect("ordered range");
        Origin::Source(source.span(range).expect("source span"))
    }

    fn newtype_registry(
        source: &SourceFile,
    ) -> (
        Arc<crate::resolved::ResolvedRegistry>,
        crate::types::NominalTypeId,
        ConstructorId,
    ) {
        let owner = crate::types::NominalTypeId::new(source.id(), 0);
        let constructor = ConstructorId::new(owner, 0);
        let node_origin = origin(source);
        let representation_span = node_origin.primary_span();
        let registry = crate::resolved::ResolvedRegistry::new(
            vec![ResolvedNominalType {
                representation_provenance: Some(ResolvedTypeProvenance::new(
                    vec![ResolvedTypeProvenanceNode::Fact(representation_span)],
                    0,
                )),
                declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Newtype,
                representation: Some(Type::Int),
                id: owner,
                spelling: "UserId".to_owned(),
                constructors: Box::new([constructor]),
                origin: node_origin.clone(),
            }],
            vec![ResolvedConstructor {
                id: constructor,
                owner,
                spelling: "UserId".to_owned(),
                payload: None,
                origin: node_origin,
            }],
        )
        .with_type_parameters(vec![(owner, Vec::new())]);
        (Arc::new(registry), owner, constructor)
    }

    #[derive(Clone, Copy, Debug)]
    enum NewtypeRegistryTamper {
        OrdinaryKind,
        NominalGeneratedOrigin,
        ConstructorGeneratedOrigin,
        WrongShape,
        WrongSource,
        EmptyRange,
        OutsideConstructor,
        SharedNode,
        OrphanNode,
    }

    fn tampered_newtype_registry(
        source: &SourceFile,
        foreign: &SourceFile,
        tamper: NewtypeRegistryTamper,
    ) -> Arc<crate::resolved::ResolvedRegistry> {
        let owner = crate::types::NominalTypeId::new(source.id(), 0);
        let constructor = ConstructorId::new(owner, 0);
        let declaration_span = source
            .span(ByteRange::new(0, 30).expect("declaration range"))
            .expect("declaration span");
        let constructor_span = source
            .span(ByteRange::new(18, 30).expect("constructor range"))
            .expect("constructor span");
        let representation_span = source
            .span(ByteRange::new(26, 29).expect("representation range"))
            .expect("representation span");
        let outside_constructor = source
            .span(ByteRange::new(8, 15).expect("name range"))
            .expect("name span");
        let empty_span = source
            .span(ByteRange::new(26, 26).expect("empty range"))
            .expect("empty span");
        let foreign_span = foreign
            .span(ByteRange::new(0, 3).expect("foreign range"))
            .expect("foreign span");
        let source_origin = Origin::Source(declaration_span);
        let generated_origin = Origin::Generated {
            cause: Box::new(source_origin.clone()),
            reason: crate::source::GeneratedReason::TypeChecking,
        };
        let (representation, provenance) = match tamper {
            NewtypeRegistryTamper::WrongShape => (
                Type::Int,
                ResolvedTypeProvenance::new(
                    vec![ResolvedTypeProvenanceNode::Tuple {
                        span: representation_span,
                        elements: Box::new([]),
                    }],
                    0,
                ),
            ),
            NewtypeRegistryTamper::WrongSource => (
                Type::Int,
                ResolvedTypeProvenance::new(
                    vec![ResolvedTypeProvenanceNode::Fact(foreign_span)],
                    0,
                ),
            ),
            NewtypeRegistryTamper::EmptyRange => (
                Type::Int,
                ResolvedTypeProvenance::new(vec![ResolvedTypeProvenanceNode::Fact(empty_span)], 0),
            ),
            NewtypeRegistryTamper::OutsideConstructor => (
                Type::Int,
                ResolvedTypeProvenance::new(
                    vec![ResolvedTypeProvenanceNode::Fact(outside_constructor)],
                    0,
                ),
            ),
            NewtypeRegistryTamper::SharedNode => (
                Type::Tuple(Box::new([Type::Int, Type::Int])),
                ResolvedTypeProvenance::new(
                    vec![
                        ResolvedTypeProvenanceNode::Fact(representation_span),
                        ResolvedTypeProvenanceNode::Tuple {
                            span: representation_span,
                            elements: Box::new([0, 0]),
                        },
                    ],
                    1,
                ),
            ),
            NewtypeRegistryTamper::OrphanNode => (
                Type::Int,
                ResolvedTypeProvenance::new(
                    vec![
                        ResolvedTypeProvenanceNode::Fact(representation_span),
                        ResolvedTypeProvenanceNode::Fact(representation_span),
                    ],
                    0,
                ),
            ),
            NewtypeRegistryTamper::OrdinaryKind
            | NewtypeRegistryTamper::NominalGeneratedOrigin
            | NewtypeRegistryTamper::ConstructorGeneratedOrigin => (
                Type::Int,
                ResolvedTypeProvenance::new(
                    vec![ResolvedTypeProvenanceNode::Fact(representation_span)],
                    0,
                ),
            ),
        };
        let nominal_origin = if matches!(tamper, NewtypeRegistryTamper::NominalGeneratedOrigin) {
            generated_origin.clone()
        } else {
            source_origin.clone()
        };
        let constructor_origin =
            if matches!(tamper, NewtypeRegistryTamper::ConstructorGeneratedOrigin) {
                generated_origin
            } else {
                Origin::Source(constructor_span)
            };
        let declaration_kind = if matches!(tamper, NewtypeRegistryTamper::OrdinaryKind) {
            ResolvedNominalDeclarationKind::Data
        } else {
            ResolvedNominalDeclarationKind::Newtype
        };
        Arc::new(
            crate::resolved::ResolvedRegistry::new(
                vec![ResolvedNominalType {
                    id: owner,
                    declaration_kind,
                    spelling: "Wrapped".to_owned(),
                    constructors: Box::new([constructor]),
                    representation: Some(representation),
                    representation_provenance: Some(provenance),
                    origin: nominal_origin,
                }],
                vec![ResolvedConstructor {
                    id: constructor,
                    owner,
                    spelling: "Wrapped".to_owned(),
                    payload: None,
                    origin: constructor_origin,
                }],
            )
            .with_type_parameters(vec![(owner, Vec::new())]),
        )
    }

    fn unit_program_with_registry(
        source: &SourceFile,
        registry: Arc<crate::resolved::ResolvedRegistry>,
    ) -> UnvalidatedProgram {
        let mut builder = CoreBuilder::with_registry(registry);
        let root = builder
            .unit(
                Type::Unit,
                Origin::Source(
                    source
                        .span(ByteRange::new(0, 30).expect("root range"))
                        .expect("root span"),
                ),
            )
            .expect("unit root should fit");
        builder.finish(root).expect("unit root should finish")
    }

    fn range_origin(source: &SourceFile, start: u32, end: u32) -> Origin {
        Origin::Source(
            source
                .span(ByteRange::new(start, end).expect("ordered range"))
                .expect("source span"),
        )
    }

    fn type_parameter(
        identity: crate::types::TypeVariableId,
    ) -> (crate::types::TypeVariableId, Kind) {
        (identity, Kind::Type)
    }

    fn type_parameters(
        identities: impl IntoIterator<Item = crate::types::TypeVariableId>,
    ) -> Vec<(crate::types::TypeVariableId, Kind)> {
        identities.into_iter().map(type_parameter).collect()
    }

    fn modular_registry_program(
        first_source: &SourceFile,
        second_source: &SourceFile,
        second_declaration: u32,
    ) -> (UnvalidatedProgram, ModuleId, ModuleId) {
        let first_module = ModuleId::new(40);
        let second_module = ModuleId::new(41);
        let first_nominal = crate::types::NominalTypeId::new(first_module, 0);
        let second_nominal = crate::types::NominalTypeId::new(second_module, second_declaration);
        let first_constructor = ConstructorId::new(first_nominal, 0);
        let second_constructor = ConstructorId::new(second_nominal, 0);
        let first_parameter = crate::types::TypeVariableId::resolved(first_module, 0);
        let second_parameter = crate::types::TypeVariableId::resolved(second_module, 0);
        let registry = Arc::new(
            crate::resolved::ResolvedRegistry::new(
                vec![
                    crate::resolved::ResolvedNominalType {
                        representation_provenance: None,
                        declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                        representation: None,
                        id: first_nominal,
                        spelling: "Shared".into(),
                        constructors: vec![first_constructor].into_boxed_slice(),
                        origin: range_origin(first_source, 0, 13),
                    },
                    crate::resolved::ResolvedNominalType {
                        representation_provenance: None,
                        declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                        representation: None,
                        id: second_nominal,
                        spelling: "Shared".into(),
                        constructors: vec![second_constructor].into_boxed_slice(),
                        origin: range_origin(second_source, 0, 13),
                    },
                ],
                vec![
                    crate::resolved::ResolvedConstructor {
                        id: first_constructor,
                        owner: first_nominal,
                        spelling: "Make".into(),
                        payload: Some(Type::Variable(first_parameter)),
                        origin: range_origin(first_source, 9, 13),
                    },
                    crate::resolved::ResolvedConstructor {
                        id: second_constructor,
                        owner: second_nominal,
                        spelling: "Make".into(),
                        payload: Some(Type::Variable(second_parameter)),
                        origin: range_origin(second_source, 9, 13),
                    },
                ],
            )
            .with_type_parameters(vec![
                (
                    first_nominal,
                    vec![crate::resolved::ResolvedTypeVariable {
                        id: first_parameter,
                        spelling: "A".into(),
                        kind: crate::types::Kind::Type,
                        origin: range_origin(first_source, 7, 8),
                    }],
                ),
                (
                    second_nominal,
                    vec![crate::resolved::ResolvedTypeVariable {
                        id: second_parameter,
                        spelling: "A".into(),
                        kind: crate::types::Kind::Type,
                        origin: range_origin(second_source, 7, 8),
                    }],
                ),
            ]),
        );
        let mut builder = CoreBuilder::with_registry(registry);
        let root = builder
            .unit(Type::Unit, range_origin(first_source, 0, 13))
            .expect("unit root");
        (
            builder.finish(root).expect("valid root"),
            first_module,
            second_module,
        )
    }

    #[test]
    fn module_validation_allows_module_local_registry_spellings() {
        let first = SourceFile::new("first.ash", "Shared A Make").expect("test source");
        let second = SourceFile::new("second.ash", "Shared A Make").expect("test source");
        let (program, first_module, second_module) = modular_registry_program(&first, &second, 0);

        validate_modules(
            program,
            &[&first, &second],
            &[(first_module, first.id()), (second_module, second.id())],
        )
        .expect("same spellings in distinct modules are valid");
    }

    #[test]
    fn module_validation_rejects_missing_forged_and_duplicate_relations() {
        let first = SourceFile::new("first.ash", "Shared A Make").expect("test source");
        let second = SourceFile::new("second.ash", "Shared A Make").expect("test source");

        let (program, first_module, _) = modular_registry_program(&first, &second, 0);
        let error = validate_modules(program, &[&first, &second], &[(first_module, first.id())])
            .expect_err("every defining module needs a source mapping");
        assert_eq!(error.reason(), ValidationReason::Registry);

        let (program, first_module, second_module) = modular_registry_program(&first, &second, 0);
        let error = validate_modules(
            program,
            &[&first, &second],
            &[(first_module, second.id()), (second_module, first.id())],
        )
        .expect_err("a module cannot claim another module's source");
        assert_eq!(error.reason(), ValidationReason::Registry);

        let (program, first_module, second_module) = modular_registry_program(&first, &second, 0);
        let error = validate_modules(
            program,
            &[&first, &second],
            &[
                (first_module, first.id()),
                (first_module, second.id()),
                (second_module, second.id()),
            ],
        )
        .expect_err("a module cannot have duplicate source associations");
        assert_eq!(error.reason(), ValidationReason::Registry);

        let (program, first_module, second_module) = modular_registry_program(&first, &second, 0);
        let error = validate_modules(
            program,
            &[&first, &second],
            &[(first_module, first.id()), (second_module, first.id())],
        )
        .expect_err("one canonical source cannot define two modules");
        assert_eq!(error.reason(), ValidationReason::Registry);
    }

    #[test]
    fn module_validation_checks_declaration_indices_per_module() {
        let first = SourceFile::new("first.ash", "Shared A Make").expect("test source");
        let second = SourceFile::new("second.ash", "Shared A Make").expect("test source");
        let (program, first_module, second_module) = modular_registry_program(&first, &second, 1);

        let error = validate_modules(
            program,
            &[&first, &second],
            &[(first_module, first.id()), (second_module, second.id())],
        )
        .expect_err("each module's nominal declarations begin at zero");
        assert_eq!(error.reason(), ValidationReason::Registry);
    }

    #[test]
    fn module_validation_checks_resolved_binder_ownership() {
        let first = SourceFile::new("first.ash", "()").expect("test source");
        let second = SourceFile::new("second.ash", "()").expect("test source");
        let module = ModuleId::new(42);
        let binder_id = BinderId::resolved(module, 0);
        let mut builder = CoreBuilder::new();
        builder
            .reserve_resolved_binders([binder_id])
            .expect("reserve source binder");
        let initializer = builder
            .unit(Type::Unit, origin(&first))
            .expect("unit initializer");
        let binder = builder
            .resolved_binder(binder_id, Type::Unit, origin(&first))
            .expect("resolved binder");
        let body = builder
            .variable(binder_id, Type::Unit, origin(&first))
            .expect("bound occurrence");
        let root = builder
            .binding(binder, initializer, body, Type::Unit, origin(&first))
            .expect("binding root");

        let error = validate_modules(
            builder.finish(root).expect("valid root"),
            &[&first, &second],
            &[(module, second.id())],
        )
        .expect_err("resolved binders belong to their defining module source");
        assert_eq!(error.reason(), ValidationReason::Registry);
    }

    fn generated_origin(source: &SourceFile, depth: usize) -> Origin {
        let mut result = origin(source);
        for _ in 0..depth {
            result = Origin::Generated {
                cause: Box::new(result),
                reason: crate::source::GeneratedReason::TypeChecking,
            };
        }
        result
    }

    fn function_type(depth: usize) -> Type {
        let mut result = Type::Unit;
        for _ in 0..depth {
            result = Type::Function(Box::new(Type::Unit), Box::new(result));
        }
        result
    }

    fn nominal_application_type(owner: crate::types::NominalTypeId, depth: usize) -> Type {
        let mut result = Type::Nominal(owner);
        for _ in 0..depth {
            result = Type::Application(Box::new(result), Box::new(Type::Unit));
        }
        result
    }

    fn wide_nominal(
        owner: crate::types::NominalTypeId,
        spelling: &str,
        depth: usize,
        node_origin: &Origin,
    ) -> (
        crate::resolved::ResolvedNominalType,
        Vec<crate::resolved::ResolvedTypeVariable>,
    ) {
        (
            crate::resolved::ResolvedNominalType {
                representation_provenance: None,
                declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                representation: None,
                id: owner,
                spelling: spelling.into(),
                constructors: Box::new([]),
                origin: node_origin.clone(),
            },
            (0..depth)
                .map(|index| crate::resolved::ResolvedTypeVariable {
                    id: crate::types::TypeVariableId::new(
                        u32::try_from(index).expect("wide type parameter identity"),
                    ),
                    spelling: format!("T{index}"),
                    kind: crate::types::Kind::Type,
                    origin: node_origin.clone(),
                })
                .collect(),
        )
    }

    fn unchecked_identity_program(source: &SourceFile, result_depth: usize) -> UnvalidatedProgram {
        let arena = super::super::dialect::ArenaId::new(180);
        let binder = TypedBinder::new(
            arena,
            BinderId::new(0),
            function_type(result_depth),
            origin(source),
        );
        let body = NodeId::new(arena, 0);
        let root = NodeId::new(arena, 1);
        UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: binder.ty().clone(),
                    origin: Some(origin(source)),
                    kind: PureExprKind::Variable(super::super::variable::VariableNode::new(
                        binder.id(),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Function(
                        Box::new(binder.ty().clone()),
                        Box::new(binder.ty().clone()),
                    ),
                    origin: Some(origin(source)),
                    kind: PureExprKind::Value(PureValue::Function(
                        super::super::function::FunctionNode::new(binder, body),
                    )),
                },
            ],
            root,
        }
    }

    fn nested_tuple_pattern(source: &SourceFile, depth: usize) -> (Type, CorePattern) {
        let mut ty = Type::Unit;
        let mut pattern = CorePattern::new(Type::Unit, origin(source), CorePatternKind::Wildcard);
        for _ in 0..depth {
            ty = Type::Tuple(vec![ty, Type::Unit].into_boxed_slice());
            pattern = CorePattern::new(
                ty.clone(),
                origin(source),
                CorePatternKind::Tuple(
                    vec![
                        pattern,
                        CorePattern::new(Type::Unit, origin(source), CorePatternKind::Wildcard),
                    ]
                    .into_boxed_slice(),
                ),
            );
        }
        (ty, pattern)
    }

    fn unchecked_pattern_program(source: &SourceFile, depth: usize) -> UnvalidatedProgram {
        let arena = super::super::dialect::ArenaId::new(181);
        let (scrutinee_type, pattern) = nested_tuple_pattern(source, depth);
        let binder = TypedBinder::new(
            arena,
            BinderId::new(0),
            scrutinee_type.clone(),
            origin(source),
        );
        let scrutinee = NodeId::new(arena, 0);
        let body = NodeId::new(arena, 1);
        let matched = NodeId::new(arena, 2);
        let root = NodeId::new(arena, 3);
        UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: scrutinee_type.clone(),
                    origin: Some(origin(source)),
                    kind: PureExprKind::Variable(super::super::variable::VariableNode::new(
                        binder.id(),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Unit,
                    origin: Some(origin(source)),
                    kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Unit,
                    origin: Some(origin(source)),
                    kind: PureExprKind::Computation(PureComputation::Match(
                        super::super::data::MatchNode::new(
                            scrutinee,
                            vec![super::super::data::CoreMatchArm::new(
                                pattern,
                                body,
                                origin(source),
                            )],
                        ),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Function(Box::new(scrutinee_type), Box::new(Type::Unit)),
                    origin: Some(origin(source)),
                    kind: PureExprKind::Value(PureValue::Function(
                        super::super::function::FunctionNode::new(binder, matched),
                    )),
                },
            ],
            root,
        }
    }

    #[test]
    fn independent_validation_enforces_exact_payload_depth_boundaries() {
        let file = source();
        validate(
            unchecked_identity_program(&file, super::super::dialect::CORE_PAYLOAD_DEPTH_LIMIT - 1),
            &[&file],
        )
        .expect("the exact type-depth boundary validates");
        let error = validate(
            unchecked_identity_program(&file, super::super::dialect::CORE_PAYLOAD_DEPTH_LIMIT),
            &[&file],
        )
        .expect_err("one type wrapper beyond the boundary must fail");
        assert_eq!(error.reason(), ValidationReason::NodeType);

        for (depth, expected) in [
            (super::super::dialect::CORE_PAYLOAD_DEPTH_LIMIT, Ok(())),
            (
                super::super::dialect::CORE_PAYLOAD_DEPTH_LIMIT + 1,
                Err(ValidationReason::Provenance),
            ),
        ] {
            let arena = super::super::dialect::ArenaId::new(182);
            let program = UnvalidatedProgram {
                registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
                method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
                method_evidence_anchors: Box::new([]),
                arena,
                nodes: vec![StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Unit,
                    origin: Some(generated_origin(&file, depth)),
                    kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
                }],
                root: NodeId::new(arena, 0),
            };
            let actual = validate(program, &[&file])
                .map(|_| ())
                .map_err(|error| error.reason());
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn independent_validation_enforces_exact_pattern_depth_boundary() {
        let file = source();
        validate(
            unchecked_pattern_program(&file, CORE_PATTERN_DEPTH_LIMIT),
            &[&file],
        )
        .expect("the exact pattern-depth boundary validates");
        let error = validate(unchecked_pattern_program(&file, 41), &[&file])
            .expect_err("an unchecked 41-deep pattern must fail");
        assert_eq!(error.reason(), ValidationReason::Pattern);
    }

    #[test]
    fn rejected_deep_unchecked_node_is_disposed_on_a_small_stack() {
        std::thread::Builder::new()
            .name("core-validation-disposal".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let file = source();
                let arena = super::super::dialect::ArenaId::new(183);
                let program = UnvalidatedProgram {
                    registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
                    method_evidence: Arc::new(
                        super::super::dialect::MethodEvidenceCatalog::default(),
                    ),
                    method_evidence_anchors: Box::new([]),
                    arena,
                    nodes: vec![StoredNode {
                        dialect: DialectId::PURE,
                        effects: (),
                        ty: function_type(5_000),
                        origin: Some(origin(&file)),
                        kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
                    }],
                    root: NodeId::new(arena, 0),
                };
                let error = validate(program, &[&file]).expect_err("overdeep node type");
                assert_eq!(error.reason(), ValidationReason::NodeType);
            })
            .expect("validation disposal thread should start")
            .join()
            .expect("validation rejection and disposal must fit the small stack");
    }

    #[test]
    fn oversized_malformed_type_maps_directly_to_validation_resource() {
        let file = source();
        let arena = super::super::dialect::ArenaId::new(99);
        let oversized = Type::Tuple(vec![Type::Int; 2_000_000].into_boxed_slice());
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![StoredNode {
                dialect: DialectId::PURE,
                effects: (),
                ty: oversized,
                origin: Some(origin(&file)),
                kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
            }],
            root: NodeId::new(arena, 0),
        };

        let error = validate(program, &[&file]).expect_err("type work must be bounded");
        assert_eq!(error.reason(), ValidationReason::Resource);
    }

    #[test]
    fn core_validation_type_work_capacity_is_exact_and_atomic() {
        const EXPECTED_CAPACITY: usize = CORE_VALIDATION_TYPE_WORK_LIMIT;

        let file = source();
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena: super::super::dialect::ArenaId::new(195),
            nodes: Vec::new(),
            root: NodeId::new(super::super::dialect::ArenaId::new(195), 0),
        };
        let validator = Validator::new(&program, &[&file]);

        validator
            .charge_type_work(EXPECTED_CAPACITY)
            .expect("the independent Core validator admits its exact cumulative capacity");
        assert_eq!(validator.type_work.get(), EXPECTED_CAPACITY);
        let error = validator
            .charge_type_work(1)
            .expect_err("one unit beyond the cumulative capacity must fail");
        assert_eq!(error.reason(), ValidationReason::Resource);
        assert_eq!(
            validator.type_work.get(),
            EXPECTED_CAPACITY,
            "failed charges leave the cumulative ledger unchanged"
        );
    }

    #[test]
    fn one_cell_type_operation_observes_exact_validator_capacity() {
        const EXPECTED_CAPACITY: usize = CORE_VALIDATION_TYPE_WORK_LIMIT;

        let file = source();
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena: super::super::dialect::ArenaId::new(196),
            nodes: Vec::new(),
            root: NodeId::new(super::super::dialect::ArenaId::new(196), 0),
        };

        let exact = Validator::new(&program, &[&file]);
        exact
            .charge_type_work(EXPECTED_CAPACITY - 1)
            .expect("test setup leaves one comparison unit");
        assert!(
            exact
                .same_type_charged(&Type::Int, &Type::Int)
                .expect("one compared Type pair fits the final unit")
        );
        assert_eq!(exact.type_work.get(), EXPECTED_CAPACITY);

        let short = Validator::new(&program, &[&file]);
        short
            .charge_type_work(EXPECTED_CAPACITY)
            .expect("test setup exhausts the exact cumulative capacity");
        let error = short
            .same_type_charged(&Type::Int, &Type::Int)
            .expect_err("a one-cell comparison cannot cross the capacity");
        assert_eq!(error.reason(), ValidationReason::Resource);
        assert_eq!(
            short.type_work.get(),
            EXPECTED_CAPACITY,
            "the rejected comparison leaves the cumulative ledger unchanged"
        );
    }

    #[test]
    fn wide_type_validation_retains_constant_pending_work() {
        let file = source();
        let arena = super::super::dialect::ArenaId::new(184);
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![StoredNode {
                dialect: DialectId::PURE,
                effects: (),
                ty: Type::Tuple(
                    vec![Type::Int; CORE_VALIDATION_TYPE_WORK_LIMIT + 1].into_boxed_slice(),
                ),
                origin: Some(origin(&file)),
                kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
            }],
            root: NodeId::new(arena, 0),
        };
        let validator = Validator::new(&program, &[&file]);
        let error = validator
            .valid_type(Some(&program.nodes[0].ty))
            .expect_err("wide type must exhaust deterministic work");
        assert_eq!(error.reason(), ValidationReason::Resource);
        assert!(validator.type_validation_pending_peak.get() <= 2);
        drop(validator);
        program.discard_iteratively();
    }

    #[test]
    fn wide_pattern_binders_are_validated_incrementally_before_retention() {
        const WIDTH: usize = 100_000;
        const ALLOWANCE: usize = 64;
        let file = source();
        let origin = origin(&file);
        let arena = super::super::dialect::ArenaId::new(185);
        let patterns = (0..WIDTH)
            .map(|index| {
                CorePattern::new(
                    Type::Unit,
                    origin.clone(),
                    CorePatternKind::Binder(TypedBinder::new(
                        arena,
                        BinderId::new(u32::try_from(index).expect("binder identity")),
                        Type::Unit,
                        origin.clone(),
                    )),
                )
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let pattern = CorePattern::new(
            Type::Tuple(vec![Type::Unit; WIDTH].into_boxed_slice()),
            origin.clone(),
            CorePatternKind::Tuple(patterns),
        );
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![StoredNode {
                dialect: DialectId::PURE,
                effects: (),
                ty: Type::Unit,
                origin: Some(origin.clone()),
                kind: PureExprKind::Computation(PureComputation::Match(
                    super::super::data::MatchNode::new(
                        NodeId::new(arena, 0),
                        vec![super::super::data::CoreMatchArm::new(
                            pattern,
                            NodeId::new(arena, 0),
                            origin,
                        )],
                    ),
                )),
            }],
            root: NodeId::new(arena, 0),
        };
        let mut validator = Validator::new(&program, &[&file]);
        validator
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - ALLOWANCE)
            .expect("test setup leaves a small exact allowance");
        super::super::data::reset_binder_traversal_pending_peak();

        let error = validator
            .collect_binders(&HashSet::new())
            .expect_err("binder types must consume the remaining allowance");
        assert_eq!(error.reason(), ValidationReason::Resource);
        assert!(super::super::data::binder_traversal_pending_peak() <= 2);
        assert!(validator.binders.len() <= ALLOWANCE);
        drop(validator);
        program.discard_iteratively();
    }

    #[test]
    fn oversized_malformed_forall_maps_directly_to_validation_resource() {
        let file = source();
        let arena = super::super::dialect::ArenaId::new(100);
        let parameters = (0..CORE_VALIDATION_TYPE_WORK_LIMIT)
            .map(|index| {
                type_parameter(crate::types::TypeVariableId::new(
                    u32::try_from(index).expect("parameter identity"),
                ))
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![StoredNode {
                dialect: DialectId::PURE,
                effects: (),
                ty: Type::Forall(parameters, Box::new(Type::Unit)),
                origin: Some(origin(&file)),
                kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
            }],
            root: NodeId::new(arena, 0),
        };

        let error = validate(program, &[&file]).expect_err("quantifier work must be bounded");
        assert_eq!(error.reason(), ValidationReason::Resource);
    }

    #[test]
    fn type_scope_analysis_charges_retained_free_variables() {
        let file = source();
        let arena = super::super::dialect::ArenaId::new(101);
        let parameter = crate::types::TypeVariableId::new(0);
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Variable(parameter),
                    origin: Some(origin(&file)),
                    kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Forall(
                        vec![type_parameter(parameter)].into_boxed_slice(),
                        Box::new(Type::Variable(parameter)),
                    ),
                    origin: Some(origin(&file)),
                    kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                        super::super::type_ops::TypeAbstractionNode::new(
                            vec![type_parameter(parameter)],
                            NodeId::new(arena, 0),
                        ),
                    )),
                },
            ],
            root: NodeId::new(arena, 1),
        };
        let validator = Validator::new(&program, &[&file]);
        validator
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - 3)
            .expect("test setup leaves the old structural allowance");

        let error = validator
            .validate_type_scopes()
            .expect_err("retained type-scope requirements must be charged");
        assert_eq!(error.reason(), ValidationReason::Resource);
    }

    #[test]
    fn linear_type_scope_chain_uses_the_exact_proportional_budget() {
        const WIDTH: usize = 4_096;
        // The predecessor scope formula is 5W + 2. The outer Forall now also
        // visits one fixed Kind node for each of its W binder records.
        const EXPECTED_WORK: usize = 6 * WIDTH + 2;
        let file = source();
        let origin = origin(&file);
        let arena = super::super::dialect::ArenaId::new(104);
        let parameter_ids = (0..WIDTH)
            .map(|index| {
                crate::types::TypeVariableId::new(u32::try_from(index).expect("parameter identity"))
            })
            .collect::<Vec<_>>();
        let mut nodes = vec![StoredNode {
            dialect: DialectId::PURE,
            effects: (),
            ty: Type::Unit,
            origin: Some(origin.clone()),
            kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
        }];
        for (index, parameter) in parameter_ids.iter().copied().enumerate() {
            nodes.push(StoredNode {
                dialect: DialectId::PURE,
                effects: (),
                ty: Type::Unit,
                origin: Some(origin.clone()),
                kind: PureExprKind::Computation(PureComputation::TypeApplication(
                    super::super::type_ops::TypeApplicationNode::new(
                        NodeId::new(arena, u32::try_from(index).expect("previous node identity")),
                        vec![Type::Variable(parameter)],
                    ),
                )),
            });
        }
        let body = NodeId::new(arena, u32::try_from(WIDTH).expect("body identity"));
        let root = NodeId::new(arena, u32::try_from(WIDTH + 1).expect("root node identity"));
        nodes.push(StoredNode {
            dialect: DialectId::PURE,
            effects: (),
            ty: Type::Forall(
                type_parameters(parameter_ids.iter().copied()).into_boxed_slice(),
                Box::new(Type::Unit),
            ),
            origin: Some(origin),
            kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                super::super::type_ops::TypeAbstractionNode::new(
                    type_parameters(parameter_ids),
                    body,
                ),
            )),
        });
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes,
            root,
        };
        let validator = Validator::new(&program, &[&file]);
        validator
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - EXPECTED_WORK)
            .expect("test setup leaves the exact proportional allowance");

        validator
            .validate_type_scopes()
            .expect("the linear scope chain fits its proportional allowance");
        assert_eq!(
            validator
                .charge_type_work(1)
                .expect_err("scope traversal consumed its exact allowance")
                .reason(),
            ValidationReason::Resource
        );
    }

    #[test]
    fn type_scope_requirements_handle_shared_and_nested_abstractions() {
        let file = source();
        let origin = origin(&file);
        let arena = super::super::dialect::ArenaId::new(105);
        let parameter = crate::types::TypeVariableId::new(0);
        let outer_parameter = crate::types::TypeVariableId::new(1);
        let occurrence = NodeId::new(arena, 0);
        let inner = NodeId::new(arena, 1);
        let left = NodeId::new(arena, 2);
        let right = NodeId::new(arena, 3);
        let root = NodeId::new(arena, 4);
        let scheme = Type::Forall(
            vec![type_parameter(parameter)].into_boxed_slice(),
            Box::new(Type::Variable(parameter)),
        );
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Variable(parameter),
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: scheme.clone(),
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                        super::super::type_ops::TypeAbstractionNode::new(
                            vec![type_parameter(parameter)],
                            occurrence,
                        ),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Forall(
                        vec![type_parameter(outer_parameter)].into_boxed_slice(),
                        Box::new(Type::Unit),
                    ),
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                        super::super::type_ops::TypeAbstractionNode::new(
                            vec![type_parameter(outer_parameter)],
                            inner,
                        ),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: scheme,
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                        super::super::type_ops::TypeAbstractionNode::new(
                            vec![type_parameter(parameter)],
                            occurrence,
                        ),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Tuple(vec![Type::Unit, Type::Unit].into_boxed_slice()),
                    origin: Some(origin),
                    kind: PureExprKind::Computation(PureComputation::Tuple(
                        super::super::data::TupleNode::new(vec![left, right]),
                    )),
                },
            ],
            root,
        };

        Validator::new(&program, &[&file])
            .validate_type_scopes()
            .expect("both paths to the shared occurrence bind its type identity");
    }

    #[test]
    fn forall_validation_charges_the_exact_quantifier_boundary() {
        let file = source();
        let arena = super::super::dialect::ArenaId::new(102);
        let parameters = vec![
            type_parameter(crate::types::TypeVariableId::new(0)),
            type_parameter(crate::types::TypeVariableId::new(1)),
        ]
        .into_boxed_slice();
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![StoredNode {
                dialect: DialectId::PURE,
                effects: (),
                ty: Type::Unit,
                origin: Some(origin(&file)),
                kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
            }],
            root: NodeId::new(arena, 0),
        };
        let validator = Validator::new(&program, &[&file]);
        validator
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - 6)
            .expect("test setup leaves six type-work cells");

        assert!(
            validator
                .valid_type(Some(&Type::Forall(parameters, Box::new(Type::Unit))))
                .expect("the exact Forall, binder-record, Kind-node, and body boundary validates")
        );
        let error = validator
            .valid_type(Some(&Type::Unit))
            .expect_err("the exact boundary leaves no uncharged work");
        assert_eq!(error.reason(), ValidationReason::Resource);
    }

    #[test]
    fn type_operation_validation_charges_binders_and_application_index_entries() {
        let file = source();
        let origin = origin(&file);
        let arena = super::super::dialect::ArenaId::new(103);
        let parameter = crate::types::TypeVariableId::new(0);
        let body = NodeId::new(arena, 0);
        let abstraction = NodeId::new(arena, 1);
        let application = NodeId::new(arena, 2);
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Unit,
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Forall(
                        vec![type_parameter(parameter)].into_boxed_slice(),
                        Box::new(Type::Unit),
                    ),
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                        super::super::type_ops::TypeAbstractionNode::new(
                            vec![type_parameter(parameter)],
                            body,
                        ),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Unit,
                    origin: Some(origin),
                    kind: PureExprKind::Computation(PureComputation::TypeApplication(
                        super::super::type_ops::TypeApplicationNode::new(
                            abstraction,
                            vec![Type::Int],
                        ),
                    )),
                },
            ],
            root: application,
        };
        let binder_kind = Kind::Type;
        let type_binders = HashMap::from([(parameter, (&binder_kind, abstraction))]);

        let abstraction_validator = Validator::new(&program, &[&file]);
        abstraction_validator
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - 8)
            .expect("test setup leaves the exact abstraction allowance");
        abstraction_validator
            .validate_computation(
                abstraction,
                &program.nodes[1],
                match &program.nodes[1].kind {
                    PureExprKind::Computation(computation) => computation,
                    _ => unreachable!("test abstraction computation"),
                },
                &type_binders,
                &HashMap::new(),
                false,
            )
            .expect("binder payload, scheme pair, body, and result kind fit exactly");
        assert_eq!(
            abstraction_validator
                .charge_type_work(1)
                .expect_err("the binder consumed the remaining work")
                .reason(),
            ValidationReason::Resource
        );

        let application_validator = Validator::new(&program, &[&file]);
        application_validator
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - 6)
            .expect("test setup leaves synthesis, comparison, clone, index, substitution, and result comparison work");
        application_validator
            .validate_computation(
                application,
                &program.nodes[2],
                match &program.nodes[2].kind {
                    PureExprKind::Computation(computation) => computation,
                    _ => unreachable!("test application computation"),
                },
                &type_binders,
                &HashMap::new(),
                false,
            )
            .expect("one argument validation, clone, replacement entry, and result fit exactly");
        assert_eq!(
            application_validator
                .charge_type_work(1)
                .expect_err("type application consumed the remaining work")
                .reason(),
            ValidationReason::Resource
        );
    }

    #[test]
    fn phantom_type_application_charges_argument_clones_at_the_exact_boundary() {
        const WIDTH: usize = 64;
        const ARGUMENT_CELLS: usize = WIDTH + 1;
        // Synthesis visits each Type cell and compares each tuple child to
        // Kind::Type, then validation revisits the argument for its retained
        // substitution clone. The final three units are expected-Kind
        // comparison, replacement storage, and substituted-result comparison.
        const EXPECTED_WORK: usize = ARGUMENT_CELLS * 3 + 3;
        let file = source();
        let origin = origin(&file);
        let arena = super::super::dialect::ArenaId::new(106);
        let parameter = crate::types::TypeVariableId::new(0);
        let body = NodeId::new(arena, 0);
        let abstraction = NodeId::new(arena, 1);
        let application = NodeId::new(arena, 2);
        let argument = Type::Tuple(vec![Type::Int; WIDTH].into_boxed_slice());
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Unit,
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Forall(
                        vec![type_parameter(parameter)].into_boxed_slice(),
                        Box::new(Type::Unit),
                    ),
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                        super::super::type_ops::TypeAbstractionNode::new(
                            vec![type_parameter(parameter)],
                            body,
                        ),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Unit,
                    origin: Some(origin),
                    kind: PureExprKind::Computation(PureComputation::TypeApplication(
                        super::super::type_ops::TypeApplicationNode::new(
                            abstraction,
                            vec![argument],
                        ),
                    )),
                },
            ],
            root: application,
        };
        let computation = match &program.nodes[2].kind {
            PureExprKind::Computation(computation) => computation,
            _ => unreachable!("test application computation"),
        };

        let exact_validator = Validator::new(&program, &[&file]);
        exact_validator
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - EXPECTED_WORK)
            .expect("test setup leaves the exact retained-work allowance");
        exact_validator
            .validate_computation(
                application,
                &program.nodes[2],
                computation,
                &HashMap::new(),
                &HashMap::new(),
                false,
            )
            .expect("the exact argument-validation and clone allowance fits");
        assert_eq!(
            exact_validator
                .charge_type_work(1)
                .expect_err("the exact allowance is fully consumed")
                .reason(),
            ValidationReason::Resource
        );

        let short_validator = Validator::new(&program, &[&file]);
        short_validator
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - (EXPECTED_WORK - 1))
            .expect("test setup leaves one cell less than the retained work");
        let error = short_validator
            .validate_computation(
                application,
                &program.nodes[2],
                computation,
                &HashMap::new(),
                &HashMap::new(),
                false,
            )
            .expect_err("argument clones must not cross the validation budget");
        assert_eq!(error.reason(), ValidationReason::Resource);
    }

    #[test]
    fn constructor_pattern_substitutions_precharge_phantom_argument_clones() {
        const WIDTH: usize = 64;
        // W application nodes + W argument leaves + one nominal head.
        const ROOT_TYPE_CELLS: usize = WIDTH * 2 + 1;
        const HEAD_INSPECTION: usize = WIDTH + 1;
        const REPLACEMENT_STORAGE: usize = WIDTH * 2;
        const PAYLOAD_WORK: usize = 3;
        // The pattern/expected agreement comparison visits the complete root
        // before replacement storage and substitution are admitted.
        const ROOT_COMPARISON: usize = ROOT_TYPE_CELLS;
        const EXACT_WORK: usize = ROOT_COMPARISON
            + ROOT_TYPE_CELLS
            + HEAD_INSPECTION
            + REPLACEMENT_STORAGE
            + PAYLOAD_WORK;

        let file = source();
        let node_origin = origin(&file);
        let arena = super::super::dialect::ArenaId::new(108);
        let owner = crate::types::NominalTypeId::new(file.id(), 0);
        let constructor = ConstructorId::new(owner, 0);
        let parameters = (0..WIDTH)
            .map(|index| crate::resolved::ResolvedTypeVariable {
                id: crate::types::TypeVariableId::new(
                    u32::try_from(index).expect("parameter identity"),
                ),
                spelling: format!("T{index}"),
                kind: crate::types::Kind::Type,
                origin: node_origin.clone(),
            })
            .collect();
        let registry = crate::resolved::ResolvedRegistry::new(
            vec![crate::resolved::ResolvedNominalType {
                representation_provenance: None,
                declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                representation: None,
                id: owner,
                spelling: "Wide".into(),
                constructors: vec![constructor].into_boxed_slice(),
                origin: node_origin.clone(),
            }],
            vec![crate::resolved::ResolvedConstructor {
                id: constructor,
                owner,
                spelling: "Make".into(),
                payload: Some(Type::Int),
                origin: node_origin.clone(),
            }],
        )
        .with_type_parameters(vec![(owner, parameters)]);
        let expected = Type::apply_arguments(Type::Nominal(owner), vec![Type::Bool; WIDTH]);
        let pattern = CorePattern::new(
            expected.clone(),
            node_origin.clone(),
            CorePatternKind::Constructor {
                constructor,
                payload: Some(Box::new(CorePattern::new(
                    Type::Int,
                    node_origin.clone(),
                    CorePatternKind::Wildcard,
                ))),
            },
        );
        let program = UnvalidatedProgram {
            registry: Arc::new(registry),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![StoredNode {
                dialect: DialectId::PURE,
                effects: (),
                ty: Type::Unit,
                origin: Some(node_origin),
                kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
            }],
            root: NodeId::new(arena, 0),
        };
        let node = program.root;

        let exact = Validator::new(&program, &[&file]);
        exact
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - EXACT_WORK)
            .expect("test setup leaves the exact complete allowance");
        exact
            .validate_pattern(&pattern, &expected, node)
            .expect("the exact pattern and substitution allowance fits");
        assert_eq!(
            exact
                .charge_type_work(1)
                .expect_err("the exact allowance is fully consumed")
                .reason(),
            ValidationReason::Resource
        );

        let preflight_short = Validator::new(&program, &[&file]);
        preflight_short
            .charge_type_work(
                CORE_VALIDATION_TYPE_WORK_LIMIT
                    - (ROOT_COMPARISON + ROOT_TYPE_CELLS + HEAD_INSPECTION + REPLACEMENT_STORAGE
                        - 1),
            )
            .expect("test setup leaves one cell fewer than replacement preflight");
        let error = preflight_short
            .validate_pattern(&pattern, &expected, node)
            .expect_err("replacement clones must be rejected before allocation");
        assert_eq!(error.reason(), ValidationReason::Resource);
    }

    #[test]
    fn distinct_type_abstractions_cannot_reuse_one_binder_identity() {
        let file = source();
        let origin = origin(&file);
        let arena = super::super::dialect::ArenaId::new(107);
        let parameter = crate::types::TypeVariableId::new(0);
        let left_body = NodeId::new(arena, 0);
        let right_body = NodeId::new(arena, 1);
        let left_abstraction = NodeId::new(arena, 2);
        let right_abstraction = NodeId::new(arena, 3);
        let left = NodeId::new(arena, 4);
        let right = NodeId::new(arena, 5);
        let root = NodeId::new(arena, 6);
        let scheme = Type::Forall(
            vec![type_parameter(parameter)].into_boxed_slice(),
            Box::new(Type::Unit),
        );
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Unit,
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Unit,
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: scheme.clone(),
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                        super::super::type_ops::TypeAbstractionNode::new(
                            vec![type_parameter(parameter)],
                            left_body,
                        ),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: scheme,
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                        super::super::type_ops::TypeAbstractionNode::new(
                            vec![type_parameter(parameter)],
                            right_body,
                        ),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Unit,
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Computation(PureComputation::TypeApplication(
                        super::super::type_ops::TypeApplicationNode::new(
                            left_abstraction,
                            vec![Type::Unit],
                        ),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Unit,
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Computation(PureComputation::TypeApplication(
                        super::super::type_ops::TypeApplicationNode::new(
                            right_abstraction,
                            vec![Type::Unit],
                        ),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Tuple(vec![Type::Unit, Type::Unit].into_boxed_slice()),
                    origin: Some(origin),
                    kind: PureExprKind::Computation(PureComputation::Tuple(
                        super::super::data::TupleNode::new(vec![left, right]),
                    )),
                },
            ],
            root,
        };

        let error = validate(program, &[&file])
            .expect_err("distinct abstraction nodes must define distinct type-variable identities");
        assert_eq!(error.reason(), ValidationReason::TypeOperation);
        assert_eq!(error.node(), Some(right_abstraction));
    }

    #[test]
    fn constructor_owner_membership_uses_the_identity_index_for_wide_declarations() {
        const WIDTH: u32 = 10_000;
        let file = source();
        let nominal = crate::types::NominalTypeId::new(file.id(), 0);
        let constructors = (0..WIDTH)
            .map(|index| ConstructorId::new(nominal, index))
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let owner = crate::resolved::ResolvedNominalType {
            representation_provenance: None,
            declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
            representation: None,
            id: nominal,
            spelling: "Wide".into(),
            constructors,
            origin: origin(&file),
        };

        assert!(constructor_belongs_to_owner(
            &owner,
            ConstructorId::new(nominal, WIDTH - 1)
        ));
        assert!(!constructor_belongs_to_owner(
            &owner,
            ConstructorId::new(nominal, WIDTH)
        ));
        assert!(!constructor_belongs_to_owner(
            &owner,
            ConstructorId::new(crate::types::NominalTypeId::new(file.id(), 1), WIDTH - 1,)
        ));
    }

    #[test]
    fn constructor_payload_owner_parameters_are_indexed_once() {
        const PARAMETERS: u32 = 64;
        const CONSTRUCTORS: u32 = 64;
        let file = SourceFile::new("test.ash", "x".repeat(CONSTRUCTORS as usize + 1))
            .expect("test source");
        let registry_origin = Origin::Source(
            file.span(ByteRange::new(0, CONSTRUCTORS + 1).expect("ordered registry range"))
                .expect("registry span"),
        );
        let nominal = crate::types::NominalTypeId::new(file.id(), 0);
        let constructors = (0..CONSTRUCTORS)
            .map(|index| ConstructorId::new(nominal, index))
            .collect::<Vec<_>>();
        let registry = crate::resolved::ResolvedRegistry::new(
            vec![crate::resolved::ResolvedNominalType {
                representation_provenance: None,
                declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                representation: None,
                id: nominal,
                spelling: "Wide".into(),
                constructors: constructors.clone().into_boxed_slice(),
                origin: registry_origin.clone(),
            }],
            constructors
                .into_iter()
                .enumerate()
                .map(|(index, id)| crate::resolved::ResolvedConstructor {
                    id,
                    owner: nominal,
                    spelling: format!("C{index}"),
                    payload: Some(Type::Variable(crate::types::TypeVariableId::new(
                        u32::try_from(index).expect("constructor index should fit") % PARAMETERS,
                    ))),
                    origin: Origin::Source(
                        file.span(
                            ByteRange::new(
                                u32::try_from(index).expect("constructor index should fit"),
                                u32::try_from(index + 1).expect("constructor index should fit"),
                            )
                            .expect("ordered constructor range"),
                        )
                        .expect("constructor span"),
                    ),
                })
                .collect(),
        )
        .with_type_parameters(vec![(
            nominal,
            (0..PARAMETERS)
                .map(|index| crate::resolved::ResolvedTypeVariable {
                    id: crate::types::TypeVariableId::new(index),
                    spelling: format!("A{index}"),
                    kind: crate::types::Kind::Type,
                    origin: Origin::Source(
                        file.span(
                            ByteRange::new(index, index + 1).expect("ordered parameter range"),
                        )
                        .expect("parameter span"),
                    ),
                })
                .collect(),
        )]);
        let mut builder = CoreBuilder::with_registry(Arc::new(registry));
        let root = builder
            .unit(Type::Unit, registry_origin)
            .expect("unit root");
        let program = builder.finish(root).expect("root");
        let validator = Validator::new(&program, &[&file]);

        let result = validator.validate_registry();
        assert!(
            result.is_ok(),
            "indexed parameterized registry should validate after {} index insertions: {result:?}",
            validator.owner_parameter_index_work.get()
        );

        assert_eq!(
            validator.owner_parameter_index_work.get(),
            PARAMETERS as usize
        );
    }

    #[test]
    fn registry_canonical_binder_kind_authentication_is_exact_and_stack_safe() {
        const DEPTH: usize = 32_768;
        const KIND_NODES: usize = 2 * DEPTH + 1;
        // The canonical registry scan visits one binder record. Authenticating
        // it against its ordered nominal record visits a second record plus
        // every pair of Kind nodes.
        const EXACT_WORK: usize = KIND_NODES + 2;

        fn deep_kind() -> crate::types::Kind {
            let mut kind = crate::types::Kind::Type;
            for _ in 0..DEPTH {
                kind =
                    crate::types::Kind::Arrow(Box::new(crate::types::Kind::Type), Box::new(kind));
            }
            kind
        }

        fn registry_program(
            file: &SourceFile,
            module: Option<ModuleId>,
            canonical_kind: Option<crate::types::Kind>,
        ) -> UnvalidatedProgram {
            let owner = module.unwrap_or_else(|| file.id().into());
            let nominal = crate::types::NominalTypeId::new(owner, 0);
            let constructor = ConstructorId::new(nominal, 0);
            let parameter = module.map_or_else(
                || crate::types::TypeVariableId::new(0),
                |module| crate::types::TypeVariableId::resolved(module, 0),
            );
            let registry = crate::resolved::ResolvedRegistry::new(
                vec![crate::resolved::ResolvedNominalType {
                    representation_provenance: None,
                    declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                    representation: None,
                    id: nominal,
                    spelling: "Holder".into(),
                    constructors: Box::new([constructor]),
                    origin: range_origin(file, 0, 13),
                }],
                vec![crate::resolved::ResolvedConstructor {
                    id: constructor,
                    owner: nominal,
                    spelling: "Make".into(),
                    payload: None,
                    origin: range_origin(file, 9, 13),
                }],
            )
            .with_type_parameters(vec![(
                nominal,
                vec![crate::resolved::ResolvedTypeVariable {
                    id: parameter,
                    spelling: "F".into(),
                    kind: deep_kind(),
                    origin: range_origin(file, 7, 8),
                }],
            )]);
            let registry = match canonical_kind {
                Some(kind) => registry.with_additional_type_variables([
                    crate::resolved::ResolvedTypeVariable {
                        id: parameter,
                        spelling: "F".into(),
                        kind,
                        origin: range_origin(file, 7, 8),
                    },
                ]),
                None => registry,
            };
            let mut builder = CoreBuilder::with_registry(Arc::new(registry));
            let root = builder
                .unit(Type::Unit, range_origin(file, 0, 13))
                .expect("the registry fixture root should fit");
            builder
                .finish(root)
                .expect("the registry fixture should finish")
        }

        std::thread::Builder::new()
            .name("core-registry-kind-authentication".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let file = SourceFile::new("registry-kind.ash", "Holder F Make")
                    .expect("the registry fixture source should fit");

                let exact_program = registry_program(&file, None, None);
                let exact = Validator::new(&exact_program, &[&file]);
                exact
                    .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - EXACT_WORK)
                    .expect("the exact fixture precharge should fit");
                exact
                    .validate_registry()
                    .expect("the exact binder-kind authentication budget should fit");
                assert_eq!(exact.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);

                let short_program = registry_program(&file, None, None);
                let short = Validator::new(&short_program, &[&file]);
                short
                    .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - (EXACT_WORK - 1))
                    .expect("the one-short fixture precharge should fit");
                let error = short
                    .validate_registry()
                    .expect_err("one missing Kind-pair visit must reject validation");
                assert_eq!(error.reason(), ValidationReason::Resource);
                assert_eq!(short.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);

                let mismatched_program =
                    registry_program(&file, None, Some(crate::types::Kind::Type));
                let mismatched = Validator::new(&mismatched_program, &[&file]);
                let error = mismatched
                    .validate_registry()
                    .expect_err("canonical and ordered binder kinds must agree");
                assert_eq!(error.reason(), ValidationReason::Registry);

                let module = ModuleId::new(47);
                let module_program = registry_program(&file, Some(module), None);
                let module_validator =
                    Validator::new_modules(&module_program, &[&file], &[(module, file.id())])
                        .expect("the module/source relation should be valid");
                module_validator
                    .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - EXACT_WORK)
                    .expect("the module fixture precharge should fit");
                module_validator
                    .validate_registry()
                    .expect("the module registry Kind authentication budget should fit");
                assert_eq!(
                    module_validator.type_work.get(),
                    CORE_VALIDATION_TYPE_WORK_LIMIT
                );

                let short_module_program = registry_program(&file, Some(module), None);
                let short_module_validator =
                    Validator::new_modules(&short_module_program, &[&file], &[(module, file.id())])
                        .expect("the one-short module/source relation should be valid");
                short_module_validator
                    .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - (EXACT_WORK - 1))
                    .expect("the one-short module fixture precharge should fit");
                let error = short_module_validator.validate_registry().expect_err(
                    "one missing module-registry Kind-pair visit must reject validation",
                );
                assert_eq!(error.reason(), ValidationReason::Resource);
                assert_eq!(
                    short_module_validator.type_work.get(),
                    CORE_VALIDATION_TYPE_WORK_LIMIT
                );
            })
            .expect("the Core registry authentication thread should start")
            .join()
            .expect("deep Core registry Kind authentication must remain stack-safe");
    }

    #[test]
    fn registry_payload_kind_validation_is_exact_and_stack_safe() {
        const DEPTH: usize = 32_768;
        const KIND_NODES: usize = 2 * DEPTH + 1;
        // Synthesizing the payload variable retains every canonical Kind node;
        // the final comparison to Kind::Type visits one mismatching root pair.
        const EXACT_WORK: usize = KIND_NODES + 1;

        fn deep_kind() -> Kind {
            let mut kind = Kind::Type;
            for _ in 0..DEPTH {
                kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
            }
            kind
        }

        fn program(
            file: &SourceFile,
        ) -> (
            UnvalidatedProgram,
            crate::types::NominalTypeId,
            crate::types::TypeVariableId,
        ) {
            let owner = crate::types::NominalTypeId::new(file.id(), 0);
            let constructor = ConstructorId::new(owner, 0);
            let parameter = crate::types::TypeVariableId::new(0);
            let registry = crate::resolved::ResolvedRegistry::new(
                vec![crate::resolved::ResolvedNominalType {
                    representation_provenance: None,
                    declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                    representation: None,
                    id: owner,
                    spelling: "Holder".into(),
                    constructors: Box::new([constructor]),
                    origin: range_origin(file, 0, 13),
                }],
                vec![crate::resolved::ResolvedConstructor {
                    id: constructor,
                    owner,
                    spelling: "Make".into(),
                    payload: Some(Type::Variable(parameter)),
                    origin: range_origin(file, 9, 13),
                }],
            )
            .with_type_parameters(vec![(
                owner,
                vec![crate::resolved::ResolvedTypeVariable {
                    id: parameter,
                    spelling: "F".into(),
                    kind: deep_kind(),
                    origin: range_origin(file, 7, 8),
                }],
            )]);
            let mut builder = CoreBuilder::with_registry(Arc::new(registry));
            let root = builder
                .unit(Type::Unit, range_origin(file, 0, 13))
                .expect("registry payload fixture root");
            (
                builder.finish(root).expect("registry payload fixture"),
                owner,
                parameter,
            )
        }

        std::thread::Builder::new()
            .name("core-registry-payload-kind".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let file = SourceFile::new("payload-kind.ash", "Holder F Make")
                    .expect("registry payload fixture source");

                let (exact_program, owner, parameter) = program(&file);
                let exact_owners =
                    HashMap::from([(parameter, RegistryParameterOwner::Nominal(owner))]);
                let exact = Validator::new(&exact_program, &[&file]);
                exact
                    .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - EXACT_WORK)
                    .expect("exact payload-kind precharge");
                assert_eq!(
                    exact.valid_registry_payload_kind(
                        Some(&Type::Variable(parameter)),
                        owner,
                        &exact_owners,
                    ),
                    Ok(false)
                );
                assert_eq!(exact.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);

                let (short_program, owner, parameter) = program(&file);
                let short_owners =
                    HashMap::from([(parameter, RegistryParameterOwner::Nominal(owner))]);
                let short = Validator::new(&short_program, &[&file]);
                short
                    .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - (EXACT_WORK - 1))
                    .expect("one-short payload-kind precharge");
                let error = short
                    .valid_registry_payload_kind(
                        Some(&Type::Variable(parameter)),
                        owner,
                        &short_owners,
                    )
                    .expect_err("one missing Kind-pair visit must reject validation");
                assert_eq!(error.reason(), ValidationReason::Resource);
                assert_eq!(short.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);
            })
            .expect("small-stack payload-kind thread")
            .join()
            .expect("payload Kind failure teardown must remain stack-safe");
    }

    #[test]
    fn registry_payload_accepts_owner_parameter_application() {
        let file = source();
        let owner = crate::types::NominalTypeId::new(file.id(), 0);
        let parameter = crate::types::TypeVariableId::new(0);
        let registry = crate::resolved::ResolvedRegistry::new(
            vec![crate::resolved::ResolvedNominalType {
                representation_provenance: None,
                declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                representation: None,
                id: owner,
                spelling: "Holder".into(),
                constructors: Box::new([]),
                origin: origin(&file),
            }],
            Vec::new(),
        )
        .with_type_parameters(vec![(
            owner,
            vec![crate::resolved::ResolvedTypeVariable {
                id: parameter,
                spelling: "F".into(),
                kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                origin: origin(&file),
            }],
        )]);
        let arena = super::super::dialect::ArenaId::new(197);
        let program = UnvalidatedProgram {
            registry: Arc::new(registry),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: Vec::new(),
            root: NodeId::new(arena, 0),
        };
        let validator = Validator::new(&program, &[&file]);
        let parameter_owners = HashMap::from([(parameter, RegistryParameterOwner::Nominal(owner))]);
        let payload = Type::Application(Box::new(Type::Variable(parameter)), Box::new(Type::Int));

        assert_eq!(
            validator.valid_registry_payload(Some(&payload), owner, &parameter_owners),
            Ok(true),
            "structural admission must leave parameter applicability to total kind synthesis"
        );
        assert_eq!(
            validator.valid_registry_payload_kind(Some(&payload), owner, &parameter_owners),
            Ok(true)
        );
    }

    #[test]
    fn registry_payload_accepts_partial_nominal_higher_kind_argument() {
        let file = source();
        let pair = crate::types::NominalTypeId::new(file.id(), 0);
        let higher = crate::types::NominalTypeId::new(file.id(), 1);
        let owner = crate::types::NominalTypeId::new(file.id(), 2);
        let left = crate::types::TypeVariableId::new(0);
        let right = crate::types::TypeVariableId::new(1);
        let constructor_parameter = crate::types::TypeVariableId::new(2);
        let registry = crate::resolved::ResolvedRegistry::new(
            vec![
                crate::resolved::ResolvedNominalType {
                    representation_provenance: None,
                    declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                    representation: None,
                    id: pair,
                    spelling: "Pair".into(),
                    constructors: Box::new([]),
                    origin: origin(&file),
                },
                crate::resolved::ResolvedNominalType {
                    representation_provenance: None,
                    declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                    representation: None,
                    id: higher,
                    spelling: "Higher".into(),
                    constructors: Box::new([]),
                    origin: origin(&file),
                },
                crate::resolved::ResolvedNominalType {
                    representation_provenance: None,
                    declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                    representation: None,
                    id: owner,
                    spelling: "Use".into(),
                    constructors: Box::new([]),
                    origin: origin(&file),
                },
            ],
            Vec::new(),
        )
        .with_type_parameters(vec![
            (
                pair,
                vec![
                    crate::resolved::ResolvedTypeVariable {
                        id: left,
                        spelling: "A".into(),
                        kind: Kind::Type,
                        origin: origin(&file),
                    },
                    crate::resolved::ResolvedTypeVariable {
                        id: right,
                        spelling: "B".into(),
                        kind: Kind::Type,
                        origin: origin(&file),
                    },
                ],
            ),
            (
                higher,
                vec![crate::resolved::ResolvedTypeVariable {
                    id: constructor_parameter,
                    spelling: "F".into(),
                    kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                    origin: origin(&file),
                }],
            ),
        ]);
        let arena = super::super::dialect::ArenaId::new(198);
        let program = UnvalidatedProgram {
            registry: Arc::new(registry),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: Vec::new(),
            root: NodeId::new(arena, 0),
        };
        let validator = Validator::new(&program, &[&file]);
        let parameter_owners = HashMap::from([
            (left, RegistryParameterOwner::Nominal(pair)),
            (right, RegistryParameterOwner::Nominal(pair)),
            (
                constructor_parameter,
                RegistryParameterOwner::Nominal(higher),
            ),
        ]);
        let partial_pair = Type::Application(Box::new(Type::Nominal(pair)), Box::new(Type::Int));
        let payload = Type::Application(Box::new(Type::Nominal(higher)), Box::new(partial_pair));

        assert_eq!(
            validator.valid_registry_payload(Some(&payload), owner, &parameter_owners),
            Ok(true),
            "partial nominal constructors are structurally valid monotypes"
        );
        assert_eq!(
            validator.valid_registry_payload_kind(Some(&payload), owner, &parameter_owners),
            Ok(true)
        );
    }

    #[test]
    fn registry_payload_wrong_domain_is_owned_by_kind_synthesis() {
        let file = source();
        let owner = crate::types::NominalTypeId::new(file.id(), 0);
        let parameter = crate::types::TypeVariableId::new(0);
        let registry = crate::resolved::ResolvedRegistry::new(
            vec![crate::resolved::ResolvedNominalType {
                representation_provenance: None,
                declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                representation: None,
                id: owner,
                spelling: "Holder".into(),
                constructors: Box::new([]),
                origin: origin(&file),
            }],
            Vec::new(),
        )
        .with_type_parameters(vec![(
            owner,
            vec![crate::resolved::ResolvedTypeVariable {
                id: parameter,
                spelling: "F".into(),
                kind: Kind::Arrow(
                    Box::new(Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))),
                    Box::new(Kind::Type),
                ),
                origin: origin(&file),
            }],
        )]);
        let arena = super::super::dialect::ArenaId::new(199);
        let program = UnvalidatedProgram {
            registry: Arc::new(registry),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: Vec::new(),
            root: NodeId::new(arena, 0),
        };
        let validator = Validator::new(&program, &[&file]);
        let parameter_owners = HashMap::from([(parameter, RegistryParameterOwner::Nominal(owner))]);
        let payload = Type::Application(Box::new(Type::Variable(parameter)), Box::new(Type::Int));

        assert_eq!(
            validator.valid_registry_payload(Some(&payload), owner, &parameter_owners),
            Ok(true),
            "structural validation must not duplicate the Kind domain rule"
        );
        assert_eq!(
            validator.valid_registry_payload_kind(Some(&payload), owner, &parameter_owners),
            Ok(false),
            "the total Kind judgment owns the wrong-domain rejection"
        );
    }

    #[test]
    fn rejects_malformed_additional_registry_type_variable_metadata() {
        let file = source();
        let foreign = SourceFile::new("foreign.ash", "A").expect("foreign source");
        let parameter_origin = Origin::Source(
            file.span(ByteRange::new(0, 1).expect("ordered parameter range"))
                .expect("parameter span"),
        );
        let registry =
            crate::resolved::ResolvedRegistry::default().with_additional_type_variables([
                crate::resolved::ResolvedTypeVariable {
                    id: crate::types::TypeVariableId::new(0),
                    spelling: "lowercase".into(),
                    kind: crate::types::Kind::Type,
                    origin: parameter_origin,
                },
            ]);
        let mut builder = CoreBuilder::with_registry(Arc::new(registry));
        let root = builder.unit(Type::Unit, origin(&file)).expect("unit root");

        let error = validate(builder.finish(root).expect("root"), &[&file])
            .expect_err("additional type-variable metadata must be validated");

        assert_eq!(error.reason(), ValidationReason::Registry);

        let registry =
            crate::resolved::ResolvedRegistry::default().with_additional_type_variables([
                crate::resolved::ResolvedTypeVariable {
                    id: crate::types::TypeVariableId::new(0),
                    spelling: "A".into(),
                    kind: crate::types::Kind::Type,
                    origin: Origin::Source(
                        foreign
                            .span(ByteRange::new(0, 1).expect("ordered foreign range"))
                            .expect("foreign parameter span"),
                    ),
                },
            ]);
        let mut builder = CoreBuilder::with_registry(Arc::new(registry));
        let root = builder.unit(Type::Unit, origin(&file)).expect("unit root");

        let error = validate(builder.finish(root).expect("root"), &[&file, &foreign])
            .expect_err("additional type-variable provenance must belong to the registry source");

        assert_eq!(error.reason(), ValidationReason::Registry);

        let registry =
            crate::resolved::ResolvedRegistry::default().with_additional_type_variables([
                crate::resolved::ResolvedTypeVariable {
                    id: crate::types::TypeVariableId::new(1),
                    spelling: "A".into(),
                    kind: crate::types::Kind::Type,
                    origin: Origin::Source(
                        file.span(ByteRange::new(0, 1).expect("ordered parameter range"))
                            .expect("parameter span"),
                    ),
                },
            ]);
        let mut builder = CoreBuilder::with_registry(Arc::new(registry));
        let root = builder.unit(Type::Unit, origin(&file)).expect("unit root");

        let error = validate(builder.finish(root).expect("root"), &[&file])
            .expect_err("type-variable identities must be contiguous from zero");

        assert_eq!(error.reason(), ValidationReason::Registry);
    }

    #[test]
    fn accepts_well_formed_non_nominal_registry_type_variables() {
        let file = source();
        let registry =
            crate::resolved::ResolvedRegistry::default().with_additional_type_variables([
                crate::resolved::ResolvedTypeVariable {
                    id: crate::types::TypeVariableId::new(0),
                    spelling: "A".into(),
                    kind: crate::types::Kind::Type,
                    origin: Origin::Source(
                        file.span(ByteRange::new(0, 1).expect("ordered parameter range"))
                            .expect("parameter span"),
                    ),
                },
            ]);
        let mut builder = CoreBuilder::with_registry(Arc::new(registry));
        let root = builder.unit(Type::Unit, origin(&file)).expect("unit root");

        validate(builder.finish(root).expect("root"), &[&file])
            .expect("global interface parameters need no nominal owner");
    }

    #[test]
    fn resolved_abstraction_kinds_must_match_the_canonical_registry_record() {
        let file = source();
        let node_origin = origin(&file);
        let parameter = crate::types::TypeVariableId::resolved(file.id().into(), 0);
        let registry =
            crate::resolved::ResolvedRegistry::default().with_additional_type_variables([
                crate::resolved::ResolvedTypeVariable {
                    id: parameter,
                    spelling: "F".into(),
                    kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                    origin: node_origin.clone(),
                },
            ]);
        let mut builder = CoreBuilder::with_registry(Arc::new(registry));
        let body = builder
            .unit(Type::Unit, node_origin.clone())
            .expect("outer abstraction body");
        let root = builder
            .type_abstraction(
                vec![(parameter, Kind::Type)],
                body,
                Type::Forall(
                    vec![(parameter, Kind::Type)].into_boxed_slice(),
                    Box::new(Type::Unit),
                ),
                node_origin,
            )
            .expect("unchecked resolved abstraction");

        let error = validate(builder.finish(root).expect("root"), &[&file])
            .expect_err("resolved Core binders must match their canonical registry kinds");

        assert_eq!(error.reason(), ValidationReason::Registry);
        assert_eq!(error.node(), Some(root));
    }

    #[test]
    fn borrowed_value_type_matching_handles_wide_function_and_constructor_shapes() {
        const WIDTH: usize = 4_096;
        // Function: tuple-domain pairs plus Bool codomain = W + 2.
        // Constructor: binder record + Kind pair, tuple payload pairs,
        // application link, and nominal head = W + 5.
        const EXACT_SUCCESS_WORK: usize = 2 * WIDTH + 7;
        let file = source();
        let node_origin = origin(&file);
        let arena = super::super::dialect::ArenaId::new(106);
        let nominal = crate::types::NominalTypeId::new(file.id(), 0);
        let parameter = crate::types::TypeVariableId::new(0);
        let constructor_id = ConstructorId::new(nominal, 0);
        let payload = Type::Tuple(vec![Type::Int; WIDTH].into_boxed_slice());
        let constructor = crate::resolved::ResolvedConstructor {
            id: constructor_id,
            owner: nominal,
            spelling: "Make".into(),
            payload: Some(payload.clone()),
            origin: node_origin.clone(),
        };
        let parameters = vec![crate::resolved::ResolvedTypeVariable {
            id: parameter,
            spelling: "A".into(),
            kind: crate::types::Kind::Type,
            origin: node_origin.clone(),
        }];
        let constructor_type = Type::Forall(
            vec![type_parameter(parameter)].into_boxed_slice(),
            Box::new(Type::Function(
                Box::new(payload.clone()),
                Box::new(Type::apply_arguments(
                    Type::Nominal(nominal),
                    [Type::Variable(parameter)],
                )),
            )),
        );
        let function_type = Type::Function(Box::new(payload.clone()), Box::new(Type::Bool));
        let malformed_function_type = Type::Function(
            Box::new(Type::Tuple(
                std::iter::repeat_n(Type::Int, WIDTH - 1)
                    .chain(std::iter::once(Type::Bool))
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            )),
            Box::new(Type::Bool),
        );
        let malformed_constructor_type = Type::Forall(
            vec![type_parameter(parameter)].into_boxed_slice(),
            Box::new(Type::Function(
                Box::new(payload.clone()),
                Box::new(Type::apply_arguments(Type::Nominal(nominal), [Type::Int])),
            )),
        );
        let binder = TypedBinder::new(
            arena,
            BinderId::new(0),
            payload.clone(),
            node_origin.clone(),
        );
        let body = NodeId::new(arena, 0);
        let function = NodeId::new(arena, 1);
        let constructor_node = NodeId::new(arena, 2);
        let malformed_function = NodeId::new(arena, 3);
        let malformed_constructor = NodeId::new(arena, 4);
        let registry = crate::resolved::ResolvedRegistry::new(
            vec![crate::resolved::ResolvedNominalType {
                representation_provenance: None,
                declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                representation: None,
                id: nominal,
                spelling: "Wide".into(),
                constructors: vec![constructor_id].into_boxed_slice(),
                origin: node_origin.clone(),
            }],
            vec![constructor],
        )
        .with_type_parameters(vec![(nominal, parameters)]);
        let program = UnvalidatedProgram {
            registry: Arc::new(registry),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: Type::Bool,
                    origin: Some(node_origin.clone()),
                    kind: PureExprKind::Value(PureValue::Boolean(
                        super::super::literal::BooleanNode::new(false),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: function_type,
                    origin: Some(node_origin.clone()),
                    kind: PureExprKind::Value(PureValue::Function(
                        super::super::function::FunctionNode::new(binder, body),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: constructor_type,
                    origin: Some(node_origin.clone()),
                    kind: PureExprKind::Value(PureValue::Constructor(
                        super::super::data::ConstructorNode::new(constructor_id),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: malformed_function_type,
                    origin: Some(node_origin.clone()),
                    kind: PureExprKind::Value(PureValue::Function(
                        super::super::function::FunctionNode::new(
                            TypedBinder::new(arena, BinderId::new(1), payload, node_origin.clone()),
                            body,
                        ),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    effects: (),
                    ty: malformed_constructor_type,
                    origin: Some(node_origin),
                    kind: PureExprKind::Value(PureValue::Constructor(
                        super::super::data::ConstructorNode::new(constructor_id),
                    )),
                },
            ],
            root: constructor_node,
        };
        let validator = Validator::new(&program, &[&file]);
        validator
            .charge_type_work(CORE_VALIDATION_TYPE_WORK_LIMIT - EXACT_SUCCESS_WORK)
            .expect("test setup leaves the exact borrowed-comparison allowance");

        for id in [function, constructor_node] {
            let node = validator.node(id).expect("test value node");
            let PureExprKind::Value(value) = &node.kind else {
                unreachable!("test node is a value")
            };
            validator
                .validate_value(id, node, value)
                .expect("borrowed value-type validation visits without retaining a derived tree");
        }
        assert_eq!(validator.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);

        let malformed_validator = Validator::new(&program, &[&file]);
        for id in [malformed_function, malformed_constructor] {
            let node = malformed_validator
                .node(id)
                .expect("malformed test value node");
            let PureExprKind::Value(value) = &node.kind else {
                unreachable!("test node is a value")
            };
            let error = malformed_validator
                .validate_value(id, node, value)
                .expect_err("malformed value types remain node-type failures at the budget edge");
            assert_eq!(error.reason(), ValidationReason::NodeType);
            assert_eq!(error.node(), Some(id));
        }
        assert_eq!(validator.type_work.get(), CORE_VALIDATION_TYPE_WORK_LIMIT);
    }

    #[test]
    fn constructor_value_type_matching_covers_every_payload_and_parameter_shape() {
        let file = source();
        let node_origin = origin(&file);
        let arena = super::super::dialect::ArenaId::new(107);
        let monomorphic = crate::types::NominalTypeId::new(file.id(), 0);
        let parameterized = crate::types::NominalTypeId::new(file.id(), 1);
        let mono_nullary = ConstructorId::new(monomorphic, 0);
        let mono_payload = ConstructorId::new(monomorphic, 1);
        let poly_nullary = ConstructorId::new(parameterized, 0);
        let poly_payload = ConstructorId::new(parameterized, 1);
        let parameter = crate::types::TypeVariableId::new(0);
        let parameterized_result =
            || Type::apply_arguments(Type::Nominal(parameterized), [Type::Variable(parameter)]);
        let parameterized_scheme = |body| {
            Type::Forall(
                vec![type_parameter(parameter)].into_boxed_slice(),
                Box::new(body),
            )
        };
        let constructors = [
            crate::resolved::ResolvedConstructor {
                id: mono_nullary,
                owner: monomorphic,
                spelling: "MonoNullary".into(),
                payload: None,
                origin: node_origin.clone(),
            },
            crate::resolved::ResolvedConstructor {
                id: mono_payload,
                owner: monomorphic,
                spelling: "MonoPayload".into(),
                payload: Some(Type::Int),
                origin: node_origin.clone(),
            },
            crate::resolved::ResolvedConstructor {
                id: poly_nullary,
                owner: parameterized,
                spelling: "PolyNullary".into(),
                payload: None,
                origin: node_origin.clone(),
            },
            crate::resolved::ResolvedConstructor {
                id: poly_payload,
                owner: parameterized,
                spelling: "PolyPayload".into(),
                payload: Some(Type::Int),
                origin: node_origin.clone(),
            },
        ];
        let registry = crate::resolved::ResolvedRegistry::new(
            vec![
                crate::resolved::ResolvedNominalType {
                    representation_provenance: None,
                    declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                    representation: None,
                    id: monomorphic,
                    spelling: "Mono".into(),
                    constructors: vec![mono_nullary, mono_payload].into_boxed_slice(),
                    origin: node_origin.clone(),
                },
                crate::resolved::ResolvedNominalType {
                    representation_provenance: None,
                    declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                    representation: None,
                    id: parameterized,
                    spelling: "Poly".into(),
                    constructors: vec![poly_nullary, poly_payload].into_boxed_slice(),
                    origin: node_origin.clone(),
                },
            ],
            constructors.into(),
        )
        .with_type_parameters(vec![(
            parameterized,
            vec![crate::resolved::ResolvedTypeVariable {
                id: parameter,
                spelling: "A".into(),
                kind: crate::types::Kind::Type,
                origin: node_origin.clone(),
            }],
        )]);
        let valid = [
            (mono_nullary, Type::Nominal(monomorphic)),
            (
                mono_payload,
                Type::Function(Box::new(Type::Int), Box::new(Type::Nominal(monomorphic))),
            ),
            (poly_nullary, parameterized_scheme(parameterized_result())),
            (
                poly_payload,
                parameterized_scheme(Type::Function(
                    Box::new(Type::Int),
                    Box::new(parameterized_result()),
                )),
            ),
        ];
        let malformed = [
            (
                mono_nullary,
                Type::Function(Box::new(Type::Int), Box::new(Type::Nominal(monomorphic))),
            ),
            (mono_payload, Type::Nominal(monomorphic)),
            (poly_nullary, parameterized_result()),
            (
                poly_payload,
                parameterized_scheme(Type::Function(
                    Box::new(Type::Int),
                    Box::new(Type::apply_arguments(
                        Type::Nominal(parameterized),
                        [Type::Int],
                    )),
                )),
            ),
        ];
        let nodes = valid
            .iter()
            .chain(&malformed)
            .map(|(constructor, ty)| StoredNode {
                dialect: DialectId::PURE,
                effects: (),
                ty: ty.clone(),
                origin: Some(node_origin.clone()),
                kind: PureExprKind::Value(PureValue::Constructor(
                    super::super::data::ConstructorNode::new(*constructor),
                )),
            })
            .collect::<Vec<_>>();
        let program = UnvalidatedProgram {
            registry: Arc::new(registry),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes,
            root: NodeId::new(arena, 0),
        };
        let validator = Validator::new(&program, &[&file]);

        for index in 0..valid.len() {
            let id = NodeId::new(arena, u32::try_from(index).expect("valid node identity"));
            let node = validator.node(id).expect("valid constructor node");
            let PureExprKind::Value(value) = &node.kind else {
                unreachable!("test node is a value")
            };
            validator
                .validate_value(id, node, value)
                .expect("valid constructor scheme shape");
        }
        for index in valid.len()..valid.len() + malformed.len() {
            let id = NodeId::new(
                arena,
                u32::try_from(index).expect("malformed node identity"),
            );
            let node = validator.node(id).expect("malformed constructor node");
            let PureExprKind::Value(value) = &node.kind else {
                unreachable!("test node is a value")
            };
            let error = validator
                .validate_value(id, node, value)
                .expect_err("malformed constructor scheme shape");
            assert_eq!(error.reason(), ValidationReason::NodeType);
            assert_eq!(error.node(), Some(id));
        }
    }

    #[test]
    fn borrowed_value_type_matching_does_not_clone_deep_types_on_a_small_stack() {
        std::thread::Builder::new()
            .name("borrowed-core-value-type-matching".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 5_000;
                let file = source();
                let node_origin = origin(&file);
                let arena = super::super::dialect::ArenaId::new(108);
                let nominal = crate::types::NominalTypeId::new(file.id(), 0);
                let constructor = ConstructorId::new(nominal, 0);
                let body = NodeId::new(arena, 0);
                let function = NodeId::new(arena, 1);
                let constructor_node = NodeId::new(arena, 2);
                let registry = crate::resolved::ResolvedRegistry::new(
                    vec![crate::resolved::ResolvedNominalType {
                        representation_provenance: None,
                        declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                        representation: None,
                        id: nominal,
                        spelling: "Deep".into(),
                        constructors: vec![constructor].into_boxed_slice(),
                        origin: node_origin.clone(),
                    }],
                    vec![crate::resolved::ResolvedConstructor {
                        id: constructor,
                        owner: nominal,
                        spelling: "Make".into(),
                        payload: Some(function_type(DEPTH)),
                        origin: node_origin.clone(),
                    }],
                );
                let program = UnvalidatedProgram {
                    registry: Arc::new(registry),
                    method_evidence: Arc::new(
                        super::super::dialect::MethodEvidenceCatalog::default(),
                    ),
                    method_evidence_anchors: Box::new([]),
                    arena,
                    nodes: vec![
                        StoredNode {
                            dialect: DialectId::PURE,
                            effects: (),
                            ty: function_type(DEPTH),
                            origin: Some(node_origin.clone()),
                            kind: PureExprKind::Value(PureValue::Unit(
                                super::super::literal::UnitNode,
                            )),
                        },
                        StoredNode {
                            dialect: DialectId::PURE,
                            effects: (),
                            ty: Type::Function(
                                Box::new(function_type(DEPTH)),
                                Box::new(function_type(DEPTH)),
                            ),
                            origin: Some(node_origin.clone()),
                            kind: PureExprKind::Value(PureValue::Function(
                                super::super::function::FunctionNode::new(
                                    TypedBinder::new(
                                        arena,
                                        BinderId::new(0),
                                        function_type(DEPTH),
                                        node_origin.clone(),
                                    ),
                                    body,
                                ),
                            )),
                        },
                        StoredNode {
                            dialect: DialectId::PURE,
                            effects: (),
                            ty: Type::Function(
                                Box::new(function_type(DEPTH)),
                                Box::new(Type::Nominal(nominal)),
                            ),
                            origin: Some(node_origin),
                            kind: PureExprKind::Value(PureValue::Constructor(
                                super::super::data::ConstructorNode::new(constructor),
                            )),
                        },
                    ],
                    root: constructor_node,
                };
                let validator = Validator::new(&program, &[&file]);
                for id in [function, constructor_node] {
                    let node = validator.node(id).expect("deep value node");
                    let PureExprKind::Value(value) = &node.kind else {
                        unreachable!("test node is a value")
                    };
                    validator
                        .validate_value(id, node, value)
                        .expect("deep value matching uses borrowed explicit work stacks");
                }
                drop(validator);
                program.discard_iteratively();
            })
            .expect("small-stack validation thread should start")
            .join()
            .expect("borrowed value matching must fit the small stack");
    }

    #[test]
    fn successful_type_application_validation_discards_instantiation_work_iteratively() {
        std::thread::Builder::new()
            .name("type-application-validation-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                // Synthesis, retained argument admission, substitution, and
                // final comparison visit 11D + 6 units. D=32,000 remains a
                // deep small-stack success inside the module-wide ledger.
                const DEPTH: usize = 32_000;
                let file = source();
                let node_origin = origin(&file);
                let arena = super::super::dialect::ArenaId::new(191);
                let owner = crate::types::NominalTypeId::new(file.id(), 0);
                let parameter = crate::types::TypeVariableId::new(
                    u32::try_from(DEPTH).expect("scheme parameter identity"),
                );
                let function = NodeId::new(arena, 0);
                let application = NodeId::new(arena, 1);
                let argument = nominal_application_type(owner, DEPTH);
                let (nominal, parameters) = wide_nominal(owner, "Wide", DEPTH, &node_origin);
                let program = UnvalidatedProgram {
                    registry: Arc::new(
                        crate::resolved::ResolvedRegistry::new(vec![nominal], vec![])
                            .with_type_parameters(vec![(owner, parameters)]),
                    ),
                    method_evidence: Arc::new(
                        super::super::dialect::MethodEvidenceCatalog::default(),
                    ),
                    method_evidence_anchors: Box::new([]),
                    arena,
                    nodes: vec![
                        StoredNode {
                            dialect: DialectId::PURE,
                            effects: (),
                            ty: Type::Forall(
                                vec![type_parameter(parameter)].into_boxed_slice(),
                                Box::new(Type::Variable(parameter)),
                            ),
                            origin: Some(node_origin.clone()),
                            kind: PureExprKind::Value(PureValue::Unit(
                                super::super::literal::UnitNode,
                            )),
                        },
                        StoredNode {
                            dialect: DialectId::PURE,
                            effects: (),
                            ty: argument.clone(),
                            origin: Some(node_origin),
                            kind: PureExprKind::Computation(PureComputation::TypeApplication(
                                super::super::type_ops::TypeApplicationNode::new(
                                    function,
                                    vec![argument],
                                ),
                            )),
                        },
                    ],
                    root: application,
                };
                let validator = Validator::new(&program, &[&file]);
                let PureExprKind::Computation(computation) = &program.nodes[1].kind else {
                    unreachable!("test application computation")
                };
                validator
                    .validate_computation(
                        application,
                        &program.nodes[1],
                        computation,
                        &HashMap::new(),
                        &HashMap::new(),
                        false,
                    )
                    .expect("the deep type application is valid");
                drop(validator);
                program.discard_iteratively();
            })
            .expect("small-stack validation thread should start")
            .join()
            .expect("successful instantiation teardown must fit the small stack");
    }

    #[test]
    fn successful_match_validation_discards_coverage_matrix_iteratively() {
        std::thread::Builder::new()
            .name("match-validation-matrix-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_000;
                let file = source();
                let node_origin = origin(&file);
                let arena = super::super::dialect::ArenaId::new(192);
                let owner = crate::types::NominalTypeId::new(file.id(), 0);
                let scrutinee = NodeId::new(arena, 0);
                let body = NodeId::new(arena, 1);
                let match_id = NodeId::new(arena, 2);
                let deep = nominal_application_type(owner, DEPTH);
                let (nominal, parameters) = wide_nominal(owner, "Wide", DEPTH, &node_origin);
                let pattern =
                    CorePattern::new(deep.clone(), node_origin.clone(), CorePatternKind::Wildcard);
                let program = UnvalidatedProgram {
                    registry: Arc::new(
                        crate::resolved::ResolvedRegistry::new(vec![nominal], vec![])
                            .with_type_parameters(vec![(owner, parameters)]),
                    ),
                    method_evidence: Arc::new(
                        super::super::dialect::MethodEvidenceCatalog::default(),
                    ),
                    method_evidence_anchors: Box::new([]),
                    arena,
                    nodes: vec![
                        StoredNode {
                            dialect: DialectId::PURE,
                            effects: (),
                            ty: deep,
                            origin: Some(node_origin.clone()),
                            kind: PureExprKind::Value(PureValue::Unit(
                                super::super::literal::UnitNode,
                            )),
                        },
                        StoredNode {
                            dialect: DialectId::PURE,
                            effects: (),
                            ty: Type::Unit,
                            origin: Some(node_origin.clone()),
                            kind: PureExprKind::Value(PureValue::Unit(
                                super::super::literal::UnitNode,
                            )),
                        },
                        StoredNode {
                            dialect: DialectId::PURE,
                            effects: (),
                            ty: Type::Unit,
                            origin: Some(node_origin.clone()),
                            kind: PureExprKind::Computation(PureComputation::Match(
                                super::super::MatchNode::new(
                                    scrutinee,
                                    vec![super::super::CoreMatchArm::new(
                                        pattern,
                                        body,
                                        node_origin,
                                    )],
                                ),
                            )),
                        },
                    ],
                    root: match_id,
                };
                let validator = Validator::new(&program, &[&file]);
                let PureExprKind::Computation(computation) = &program.nodes[2].kind else {
                    unreachable!("test match computation")
                };
                validator
                    .validate_computation(
                        match_id,
                        &program.nodes[2],
                        computation,
                        &HashMap::new(),
                        &HashMap::new(),
                        false,
                    )
                    .expect("the exhaustive deep match is valid");
                drop(validator);
                program.discard_iteratively();
            })
            .expect("small-stack validation thread should start")
            .join()
            .expect("successful coverage-matrix teardown must fit the small stack");
    }

    #[test]
    fn redundant_match_validation_discards_pending_pattern_row_iteratively() {
        std::thread::Builder::new()
            .name("match-validation-row-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_000;
                let file = source();
                let node_origin = origin(&file);
                let arena = super::super::dialect::ArenaId::new(194);
                let owner = crate::types::NominalTypeId::new(file.id(), 0);
                let scrutinee = NodeId::new(arena, 0);
                let body = NodeId::new(arena, 1);
                let match_id = NodeId::new(arena, 2);
                let deep = nominal_application_type(owner, DEPTH);
                let (nominal, parameters) = wide_nominal(owner, "Wide", DEPTH, &node_origin);
                let arms = vec![
                    super::super::CoreMatchArm::new(
                        CorePattern::new(
                            deep.clone(),
                            node_origin.clone(),
                            CorePatternKind::Wildcard,
                        ),
                        body,
                        node_origin.clone(),
                    ),
                    super::super::CoreMatchArm::new(
                        CorePattern::new(
                            deep.clone(),
                            node_origin.clone(),
                            CorePatternKind::Wildcard,
                        ),
                        body,
                        node_origin.clone(),
                    ),
                ];
                let program = UnvalidatedProgram {
                    registry: Arc::new(
                        crate::resolved::ResolvedRegistry::new(vec![nominal], vec![])
                            .with_type_parameters(vec![(owner, parameters)]),
                    ),
                    method_evidence: Arc::new(
                        super::super::dialect::MethodEvidenceCatalog::default(),
                    ),
                    method_evidence_anchors: Box::new([]),
                    arena,
                    nodes: vec![
                        StoredNode {
                            dialect: DialectId::PURE,
                            effects: (),
                            ty: deep,
                            origin: Some(node_origin.clone()),
                            kind: PureExprKind::Value(PureValue::Unit(
                                super::super::literal::UnitNode,
                            )),
                        },
                        StoredNode {
                            dialect: DialectId::PURE,
                            effects: (),
                            ty: Type::Unit,
                            origin: Some(node_origin.clone()),
                            kind: PureExprKind::Value(PureValue::Unit(
                                super::super::literal::UnitNode,
                            )),
                        },
                        StoredNode {
                            dialect: DialectId::PURE,
                            effects: (),
                            ty: Type::Unit,
                            origin: Some(node_origin.clone()),
                            kind: PureExprKind::Computation(PureComputation::Match(
                                super::super::MatchNode::new(scrutinee, arms),
                            )),
                        },
                    ],
                    root: match_id,
                };
                let validator = Validator::new(&program, &[&file]);
                let PureExprKind::Computation(computation) = &program.nodes[2].kind else {
                    unreachable!("test match computation")
                };
                let error = validator
                    .validate_computation(
                        match_id,
                        &program.nodes[2],
                        computation,
                        &HashMap::new(),
                        &HashMap::new(),
                        false,
                    )
                    .expect_err("the second wildcard is redundant");
                assert_eq!(error.reason(), ValidationReason::Coverage);
                drop(validator);
                program.discard_iteratively();
            })
            .expect("small-stack validation thread should start")
            .join()
            .expect("redundant pattern-row teardown must fit the small stack");
    }

    #[test]
    fn late_pattern_validation_error_discards_owned_payload_type_iteratively() {
        std::thread::Builder::new()
            .name("pattern-validation-owned-payload".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_000;
                let file = source();
                let node_origin = origin(&file);
                let arena = super::super::dialect::ArenaId::new(193);
                let owner = crate::types::NominalTypeId::new(file.id(), 0);
                let deep_owner = crate::types::NominalTypeId::new(file.id(), 1);
                let constructor = ConstructorId::new(owner, 0);
                let parameter = crate::types::TypeVariableId::new(0);
                let (deep_nominal, deep_parameters) =
                    wide_nominal(deep_owner, "Wide", DEPTH, &node_origin);
                let registry = crate::resolved::ResolvedRegistry::new(
                    vec![
                        crate::resolved::ResolvedNominalType {
                            representation_provenance: None,
                            declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                            representation: None,
                            id: owner,
                            spelling: "Deep".into(),
                            constructors: vec![constructor].into_boxed_slice(),
                            origin: node_origin.clone(),
                        },
                        deep_nominal,
                    ],
                    vec![crate::resolved::ResolvedConstructor {
                        id: constructor,
                        owner,
                        spelling: "Make".into(),
                        payload: Some(Type::Variable(parameter)),
                        origin: node_origin.clone(),
                    }],
                )
                .with_type_parameters(vec![
                    (
                        owner,
                        vec![crate::resolved::ResolvedTypeVariable {
                            id: parameter,
                            spelling: "T".into(),
                            kind: crate::types::Kind::Type,
                            origin: node_origin.clone(),
                        }],
                    ),
                    (deep_owner, deep_parameters),
                ]);
                let expected = Type::Application(
                    Box::new(Type::Nominal(owner)),
                    Box::new(nominal_application_type(deep_owner, DEPTH)),
                );
                let pattern = CorePattern::new(
                    expected.clone(),
                    node_origin.clone(),
                    CorePatternKind::Constructor {
                        constructor,
                        payload: Some(Box::new(CorePattern::new(
                            Type::Bool,
                            node_origin.clone(),
                            CorePatternKind::Wildcard,
                        ))),
                    },
                );
                let program = UnvalidatedProgram {
                    registry: Arc::new(registry),
                    method_evidence: Arc::new(
                        super::super::dialect::MethodEvidenceCatalog::default(),
                    ),
                    method_evidence_anchors: Box::new([]),
                    arena,
                    nodes: vec![StoredNode {
                        dialect: DialectId::PURE,
                        effects: (),
                        ty: Type::Unit,
                        origin: Some(node_origin),
                        kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
                    }],
                    root: NodeId::new(arena, 0),
                };
                let validator = Validator::new(&program, &[&file]);
                let error = validator
                    .validate_pattern(&pattern, &expected, program.root)
                    .expect_err("the payload pattern has the wrong type");
                assert_eq!(error.reason(), ValidationReason::Pattern);
                drop(validator);
                pattern.discard_iteratively();
                discard_type_iteratively(expected);
                program.discard_iteratively();
            })
            .expect("small-stack validation thread should start")
            .join()
            .expect("late owned-pattern teardown must fit the small stack");
    }

    #[test]
    fn payload_shape_error_discards_substituted_type_iteratively() {
        std::thread::Builder::new()
            .name("pattern-validation-payload-shape-owner".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 32_000;
                let file = source();
                let node_origin = origin(&file);
                let arena = super::super::dialect::ArenaId::new(195);
                let owner = crate::types::NominalTypeId::new(file.id(), 0);
                let deep_owner = crate::types::NominalTypeId::new(file.id(), 1);
                let constructor = ConstructorId::new(owner, 0);
                let parameter = crate::types::TypeVariableId::new(0);
                let (deep_nominal, deep_parameters) =
                    wide_nominal(deep_owner, "Wide", DEPTH, &node_origin);
                let registry = crate::resolved::ResolvedRegistry::new(
                    vec![
                        crate::resolved::ResolvedNominalType {
                            representation_provenance: None,
                            declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                            representation: None,
                            id: owner,
                            spelling: "Deep".into(),
                            constructors: vec![constructor].into_boxed_slice(),
                            origin: node_origin.clone(),
                        },
                        deep_nominal,
                    ],
                    vec![crate::resolved::ResolvedConstructor {
                        id: constructor,
                        owner,
                        spelling: "Make".into(),
                        payload: Some(Type::Variable(parameter)),
                        origin: node_origin.clone(),
                    }],
                )
                .with_type_parameters(vec![
                    (
                        owner,
                        vec![crate::resolved::ResolvedTypeVariable {
                            id: parameter,
                            spelling: "T".into(),
                            kind: crate::types::Kind::Type,
                            origin: node_origin.clone(),
                        }],
                    ),
                    (deep_owner, deep_parameters),
                ]);
                let expected = Type::Application(
                    Box::new(Type::Nominal(owner)),
                    Box::new(nominal_application_type(deep_owner, DEPTH)),
                );
                let pattern = CorePattern::new(
                    expected.clone(),
                    node_origin.clone(),
                    CorePatternKind::Constructor {
                        constructor,
                        payload: None,
                    },
                );
                let program = UnvalidatedProgram {
                    registry: Arc::new(registry),
                    method_evidence: Arc::new(
                        super::super::dialect::MethodEvidenceCatalog::default(),
                    ),
                    method_evidence_anchors: Box::new([]),
                    arena,
                    nodes: vec![StoredNode {
                        dialect: DialectId::PURE,
                        effects: (),
                        ty: Type::Unit,
                        origin: Some(node_origin),
                        kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
                    }],
                    root: NodeId::new(arena, 0),
                };
                let validator = Validator::new(&program, &[&file]);
                let error = validator
                    .validate_pattern(&pattern, &expected, program.root)
                    .expect_err("the required payload pattern is missing");
                assert_eq!(error.reason(), ValidationReason::Pattern);
                drop(validator);
                pattern.discard_iteratively();
                discard_type_iteratively(expected);
                program.discard_iteratively();
            })
            .expect("small-stack validation thread should start")
            .join()
            .expect("payload-shape teardown must fit the small stack");
    }

    #[test]
    fn rejects_a_foreign_dialect_envelope_without_a_foreign_pure_variant() {
        let file = source();
        let mut builder = CoreBuilder::new();
        let root = builder
            .unit(Type::Unit, origin(&file))
            .expect("small arena");
        let mut program = builder.finish(root).expect("valid root");
        program.nodes[0].dialect = DialectId::FOREIGN;

        let error = validate(program, &[&file]).expect_err("foreign dialect");
        assert_eq!(error.reason(), ValidationReason::DialectMembership);
    }

    #[test]
    fn independent_validation_rejects_a_conversion_without_a_canonical_relation() {
        let file = source();
        let owner = crate::types::NominalTypeId::new(file.id(), 0);
        let mut builder = CoreBuilder::new();
        let child = builder
            .unit(Type::Unit, origin(&file))
            .expect("the conversion child should fit");
        let root = builder
            .newtype_conversion(
                owner,
                NewtypeConversionDirection::Wrap,
                child,
                Type::Unit,
                origin(&file),
            )
            .expect("the unchecked conversion carrier should fit");

        let error = validate(
            builder.finish(root).expect("the conversion should finish"),
            &[&file],
        )
        .expect_err("a conversion without a registry relation must not validate");
        assert_eq!(error.reason(), ValidationReason::NewtypeConversion);
        assert_eq!(error.node(), Some(root));
    }

    #[test]
    fn both_registry_validators_reject_newtype_provenance_tampering() {
        for tamper in [
            NewtypeRegistryTamper::OrdinaryKind,
            NewtypeRegistryTamper::NominalGeneratedOrigin,
            NewtypeRegistryTamper::ConstructorGeneratedOrigin,
            NewtypeRegistryTamper::WrongShape,
            NewtypeRegistryTamper::WrongSource,
            NewtypeRegistryTamper::EmptyRange,
            NewtypeRegistryTamper::OutsideConstructor,
            NewtypeRegistryTamper::SharedNode,
            NewtypeRegistryTamper::OrphanNode,
        ] {
            let source = SourceFile::new(
                "newtype-registry-tamper.ash",
                "newtype Wrapped = Wrapped(Int)",
            )
            .expect("test source");
            let foreign = SourceFile::new("foreign.ash", "Int").expect("foreign source");

            let registry = tampered_newtype_registry(&source, &foreign, tamper);
            let error = validate(
                unit_program_with_registry(&source, registry),
                &[&source, &foreign],
            )
            .expect_err("single-source Core must reject the tampered canonical fact");
            assert_eq!(error.reason(), ValidationReason::Registry, "{tamper:?}");
            assert_eq!(error.node(), None, "{tamper:?}");

            let registry = tampered_newtype_registry(&source, &foreign, tamper);
            let owner_module = registry
                .nominals()
                .first()
                .expect("the tampered registry should retain its owner")
                .id
                .module();
            let error = validate_modules(
                unit_program_with_registry(&source, registry),
                &[&source, &foreign],
                &[(owner_module, source.id())],
            )
            .expect_err("module Core must reject the tampered canonical fact");
            assert_eq!(error.reason(), ValidationReason::Registry, "{tamper:?}");
            assert_eq!(error.node(), None, "{tamper:?}");
        }
    }

    #[test]
    fn linked_newtype_conversion_rejects_each_independent_relation_tamper() {
        #[derive(Clone, Copy, Debug)]
        enum Case {
            Direction,
            OrdinaryOwner,
            MissingArgument,
            OverApplication,
            WrongArgumentKind,
            ParameterOrder,
            FreshBinderSubstitution,
            ChildType,
            ResultType,
            ForeignOrigin,
        }

        for case in [
            Case::Direction,
            Case::OrdinaryOwner,
            Case::MissingArgument,
            Case::OverApplication,
            Case::WrongArgumentKind,
            Case::ParameterOrder,
            Case::FreshBinderSubstitution,
            Case::ChildType,
            Case::ResultType,
            Case::ForeignOrigin,
        ] {
            let mut fixture = LinkedCoreValidationFixture::compile(
                "",
                concat!(
                    "type Carrier = Carrier(Int)\n",
                    "type Higher<A> = Higher(A)\n",
                    "newtype Box<A, B> = Box((A, B))\n",
                    "main : Unit -> Box<Int, Bool>\n",
                    "main () = Box((42, true))\n",
                ),
                &[],
            );
            let conversion_index = fixture
                .program
                .nodes
                .iter()
                .position(|node| {
                    matches!(
                        node.kind,
                        PureExprKind::Computation(PureComputation::NewtypeConversion(_))
                    )
                })
                .expect("the parameterized constructor should lower one conversion");
            let PureExprKind::Computation(PureComputation::NewtypeConversion(conversion)) =
                fixture.program.nodes[conversion_index].kind
            else {
                unreachable!("the selected node is a conversion")
            };
            let owner = conversion.owner();
            let child = conversion.child();
            let ordinary = fixture
                .program
                .registry
                .nominals()
                .iter()
                .find(|nominal| nominal.spelling == "Carrier")
                .expect("the ordinary owner should remain registered")
                .id;
            let higher = fixture
                .program
                .registry
                .nominals()
                .iter()
                .find(|nominal| nominal.spelling == "Higher")
                .expect("the higher-kinded owner should remain registered")
                .id;
            match case {
                Case::Direction => {
                    fixture.program.nodes[conversion_index].kind =
                        PureExprKind::Computation(PureComputation::NewtypeConversion(
                            super::super::NewtypeConversionNode::new(
                                owner,
                                NewtypeConversionDirection::Unwrap,
                                child,
                            ),
                        ));
                }
                Case::OrdinaryOwner => {
                    fixture.program.nodes[conversion_index].kind =
                        PureExprKind::Computation(PureComputation::NewtypeConversion(
                            super::super::NewtypeConversionNode::new(
                                ordinary,
                                NewtypeConversionDirection::Wrap,
                                child,
                            ),
                        ));
                }
                Case::MissingArgument => {
                    fixture.program.nodes[conversion_index].ty = Type::Nominal(owner);
                }
                Case::OverApplication => {
                    let original = std::mem::replace(
                        &mut fixture.program.nodes[conversion_index].ty,
                        Type::Unit,
                    );
                    fixture.program.nodes[conversion_index].ty =
                        Type::Application(Box::new(original), Box::new(Type::Unit));
                }
                Case::WrongArgumentKind => {
                    fixture.program.nodes[conversion_index].ty = Type::Application(
                        Box::new(Type::Application(
                            Box::new(Type::Nominal(owner)),
                            Box::new(Type::Nominal(higher)),
                        )),
                        Box::new(Type::Bool),
                    );
                }
                Case::ParameterOrder => {
                    let Type::Application(function, second) =
                        fixture.program.nodes[conversion_index].ty.clone()
                    else {
                        panic!("Box should retain its second applied argument");
                    };
                    let Type::Application(_, first) = *function else {
                        panic!("Box should retain its first applied argument");
                    };
                    fixture.program.nodes[conversion_index].ty = Type::Application(
                        Box::new(Type::Application(Box::new(Type::Nominal(owner)), second)),
                        first,
                    );
                }
                Case::FreshBinderSubstitution => {
                    fixture.program.nodes[conversion_index].ty = Type::Application(
                        Box::new(Type::Application(
                            Box::new(Type::Nominal(owner)),
                            Box::new(Type::Int),
                        )),
                        Box::new(Type::Bool),
                    );
                }
                Case::ChildType => {
                    fixture.program.nodes[child.index().expect("child index")].ty = Type::Bool;
                }
                Case::ResultType => {
                    fixture.program.nodes[conversion_index].ty = Type::Bool;
                }
                Case::ForeignOrigin => {
                    let foreign = SourceFile::new("foreign-conversion.ash", "Box")
                        .expect("foreign conversion source");
                    fixture.program.nodes[conversion_index].origin = Some(Origin::Source(
                        foreign
                            .span(ByteRange::new(0, 3).expect("foreign range"))
                            .expect("foreign span"),
                    ));
                }
            }

            let conversion_id = NodeId::new(
                fixture.program.arena,
                u32::try_from(conversion_index).expect("conversion index fits"),
            );
            let error = fixture
                .validate()
                .expect_err("each relation mutation must reject before evaluation");
            let (reason, node) = match case {
                Case::MissingArgument | Case::OverApplication | Case::WrongArgumentKind => {
                    (ValidationReason::NodeType, conversion_id)
                }
                Case::ChildType => (ValidationReason::NodeType, child),
                Case::ForeignOrigin => (ValidationReason::Provenance, conversion_id),
                Case::Direction
                | Case::OrdinaryOwner
                | Case::ParameterOrder
                | Case::FreshBinderSubstitution
                | Case::ResultType => (ValidationReason::NewtypeConversion, conversion_id),
            };
            assert_eq!(error.reason(), reason, "{case:?}");
            assert_eq!(error.node(), Some(node), "{case:?}");
        }
    }

    #[test]
    fn parameterized_newtype_validation_is_exact_atomic_and_retryable() {
        fn fixture() -> LinkedCoreValidationFixture {
            LinkedCoreValidationFixture::compile(
                "",
                concat!(
                    "newtype Box<Left, Right> = Box((Left, Right))\n",
                    "main : Unit -> Box<Int, Bool>\n",
                    "main () = Box((42, true))\n",
                ),
                &[],
            )
        }

        fn attempt(initial_type_work: usize) -> ConsumingModuleValidationAttempt {
            let LinkedCoreValidationFixture {
                directory,
                graph,
                program,
                module_sources,
                globals: _,
            } = fixture();
            let sources = graph
                .modules()
                .iter()
                .map(|module| module.source())
                .collect::<Vec<_>>();
            let attempt = validate_modules_with_initial_type_work_for_test(
                program,
                &sources,
                &module_sources,
                initial_type_work,
            );
            drop(graph);
            drop(directory);
            attempt
        }

        let measured = fixture();
        let sources = linked_fixture_sources(&measured);
        let mut validator =
            Validator::new_modules(&measured.program, &sources, &measured.module_sources)
                .expect("the canonical module/source relation should initialize");
        run_module_validation_phases_for_test(&mut validator)
            .expect("the canonical parameterized conversion should validate");
        let exact_work = validator.type_work.get();
        // P argument slots + (P + 1) spine inspections + P replacement slots
        // + P parameter/argument rows = 4P + 1.
        const NEWTYPE_PARAMETER_WORK: usize = 4 * 2 + 1;
        // All fixed registry and node validation for this concrete fixture is
        // independent of the conversion's parameter-width term.
        const VALIDATION_ENVELOPE_WORK: usize = 518;
        const EXACT_WORK: usize = VALIDATION_ENVELOPE_WORK + NEWTYPE_PARAMETER_WORK;
        assert_eq!(
            validator.newtype_conversion_parameter_work.get(),
            NEWTYPE_PARAMETER_WORK,
            "two arguments require 2P carriers, P row traversal, and P+1 spine inspection",
        );
        assert_eq!(exact_work, EXACT_WORK);
        assert!(exact_work < CORE_VALIDATION_TYPE_WORK_LIMIT);
        drop(validator);
        drop(measured);

        let exact = attempt(CORE_VALIDATION_TYPE_WORK_LIMIT - exact_work);
        assert!(exact.result.is_ok());
        assert_eq!(exact.type_work, CORE_VALIDATION_TYPE_WORK_LIMIT);

        let one_short = attempt(CORE_VALIDATION_TYPE_WORK_LIMIT - (exact_work - 1));
        let error = one_short
            .result
            .expect_err("one missing unit must reject before publication");
        assert_eq!(error.reason(), ValidationReason::Resource);
        assert_eq!(one_short.type_work, CORE_VALIDATION_TYPE_WORK_LIMIT);

        let retry = attempt(CORE_VALIDATION_TYPE_WORK_LIMIT - exact_work);
        assert!(retry.result.is_ok());
        assert_eq!(retry.type_work, CORE_VALIDATION_TYPE_WORK_LIMIT);
    }

    #[test]
    fn independent_validation_rejects_newtypes_in_the_ordinary_constructor_route() {
        let file = source();
        let (registry, owner, constructor) = newtype_registry(&file);
        let mut builder = CoreBuilder::with_registry(registry);
        let root = builder
            .constructor(constructor, Type::Nominal(owner), origin(&file))
            .expect("the forged ordinary constructor should fit unchecked Core");

        let error = validate(
            builder.finish(root).expect("the constructor should finish"),
            &[&file],
        )
        .expect_err("a newtype must never validate as an ordinary constructor");
        assert_eq!(error.reason(), ValidationReason::Registry);
        assert_eq!(error.node(), Some(root));
    }

    #[test]
    fn independent_validation_rejects_newtypes_in_ordinary_constructor_patterns() {
        let file = source();
        let (registry, owner, constructor) = newtype_registry(&file);
        let node_origin = origin(&file);
        let mut builder = CoreBuilder::with_registry(registry);
        let parameter = builder
            .binder(Type::Nominal(owner), node_origin.clone())
            .expect("the nominal parameter should fit");
        let scrutinee = builder
            .variable(parameter.id(), Type::Nominal(owner), node_origin.clone())
            .expect("the scrutinee should fit");
        let body = builder
            .unit(Type::Unit, node_origin.clone())
            .expect("the arm body should fit");
        let pattern = CorePattern::new(
            Type::Nominal(owner),
            node_origin.clone(),
            CorePatternKind::Constructor {
                constructor,
                payload: None,
            },
        );
        let matched = builder
            .match_expression(
                scrutinee,
                vec![super::super::CoreMatchArm::new(
                    pattern,
                    body,
                    node_origin.clone(),
                )],
                Type::Unit,
                node_origin.clone(),
            )
            .expect("the forged constructor pattern should fit unchecked Core");
        let root = builder
            .function(
                parameter,
                matched,
                Type::Function(Box::new(Type::Nominal(owner)), Box::new(Type::Unit)),
                node_origin,
            )
            .expect("the enclosing function should fit");

        let error = validate(
            builder.finish(root).expect("the function should finish"),
            &[&file],
        )
        .expect_err("a newtype must never validate as an ordinary constructor pattern");
        assert_eq!(error.reason(), ValidationReason::Pattern);
        assert_eq!(error.node(), Some(matched));
    }

    #[test]
    fn canonical_newtype_conversion_chains_validate_and_reject_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("newtype-conversion-validation-deep".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let file = source();
                let (registry, owner, _) = newtype_registry(&file);
                let mut builder = CoreBuilder::with_registry(registry);
                let mut root = builder
                    .integer(
                        Integer::parse_decimal("0").expect("zero should parse"),
                        Type::Int,
                        origin(&file),
                    )
                    .expect("the conversion leaf should fit");
                for index in 0..DEPTH {
                    root = builder
                        .newtype_conversion(
                            owner,
                            if index % 2 == 0 {
                                NewtypeConversionDirection::Wrap
                            } else {
                                NewtypeConversionDirection::Unwrap
                            },
                            root,
                            if index % 2 == 0 {
                                Type::Nominal(owner)
                            } else {
                                Type::Int
                            },
                            origin(&file),
                        )
                        .expect("the unchecked conversion chain should fit");
                }
                let accepted = validate(
                    builder.finish(root).expect("the conversion should finish"),
                    &[&file],
                )
                .expect("the canonical conversion chain should validate");
                drop(accepted);

                let (registry, owner, _) = newtype_registry(&file);
                let mut builder = CoreBuilder::with_registry(registry);
                let mut root = builder
                    .integer(
                        Integer::parse_decimal("0").expect("zero should parse"),
                        Type::Int,
                        origin(&file),
                    )
                    .expect("the conversion leaf should fit");
                for index in 0..DEPTH {
                    let direction = if index + 1 == DEPTH || index % 2 == 0 {
                        NewtypeConversionDirection::Wrap
                    } else {
                        NewtypeConversionDirection::Unwrap
                    };
                    root = builder
                        .newtype_conversion(
                            owner,
                            direction,
                            root,
                            if index % 2 == 0 {
                                Type::Nominal(owner)
                            } else {
                                Type::Int
                            },
                            origin(&file),
                        )
                        .expect("the rejected conversion chain should fit");
                }
                let error = validate(
                    builder
                        .finish(root)
                        .expect("the rejected chain should finish"),
                    &[&file],
                )
                .expect_err("the late wrong direction must reject");
                assert_eq!(error.reason(), ValidationReason::NewtypeConversion);
            })
            .expect("the conversion validation thread should start")
            .join()
            .expect("accepted and rejected conversion teardown must fit a small stack");
    }

    #[test]
    fn rejects_missing_provenance_before_projection() {
        let file = source();
        let mut builder = CoreBuilder::new();
        let root = builder
            .unit(Type::Unit, origin(&file))
            .expect("small arena");
        let mut program = builder.finish(root).expect("valid root");
        program.nodes[0].origin = None;

        let error = validate(program, &[&file]).expect_err("missing origin");
        assert_eq!(error.reason(), ValidationReason::Provenance);
    }

    #[test]
    fn rejects_a_root_outside_the_arena() {
        let file = source();
        let arena = super::super::dialect::ArenaId::new(100);
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: Vec::new(),
            root: NodeId::new(arena, 0),
        };

        let error = validate(program, &[&file]).expect_err("invalid root");
        assert_eq!(error.reason(), ValidationReason::Root);
        assert_eq!(error.node(), None);
    }

    #[test]
    fn rejects_a_privately_corrupted_foreign_binder_capability() {
        let file = source();
        let arena = super::super::dialect::ArenaId::new(102);
        let foreign_arena = super::super::dialect::ArenaId::new(103);
        let unit = StoredNode {
            dialect: DialectId::PURE,
            effects: (),
            ty: Type::Unit,
            origin: Some(origin(&file)),
            kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
        };
        let function = StoredNode {
            dialect: DialectId::PURE,
            effects: (),
            ty: Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
            origin: Some(origin(&file)),
            kind: PureExprKind::Value(PureValue::Function(
                super::super::function::FunctionNode::new(
                    TypedBinder::new(foreign_arena, BinderId::new(0), Type::Unit, origin(&file)),
                    NodeId::new(arena, 0),
                ),
            )),
        };
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![unit, function],
            root: NodeId::new(arena, 1),
        };

        let error = validate(program, &[&file]).expect_err("foreign binder capability");
        assert_eq!(error.reason(), ValidationReason::Scope);
        assert_eq!(error.node(), Some(NodeId::new(arena, 1)));
    }

    #[test]
    fn rejects_out_of_bounds_and_cycles_without_recursion() {
        let file = source();
        let arena = super::super::dialect::ArenaId::new(101);
        let stored = StoredNode {
            dialect: DialectId::PURE,
            effects: (),
            ty: Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
            origin: Some(origin(&file)),
            kind: PureExprKind::Value(PureValue::Function(
                super::super::function::FunctionNode::new(
                    TypedBinder::new(arena, BinderId::new(0), Type::Unit, origin(&file)),
                    NodeId::new(arena, 1),
                ),
            )),
        };
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![stored],
            root: NodeId::new(arena, 0),
        };
        let error = validate(program, &[&file]).expect_err("out-of-bounds child");
        assert_eq!(error.reason(), ValidationReason::NodeBounds);

        let cyclic = StoredNode {
            dialect: DialectId::PURE,
            effects: (),
            ty: Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
            origin: Some(origin(&file)),
            kind: PureExprKind::Value(PureValue::Function(
                super::super::function::FunctionNode::new(
                    TypedBinder::new(arena, BinderId::new(0), Type::Unit, origin(&file)),
                    NodeId::new(arena, 0),
                ),
            )),
        };
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![cyclic],
            root: NodeId::new(arena, 0),
        };
        let error = validate(program, &[&file]).expect_err("cycle");
        assert_eq!(error.reason(), ValidationReason::Cycle);
    }

    #[test]
    fn rejects_an_ownership_cycle_through_a_recursive_group_body() {
        let file = source();
        let arena = super::super::dialect::ArenaId::new(104);
        let node_origin = origin(&file);
        let function_type = Type::Function(Box::new(Type::Unit), Box::new(Type::Unit));
        let recursive = TypedBinder::new(
            arena,
            BinderId::new(0),
            function_type.clone(),
            node_origin.clone(),
        );
        let parameter = TypedBinder::new(arena, BinderId::new(1), Type::Unit, node_origin.clone());
        let group = StoredNode {
            dialect: DialectId::PURE,
            effects: (),
            ty: Type::Unit,
            origin: Some(node_origin.clone()),
            kind: PureExprKind::Computation(PureComputation::RecursiveBind(
                super::super::recursion::RecursiveBindingNode::new(
                    vec![super::super::recursion::RecursiveBindingMember::new(
                        recursive,
                        NodeId::new(arena, 1),
                    )],
                    NodeId::new(arena, 0),
                ),
            )),
        };
        let function = StoredNode {
            dialect: DialectId::PURE,
            effects: (),
            ty: function_type,
            origin: Some(node_origin.clone()),
            kind: PureExprKind::Value(PureValue::Function(
                super::super::function::FunctionNode::new(parameter, NodeId::new(arena, 2)),
            )),
        };
        let unit = StoredNode {
            dialect: DialectId::PURE,
            effects: (),
            ty: Type::Unit,
            origin: Some(node_origin),
            kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
        };
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            method_evidence: Arc::new(super::super::dialect::MethodEvidenceCatalog::default()),
            method_evidence_anchors: Box::new([]),
            arena,
            nodes: vec![group, function, unit],
            root: NodeId::new(arena, 0),
        };

        let error = validate(program, &[&file]).expect_err("recursive ownership cycle");
        assert_eq!(error.reason(), ValidationReason::Cycle);
        assert_eq!(error.node(), Some(NodeId::new(arena, 0)));
    }

    #[test]
    fn validates_a_deep_arena_with_explicit_work_stacks() {
        let file = source();
        let node_origin = origin(&file);
        let mut builder = CoreBuilder::new();
        let initializer = builder
            .unit(Type::Unit, node_origin.clone())
            .expect("small initial arena");
        let mut root = initializer;
        for _ in 0..10_000 {
            let binder = builder
                .binder(Type::Unit, node_origin.clone())
                .expect("bounded binder set");
            root = builder
                .binding(binder, initializer, root, Type::Unit, node_origin.clone())
                .expect("bounded arena");
        }

        let validated = validate(builder.finish(root).expect("valid root"), &[&file])
            .expect("deep acyclic Core");
        assert_eq!(validated.node_count(), 10_001);
    }

    #[test]
    fn shared_dag_scope_analysis_visits_each_node_once() {
        let file = SourceFile::new("shared.ash", "1").expect("test source");
        let node_origin = Origin::Source(
            file.span(ByteRange::new(0, 1).expect("ordered range"))
                .expect("source span"),
        );
        let mut builder = CoreBuilder::new();
        let mut root = builder
            .integer(
                crate::integer::Integer::parse_decimal("1").expect("test integer"),
                Type::Int,
                node_origin.clone(),
            )
            .expect("small arena");
        for _ in 0..64 {
            root = builder
                .primitive(
                    crate::core::Primitive::Add,
                    root,
                    root,
                    Type::Int,
                    node_origin.clone(),
                )
                .expect("bounded arena");
        }
        let program = builder.finish(root).expect("valid root");
        let sources = [&file];
        let validator = Validator::new(&program, &sources);

        let analysis = validator.analyze_free_binders().expect("valid shared DAG");
        assert!(analysis.root_requirements.is_empty());
        assert_eq!(analysis.analyzed_nodes, program.nodes.len());
    }
}
#[cfg(test)]
mod replacement_owner_api_tests {
    use super::*;

    fn deep_type(depth: usize) -> Type {
        let mut ty = Type::Int;
        for _ in 0..depth {
            ty = Type::Application(Box::new(ty), Box::new(Type::Unit));
        }
        ty
    }

    #[test]
    fn recursive_type_replacements_do_not_bypass_the_owner_api() {
        let source: String = include_str!("validate.rs")
            .chars()
            .filter(|character| !character.is_whitespace())
            .collect();
        let replacement_map = &source[source
            .find("structTypeReplacementMap")
            .expect("the replacement owner exists")
            ..source
                .find("implDropforTypeReplacementMap")
                .expect("the replacement owner has iterative teardown")];
        let raw_field = ["replacements", ".0"].concat();
        assert!(!source.contains(&raw_field));
        let raw_insert = [".0", ".insert("].concat();
        let raw_reserve = [".0", ".try_reserve("].concat();
        assert_eq!(replacement_map.matches(&raw_insert).count(), 1);
        assert_eq!(replacement_map.matches(&raw_reserve).count(), 1);
        let broad_mutation = ["impl", "DerefMut", "for", "TypeReplacementMap"].concat();
        assert!(!source.contains(&broad_mutation));
    }

    #[test]
    fn duplicate_deep_replacement_is_dismantled_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("duplicate-core-validation-replacement".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let parameter = crate::types::TypeVariableId::new(0);
                let mut replacements = TypeReplacementMap::new();
                replacements.insert_replacing(parameter, deep_type(DEPTH));
                replacements.insert_replacing(parameter, deep_type(DEPTH));
            })
            .expect("the duplicate-replacement thread should start")
            .join()
            .expect("duplicate replacement teardown must stay iterative");
    }
}
