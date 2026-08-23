//! Independent validation for unchecked pure Core arenas.

use std::{
    cell::Cell,
    collections::{HashMap, HashSet},
    error::Error,
    fmt,
    sync::Arc,
};

use super::{
    dialect::{
        CORE_PATTERN_DEPTH_LIMIT, DialectId, NodeId, PureComputation, PureExprKind, PureProgram,
        PureValue, StoredNode, TypedExpr, UnvalidatedProgram, ValidatedProgram,
        origin_depth_within_limit,
    },
    variable::TypedBinder,
};
use crate::{
    core::{CorePattern, CorePatternKind},
    pattern::{UsefulnessBudget, missing_witness_for_types_with_budget, usefulness_with_budget},
    resolved::{BinderId, ResolvedNominalType},
    source::{Origin, SourceFile, SourceId, Span},
    types::{ConstructorId, TYPE_WORK_LIMIT, Type, same_type, substitute_type_variables_with},
};

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
    const fn new(reason: ValidationReason, node: Option<NodeId>) -> Self {
        Self { reason, node }
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

fn constructor_belongs_to_owner(owner: &ResolvedNominalType, constructor: ConstructorId) -> bool {
    if constructor.owner() != owner.id {
        return false;
    }
    usize::try_from(constructor.constructor())
        .ok()
        .and_then(|index| owner.constructors.get(index))
        .is_some_and(|owned| *owned == constructor)
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
    if let Err(error) = Validator::new(&program, sources).run() {
        program.discard_iteratively();
        return Err(error);
    }

    let mut nodes = Vec::with_capacity(program.nodes.len());
    for (index, stored) in program.nodes.into_iter().enumerate() {
        let node = node_id(program.arena, index)?;
        let Some(origin) = stored.origin else {
            return Err(ValidationError::new(
                ValidationReason::Provenance,
                Some(node),
            ));
        };
        nodes.push(TypedExpr {
            ty: stored.ty,
            origin,
            kind: stored.kind,
        });
    }

    Ok(ValidatedProgram::new(PureProgram::new(
        Arc::clone(&program.registry),
        program.arena,
        nodes,
        program.root,
    )))
}

struct Validator<'program, 'source> {
    program: &'program UnvalidatedProgram,
    sources: HashMap<SourceId, &'source SourceFile>,
    binders: HashMap<BinderId, &'program TypedBinder>,
    type_work: Cell<usize>,
    #[cfg(test)]
    owner_parameter_index_work: Cell<usize>,
    #[cfg(test)]
    type_validation_pending_peak: Cell<usize>,
}

impl<'program, 'source> Validator<'program, 'source> {
    fn new(program: &'program UnvalidatedProgram, sources: &[&'source SourceFile]) -> Self {
        Self {
            program,
            sources: sources
                .iter()
                .map(|source| (source.id(), *source))
                .collect(),
            binders: HashMap::new(),
            type_work: Cell::new(0),
            #[cfg(test)]
            owner_parameter_index_work: Cell::new(0),
            #[cfg(test)]
            type_validation_pending_peak: Cell::new(0),
        }
    }

    fn run(mut self) -> Result<(), ValidationError> {
        self.validate_registry()?;
        self.validate_envelopes()?;
        self.validate_graph()?;
        self.collect_binders()?;
        self.validate_node_types()?;
        self.validate_scopes()?;
        self.validate_type_scopes()
    }

    fn validate_registry(&self) -> Result<(), ValidationError> {
        let registry = &self.program.registry;
        let mut nominal_ids = HashSet::new();
        let mut nominal_names = HashSet::new();
        let mut constructor_ids = HashSet::new();
        let mut constructor_names = HashSet::new();
        let registry_source = registry
            .nominals()
            .first()
            .map(|nominal| nominal.origin.primary_span().source());
        if let (Some(registry_source), Ok(root)) = (registry_source, self.node(self.program.root))
            && root
                .origin
                .as_ref()
                .is_some_and(|origin| origin.primary_span().source() != registry_source)
        {
            return Err(ValidationError::new(ValidationReason::Registry, None));
        }
        let mut previous_nominal_end = None;
        for (index, nominal) in registry.nominals().iter().enumerate() {
            let index = u32::try_from(index)
                .map_err(|_| ValidationError::new(ValidationReason::Registry, None))?;
            let source = registry_source.unwrap_or_else(|| nominal.id.source());
            let nominal_range = nominal.origin.primary_span().range();
            if nominal.id != crate::types::NominalTypeId::new(source, index)
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
        if registry
            .nominal_parameter_entries()
            .any(|(owner, _)| registry.nominal(owner).is_none())
        {
            return Err(ValidationError::new(ValidationReason::Registry, None));
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
                self.charge_type_work(1)?;
                #[cfg(test)]
                self.owner_parameter_index_work
                    .set(self.owner_parameter_index_work.get() + 1);
                let parameter_span = parameter.origin.primary_span();
                let parameter_range = parameter_span.range();
                if Some(parameter_span.source()) != registry_source
                    || !origin_depth_within_limit(&parameter.origin)
                    || !valid_upper_spelling(&parameter.spelling)
                    || parameter_owners.insert(parameter.id, nominal.id).is_some()
                    || !parameter_names.insert(parameter.spelling.as_str())
                    || registry.type_variable(parameter.id) != Some(parameter)
                    || parameter_range.start() >= parameter_range.end()
                    || parameter_range.start() < nominal_range.start()
                    || parameter_range.end() > nominal_range.end()
                    || previous_parameter_start
                        .is_some_and(|previous| parameter_range.start() <= previous)
                {
                    return Err(ValidationError::new(ValidationReason::Registry, None));
                }
                previous_parameter_start = Some(parameter_range.start());
                self.validate_origin(&parameter.origin, self.program.root)?;
            }
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
            if constructor.id.owner() != constructor.owner
                || !nominal_ids.contains(&constructor.owner)
                || Some(constructor.origin.primary_span().source()) != registry_source
                || !origin_depth_within_limit(&constructor.origin)
                || !valid_upper_spelling(&constructor.spelling)
                || !constructor_ids.insert(constructor.id)
                || !constructor_names.insert(constructor.spelling.as_str())
                || !payload_valid
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
        Ok(())
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
            Visit(&'a Type, bool, usize),
            Sequence(std::slice::Iter<'a, Type>, usize),
        }
        let mut work = vec![Task::Visit(root, allow_scheme, 0)];
        while let Some(task) = work.pop() {
            #[cfg(test)]
            self.type_validation_pending_peak
                .set(self.type_validation_pending_peak.get().max(work.len() + 1));
            match task {
                Task::Visit(ty, allow_scheme, depth) => {
                    if depth > super::dialect::CORE_PAYLOAD_DEPTH_LIMIT {
                        return Ok(false);
                    }
                    self.charge_type_work(1)?;
                    match ty {
                        Type::Int | Type::Bool | Type::Unit => {}
                        Type::Nominal(id)
                            if self
                                .program
                                .registry
                                .nominal_parameters(*id)
                                .is_some_and(<[_]>::is_empty) => {}
                        Type::Nominal(_) => return Ok(false),
                        Type::Variable(_) => {}
                        Type::Inference(_) => return Ok(false),
                        Type::AppliedNominal(id, arguments) => {
                            let Some(nominal) = self.program.registry.nominal(*id) else {
                                return Ok(false);
                            };
                            if self
                                .program
                                .registry
                                .nominal_parameters(nominal.id)
                                .is_none_or(|parameters| parameters.len() != arguments.len())
                            {
                                return Ok(false);
                            }
                            work.push(Task::Sequence(arguments.iter(), depth.saturating_add(1)));
                        }
                        Type::Forall(parameters, body) if allow_scheme => {
                            self.charge_type_work(parameters.len())?;
                            let mut unique = HashSet::new();
                            unique.try_reserve(parameters.len()).map_err(|_| {
                                ValidationError::new(ValidationReason::Resource, None)
                            })?;
                            if parameters.is_empty()
                                || !parameters
                                    .iter()
                                    .copied()
                                    .all(|parameter| unique.insert(parameter))
                            {
                                return Ok(false);
                            }
                            work.push(Task::Visit(body, false, depth.saturating_add(1)));
                        }
                        Type::Forall(_, _) => return Ok(false),
                        Type::Tuple(elements) if elements.len() >= 2 => {
                            work.push(Task::Sequence(elements.iter(), depth.saturating_add(1)));
                        }
                        Type::Tuple(_) => return Ok(false),
                        Type::Function(domain, codomain) => {
                            let child_depth = depth.saturating_add(1);
                            work.push(Task::Visit(codomain, false, child_depth));
                            work.push(Task::Visit(domain, false, child_depth));
                        }
                    }
                }
                Task::Sequence(mut remaining, depth) => {
                    if let Some(ty) = remaining.next() {
                        work.push(Task::Sequence(remaining, depth));
                        work.push(Task::Visit(ty, false, depth));
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
        parameter_owners: &HashMap<crate::types::TypeVariableId, crate::types::NominalTypeId>,
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
                Type::Nominal(id)
                    if self
                        .program
                        .registry
                        .nominal_parameters(*id)
                        .is_some_and(<[_]>::is_empty) => {}
                Type::Nominal(_) => return Ok(false),
                Type::Variable(variable) if parameter_owners.get(variable) == Some(&owner) => {}
                Type::Variable(_) | Type::Inference(_) | Type::Forall(_, _) => return Ok(false),
                Type::AppliedNominal(id, arguments) => {
                    if self
                        .program
                        .registry
                        .nominal_parameters(*id)
                        .is_none_or(|parameters| parameters.len() != arguments.len())
                    {
                        return Ok(false);
                    }
                    work.push(Task::Sequence(arguments.iter(), depth.saturating_add(1)));
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
            }
        }
        Ok(true)
    }

    fn charge_type_work(&self, cells: usize) -> Result<(), ValidationError> {
        let next = self
            .type_work
            .get()
            .checked_add(cells)
            .filter(|next| *next <= TYPE_WORK_LIMIT)
            .ok_or_else(|| ValidationError::new(ValidationReason::Resource, None))?;
        self.type_work.set(next);
        Ok(())
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
                Type::Tuple(elements) | Type::AppliedNominal(_, elements) => {
                    work.push(Task::Sequence(elements.iter()));
                }
                Type::Function(domain, codomain) => {
                    work.push(Task::Visit(codomain));
                    work.push(Task::Visit(domain));
                }
                Type::Forall(parameters, body) => {
                    self.charge_type_work(parameters.len())?;
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

    fn validate_envelopes(&self) -> Result<(), ValidationError> {
        for (index, node) in self.program.nodes.iter().enumerate() {
            let id = node_id(self.program.arena, index)?;
            if !self.valid_type(Some(&node.ty))? {
                return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
            }
            if node.dialect != DialectId::PURE {
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
                    work.push(GraphTask::Exit(id));
                    let node = self.node(id)?;
                    for child_index in (0..node.kind.child_count()).rev() {
                        let Some(child) = node.kind.child_at(child_index) else {
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

    fn collect_binders(&mut self) -> Result<(), ValidationError> {
        for (index, node) in self.program.nodes.iter().enumerate() {
            let id = node_id(self.program.arena, index)?;
            match &node.kind {
                PureExprKind::Value(PureValue::Function(function)) => {
                    self.collect_binder(
                        id,
                        function.parameter(),
                        ValidationReason::NodeType,
                        true,
                    )?;
                }
                PureExprKind::Computation(PureComputation::Bind(binding)) => {
                    self.collect_binder(id, binding.binder(), ValidationReason::NodeType, true)?;
                }
                PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
                    for member in group.members() {
                        self.collect_binder(id, member.binder(), ValidationReason::NodeType, true)?;
                    }
                }
                PureExprKind::Computation(PureComputation::Match(match_node)) => {
                    for arm in match_node.arms() {
                        let mut binders = Vec::new();
                        arm.pattern().binders(&mut binders);
                        for binder in binders {
                            self.collect_binder(id, binder, ValidationReason::Pattern, false)?;
                        }
                    }
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
                    | PureComputation::TypeAbstraction(_)
                    | PureComputation::TypeApplication(_),
                ) => {}
            }
        }
        Ok(())
    }

    fn collect_binder(
        &mut self,
        node: NodeId,
        binder: &'program TypedBinder,
        invalid_type: ValidationReason,
        allow_scheme: bool,
    ) -> Result<(), ValidationError> {
        if binder.arena() != self.program.arena {
            return Err(ValidationError::new(ValidationReason::Scope, Some(node)));
        }
        self.validate_origin(binder.origin(), node)?;
        let type_valid = if allow_scheme {
            self.valid_type(Some(binder.ty()))?
        } else {
            self.valid_monotype(Some(binder.ty()))?
        };
        if !type_valid {
            return Err(ValidationError::new(invalid_type, Some(node)));
        }
        if self.binders.insert(binder.id(), binder).is_some() {
            return Err(ValidationError::new(ValidationReason::Scope, Some(node)));
        }
        Ok(())
    }

    fn validate_node_types(&self) -> Result<(), ValidationError> {
        for (index, node) in self.program.nodes.iter().enumerate() {
            let id = node_id(self.program.arena, index)?;
            match &node.kind {
                PureExprKind::Value(value) => self.validate_value(id, node, value)?,
                PureExprKind::Variable(variable) => {
                    let Some(binder) = self.binders.get(&variable.binder()) else {
                        return Err(ValidationError::new(ValidationReason::Scope, Some(id)));
                    };
                    if !same_type(&node.ty, binder.ty()) {
                        return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                    }
                }
                PureExprKind::Computation(computation) => {
                    self.validate_computation(id, node, computation)?;
                }
            }
        }
        Ok(())
    }

    fn validate_value(
        &self,
        id: NodeId,
        node: &StoredNode,
        value: &PureValue,
    ) -> Result<(), ValidationError> {
        let expected = match value {
            PureValue::Integer(integer) => integer.expected_type(),
            PureValue::Boolean(boolean) => boolean.expected_type(),
            PureValue::Unit(unit) => unit.expected_type(),
            PureValue::Function(function) => {
                let body = self.node(function.body())?;
                Type::Function(
                    Box::new(function.parameter().ty().clone()),
                    Box::new(body.ty.clone()),
                )
            }
            PureValue::Constructor(constructor) => {
                let Some(info) = self.program.registry.constructor(constructor.constructor())
                else {
                    return Err(ValidationError::new(ValidationReason::Registry, Some(id)));
                };
                let parameters = self
                    .program
                    .registry
                    .nominal_parameters(info.owner)
                    .ok_or_else(|| ValidationError::new(ValidationReason::Registry, Some(id)))?;
                let result = if parameters.is_empty() {
                    Type::Nominal(info.owner)
                } else {
                    Type::AppliedNominal(
                        info.owner,
                        parameters
                            .iter()
                            .map(|parameter| Type::Variable(parameter.id))
                            .collect::<Vec<_>>()
                            .into_boxed_slice(),
                    )
                };
                let monotype = info.payload.as_ref().map_or(result.clone(), |payload| {
                    Type::Function(Box::new(payload.clone()), Box::new(result))
                });
                let expected = if parameters.is_empty() {
                    monotype
                } else {
                    Type::Forall(
                        parameters
                            .iter()
                            .map(|parameter| parameter.id)
                            .collect::<Vec<_>>()
                            .into_boxed_slice(),
                        Box::new(monotype),
                    )
                };
                if !same_type(&node.ty, &expected) {
                    return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                }
                return Ok(());
            }
        };
        if !same_type(&node.ty, &expected) {
            return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
        }
        Ok(())
    }

    fn validate_computation(
        &self,
        id: NodeId,
        node: &StoredNode,
        computation: &PureComputation,
    ) -> Result<(), ValidationError> {
        match computation {
            PureComputation::Bind(binding) => {
                let initializer = self.node(binding.initializer())?;
                let body = self.node(binding.body())?;
                if !same_type(&initializer.ty, binding.binder().ty())
                    || !same_type(&node.ty, &body.ty)
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
                            initializer.kind,
                            PureExprKind::Value(PureValue::Function(_))
                        ),
                        Type::Nominal(owner) => {
                            self.guarded_data_root(member.initializer(), *owner, &recursive)?
                        }
                        Type::AppliedNominal(owner, _) => {
                            self.guarded_data_root(member.initializer(), *owner, &recursive)?
                        }
                        Type::Forall(parameters, body)
                            if matches!(body.as_ref(), Type::Function(_, _)) =>
                        {
                            let PureExprKind::Computation(PureComputation::TypeAbstraction(
                                abstraction,
                            )) = &initializer.kind
                            else {
                                return Err(ValidationError::new(
                                    ValidationReason::RecursiveBinding,
                                    Some(id),
                                ));
                            };
                            abstraction.parameters() == parameters.as_ref()
                                && matches!(
                                    self.node(abstraction.body())?.kind,
                                    PureExprKind::Value(PureValue::Function(_))
                                )
                        }
                        Type::Int
                        | Type::Bool
                        | Type::Unit
                        | Type::Tuple(_)
                        | Type::Variable(_)
                        | Type::Inference(_)
                        | Type::Forall(_, _) => false,
                    };
                    if !safe {
                        return Err(ValidationError::new(
                            ValidationReason::RecursiveBinding,
                            Some(id),
                        ));
                    }
                    if !same_type(&initializer.ty, member.binder().ty()) {
                        return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                    }
                }
                let body = self.node(group.body())?;
                if !same_type(&node.ty, &body.ty) {
                    return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                }
            }
            PureComputation::Apply(application) => {
                let function = self.node(application.function())?;
                let argument = self.node(application.argument())?;
                let Type::Function(domain, codomain) = &function.ty else {
                    return Err(ValidationError::new(
                        ValidationReason::ApplicationType,
                        Some(id),
                    ));
                };
                if !same_type(domain, &argument.ty) || !same_type(codomain, &node.ty) {
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
                if !same_type(&left.ty, &left_type)
                    || !same_type(&right.ty, &right_type)
                    || !same_type(&node.ty, &result_type)
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
                    if !same_type(&self.node(*element)?.ty, expected) {
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
                let mut matrix = Vec::new();
                let mut coverage_budget = UsefulnessBudget::default();
                for arm in match_node.arms() {
                    self.validate_origin(arm.origin(), id)?;
                    self.validate_pattern(arm.pattern(), &scrutinee.ty, id)?;
                    if !same_type(&self.node(arm.body())?.ty, &node.ty) {
                        return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                    }
                    let row = vec![arm.pattern().clone()];
                    if usefulness_with_budget(
                        &matrix,
                        &row,
                        std::slice::from_ref(&scrutinee.ty),
                        &self.program.registry,
                        &mut coverage_budget,
                    )
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?
                    .is_none()
                    {
                        return Err(ValidationError::new(ValidationReason::Coverage, Some(id)));
                    }
                    matrix.push(row);
                }
                if missing_witness_for_types_with_budget(
                    &matrix,
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
            PureComputation::TypeAbstraction(abstraction) => {
                let body = self.node(abstraction.body())?;
                let Type::Forall(parameters, scheme_body) = &node.ty else {
                    return Err(ValidationError::new(
                        ValidationReason::TypeOperation,
                        Some(id),
                    ));
                };
                self.charge_type_work(abstraction.parameters().len())?;
                let mut unique = HashSet::new();
                unique
                    .try_reserve(abstraction.parameters().len())
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?;
                if abstraction.parameters().is_empty()
                    || !abstraction
                        .parameters()
                        .iter()
                        .copied()
                        .all(|parameter| unique.insert(parameter))
                    || abstraction.parameters() != parameters.as_ref()
                    || !same_type(&body.ty, scheme_body)
                    || matches!(scheme_body.as_ref(), Type::Forall(_, _))
                {
                    return Err(ValidationError::new(
                        ValidationReason::TypeOperation,
                        Some(id),
                    ));
                }
            }
            PureComputation::TypeApplication(application) => {
                let function = self.node(application.function())?;
                let Type::Forall(parameters, body) = &function.ty else {
                    return Err(ValidationError::new(
                        ValidationReason::TypeOperation,
                        Some(id),
                    ));
                };
                let mut invalid_argument = false;
                for argument in application.arguments() {
                    invalid_argument |= matches!(argument, Type::Forall(_, _))
                        || !self.valid_type(Some(argument))?;
                }
                if parameters.len() != application.arguments().len() || invalid_argument {
                    return Err(ValidationError::new(
                        ValidationReason::TypeOperation,
                        Some(id),
                    ));
                }
                self.charge_type_work(parameters.len())?;
                let mut replacements = HashMap::new();
                replacements
                    .try_reserve(parameters.len())
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?;
                replacements.extend(
                    parameters
                        .iter()
                        .zip(application.arguments())
                        .map(|(parameter, argument)| (*parameter, argument.clone())),
                );
                let instantiated = substitute_type_variables_with(body, &replacements, |cells| {
                    self.charge_type_work(cells)
                })?;
                if !same_type(&node.ty, &instantiated) {
                    return Err(ValidationError::new(
                        ValidationReason::TypeOperation,
                        Some(id),
                    ));
                }
            }
        }
        Ok(())
    }

    fn guarded_data_root(
        &self,
        initializer: NodeId,
        owner: crate::types::NominalTypeId,
        recursive: &HashSet<BinderId>,
    ) -> Result<bool, ValidationError> {
        let initializer = self.erase_type_applications(initializer)?;
        let root = self.node(initializer)?;
        let payload = match &root.kind {
            PureExprKind::Value(PureValue::Constructor(constructor)) => {
                let Some(info) = self.program.registry.constructor(constructor.constructor())
                else {
                    return Ok(false);
                };
                if info.owner != owner || info.payload.is_some() {
                    return Ok(false);
                }
                return Ok(true);
            }
            PureExprKind::Computation(PureComputation::Apply(application)) => {
                let function = self.node(self.erase_type_applications(application.function())?)?;
                let PureExprKind::Value(PureValue::Constructor(constructor)) = &function.kind
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
            match &node.kind {
                PureExprKind::Variable(variable) if recursive.contains(&variable.binder()) => {}
                PureExprKind::Computation(PureComputation::Tuple(tuple)) => {
                    work.extend(tuple.elements().iter().copied());
                }
                PureExprKind::Computation(PureComputation::Apply(application)) => {
                    let function =
                        self.node(self.erase_type_applications(application.function())?)?;
                    if !matches!(
                        function.kind,
                        PureExprKind::Value(PureValue::Constructor(_))
                    ) {
                        return Ok(false);
                    }
                    work.push(application.argument());
                }
                PureExprKind::Value(PureValue::Function(_)) => {}
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    fn erase_type_applications(&self, mut id: NodeId) -> Result<NodeId, ValidationError> {
        loop {
            let node = self.node(id)?;
            let PureExprKind::Computation(PureComputation::TypeApplication(application)) =
                &node.kind
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
                    work.push(Task::Finish(id));
                    for index in 0..node.kind.child_count() {
                        work.push(Task::Visit(node.kind.child_at(index).ok_or_else(|| {
                            ValidationError::new(ValidationReason::NodeBounds, Some(id))
                        })?));
                    }
                }
                Task::Finish(id) => {
                    let node = self.node(id)?;
                    let direct = matches!(
                        &node.kind,
                        PureExprKind::Variable(variable)
                            if recursive.contains(&variable.binder())
                    );
                    let mut reaches = direct;
                    for index in 0..node.kind.child_count() {
                        let child = node.kind.child_at(index).ok_or_else(|| {
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
            Owned(Type),
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
                types: std::vec::IntoIter<Type>,
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
                        work.push(Task::Visit(pattern, Expected::Owned(ty), depth));
                    }
                    continue;
                }
            };
            if depth > CORE_PATTERN_DEPTH_LIMIT {
                return Err(ValidationError::new(ValidationReason::Pattern, Some(node)));
            }
            self.validate_origin(&pattern.origin, node)?;
            if !same_type(&pattern.ty, expected.as_type())
                || !self.valid_monotype(Some(&pattern.ty))?
            {
                return Err(ValidationError::new(ValidationReason::Pattern, Some(node)));
            }
            match &pattern.kind {
                CorePatternKind::Binder(binder) => {
                    if binder.arena() != self.program.arena
                        || !same_type(binder.ty(), expected.as_type())
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
                    Expected::Owned(Type::Tuple(types)) if patterns.len() == types.len() => {
                        work.push(Task::OwnedTupleSequence {
                            patterns: patterns.iter(),
                            types: types.into_vec().into_iter(),
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
                    let (owner, arguments): (_, &[Type]) = match expected.as_type() {
                        Type::Nominal(owner) => (*owner, &[]),
                        Type::AppliedNominal(owner, arguments) => (*owner, arguments),
                        _ => {
                            return Err(ValidationError::new(
                                ValidationReason::Pattern,
                                Some(node),
                            ));
                        }
                    };
                    let Some(info) = self.program.registry.constructor(*constructor) else {
                        return Err(ValidationError::new(ValidationReason::Pattern, Some(node)));
                    };
                    if info.owner != owner {
                        return Err(ValidationError::new(ValidationReason::Pattern, Some(node)));
                    }
                    let Some(parameters) = self.program.registry.nominal_parameters(owner) else {
                        return Err(ValidationError::new(ValidationReason::Pattern, Some(node)));
                    };
                    if parameters.len() != arguments.len() {
                        return Err(ValidationError::new(ValidationReason::Pattern, Some(node)));
                    }
                    let replacements = parameters
                        .iter()
                        .zip(arguments)
                        .map(|(parameter, argument)| (parameter.id, argument.clone()))
                        .collect();
                    let payload_type = info
                        .payload
                        .as_ref()
                        .map(|payload| {
                            substitute_type_variables_with(payload, &replacements, |cells| {
                                self.charge_type_work(cells)
                            })
                        })
                        .transpose()?;
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
        if let Some(occurrence) = analysis
            .root_requirements
            .values()
            .min_by_key(|node| node.value())
        {
            return Err(ValidationError::new(
                ValidationReason::Scope,
                Some(*occurrence),
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
            for child_index in 0..node.kind.child_count() {
                let child = node
                    .kind
                    .child_at(child_index)
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
                    work.push(ScopeAnalysisTask::Finish(id));
                    let kind = &self.node(id)?.kind;
                    for child_index in (0..kind.child_count()).rev() {
                        let child = kind.child_at(child_index).ok_or_else(|| {
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
                    for child_index in 0..node.kind.child_count() {
                        let child = node.kind.child_at(child_index).ok_or_else(|| {
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
                    match &node.kind {
                        PureExprKind::Value(PureValue::Function(function)) => {
                            self.charge_type_structure(function.parameter().ty())?;
                            self.collect_free_type_variables(function.parameter().ty(), &mut free)?;
                        }
                        PureExprKind::Computation(PureComputation::Bind(binding)) => {
                            self.charge_type_structure(binding.binder().ty())?;
                            self.collect_free_type_variables(binding.binder().ty(), &mut free)?;
                        }
                        PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
                            for member in group.members() {
                                self.charge_type_structure(member.binder().ty())?;
                                self.collect_free_type_variables(member.binder().ty(), &mut free)?;
                            }
                        }
                        PureExprKind::Computation(PureComputation::Match(match_node)) => {
                            for arm in match_node.arms() {
                                self.charge_pattern_type_structure(arm.pattern())?;
                                self.collect_pattern_type_variables(arm.pattern(), &mut free)?;
                            }
                        }
                        PureExprKind::Computation(PureComputation::TypeApplication(operation)) => {
                            for argument in operation.arguments() {
                                self.charge_type_structure(argument)?;
                                self.collect_free_type_variables(argument, &mut free)?;
                            }
                        }
                        PureExprKind::Computation(PureComputation::TypeAbstraction(operation)) => {
                            for parameter in operation.parameters() {
                                free.remove(parameter);
                            }
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
                            | PureComputation::Tuple(_),
                        ) => {}
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
                Task::Visit(Type::Tuple(elements) | Type::AppliedNominal(_, elements)) => {
                    work.push(Task::Sequence(elements.iter()));
                }
                Task::Visit(Type::Function(domain, codomain)) => {
                    work.push(Task::Visit(codomain));
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
            for parameter in parameters {
                discovered.remove(parameter);
            }
        }
        self.merge_type_scope_requirements(output, discovered)
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
                    work.push(ScopeAnalysisTask::Finish(id));
                    let kind = &self.node(id)?.kind;
                    for child_index in (0..kind.child_count()).rev() {
                        let child = kind.child_at(child_index).ok_or_else(|| {
                            ValidationError::new(ValidationReason::Scope, Some(id))
                        })?;
                        work.push(ScopeAnalysisTask::Enter(child));
                    }
                }
                ScopeAnalysisTask::Finish(id) => {
                    let node = self.node(id)?;
                    let free = match &node.kind {
                        PureExprKind::Variable(variable) => {
                            HashMap::from([(variable.binder(), id)])
                        }
                        PureExprKind::Value(PureValue::Function(function)) => {
                            let mut body = self.requirements_for(&requirements, function.body())?;
                            body.remove(&function.parameter().id());
                            body
                        }
                        PureExprKind::Computation(PureComputation::Bind(binding)) => {
                            let initializer =
                                self.requirements_for(&requirements, binding.initializer())?;
                            let mut body = self.requirements_for(&requirements, binding.body())?;
                            body.remove(&binding.binder().id());
                            union_requirements(initializer, body)
                        }
                        PureExprKind::Computation(PureComputation::RecursiveBind(group)) => {
                            let mut free = self.requirements_for(&requirements, group.body())?;
                            for member in group.members() {
                                let initializer =
                                    self.requirements_for(&requirements, member.initializer())?;
                                free = union_requirements(free, initializer);
                            }
                            for member in group.members() {
                                free.remove(&member.binder().id());
                            }
                            free
                        }
                        PureExprKind::Computation(PureComputation::Apply(application)) => {
                            let function =
                                self.requirements_for(&requirements, application.function())?;
                            let argument =
                                self.requirements_for(&requirements, application.argument())?;
                            union_requirements(function, argument)
                        }
                        PureExprKind::Computation(PureComputation::Primitive(primitive)) => {
                            let left = self.requirements_for(&requirements, primitive.left())?;
                            let right = self.requirements_for(&requirements, primitive.right())?;
                            union_requirements(left, right)
                        }
                        PureExprKind::Computation(PureComputation::Tuple(tuple)) => {
                            let mut free = HashMap::new();
                            for element in tuple.elements() {
                                free = union_requirements(
                                    free,
                                    self.requirements_for(&requirements, *element)?,
                                );
                            }
                            free
                        }
                        PureExprKind::Computation(PureComputation::Match(match_node)) => {
                            let mut free =
                                self.requirements_for(&requirements, match_node.scrutinee())?;
                            for arm in match_node.arms() {
                                let mut arm_free =
                                    self.requirements_for(&requirements, arm.body())?;
                                let mut binders = Vec::new();
                                arm.pattern().binders(&mut binders);
                                for binder in binders {
                                    arm_free.remove(&binder.id());
                                }
                                free = union_requirements(free, arm_free);
                            }
                            free
                        }
                        PureExprKind::Computation(PureComputation::TypeAbstraction(operation)) => {
                            self.requirements_for(&requirements, operation.body())?
                        }
                        PureExprKind::Computation(PureComputation::TypeApplication(operation)) => {
                            self.requirements_for(&requirements, operation.function())?
                        }
                        PureExprKind::Value(
                            PureValue::Integer(_)
                            | PureValue::Boolean(_)
                            | PureValue::Unit(_)
                            | PureValue::Constructor(_),
                        ) => HashMap::new(),
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
        requirements: &[Option<HashMap<BinderId, NodeId>>],
        id: NodeId,
    ) -> Result<HashMap<BinderId, NodeId>, ValidationError> {
        let index = self.index(id)?;
        let Some(free) = requirements.get(index).and_then(Option::as_ref) else {
            return Err(ValidationError::new(ValidationReason::Scope, Some(id)));
        };
        Ok(free.clone())
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

    fn node(&self, id: NodeId) -> Result<&'program StoredNode, ValidationError> {
        let index = self.index(id)?;
        self.program
            .nodes
            .get(index)
            .ok_or_else(|| ValidationError::new(ValidationReason::NodeBounds, Some(id)))
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
    root_requirements: HashMap<BinderId, NodeId>,
    analyzed_nodes: usize,
}

enum ScopeAnalysisTask {
    Enter(NodeId),
    Finish(NodeId),
}

fn union_requirements(
    mut left: HashMap<BinderId, NodeId>,
    right: HashMap<BinderId, NodeId>,
) -> HashMap<BinderId, NodeId> {
    for (binder, occurrence) in right {
        left.entry(binder).or_insert(occurrence);
    }
    left
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
        core::{CoreBuilder, PureValue},
        source::ByteRange,
    };

    fn source() -> SourceFile {
        SourceFile::new("test.ash", "()").expect("test source")
    }

    fn origin(source: &SourceFile) -> Origin {
        let range = ByteRange::new(0, 2).expect("ordered range");
        Origin::Source(source.span(range).expect("source span"))
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
            arena,
            nodes: vec![
                StoredNode {
                    dialect: DialectId::PURE,
                    ty: binder.ty().clone(),
                    origin: Some(origin(source)),
                    kind: PureExprKind::Variable(super::super::variable::VariableNode::new(
                        binder.id(),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
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
            arena,
            nodes: vec![
                StoredNode {
                    dialect: DialectId::PURE,
                    ty: scrutinee_type.clone(),
                    origin: Some(origin(source)),
                    kind: PureExprKind::Variable(super::super::variable::VariableNode::new(
                        binder.id(),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    ty: Type::Unit,
                    origin: Some(origin(source)),
                    kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
                },
                StoredNode {
                    dialect: DialectId::PURE,
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
                arena,
                nodes: vec![StoredNode {
                    dialect: DialectId::PURE,
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
                    arena,
                    nodes: vec![StoredNode {
                        dialect: DialectId::PURE,
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
            arena,
            nodes: vec![StoredNode {
                dialect: DialectId::PURE,
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
    fn wide_type_validation_retains_constant_pending_work() {
        let file = source();
        let arena = super::super::dialect::ArenaId::new(184);
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            arena,
            nodes: vec![StoredNode {
                dialect: DialectId::PURE,
                ty: Type::Tuple(
                    vec![Type::Int; crate::types::TYPE_WORK_LIMIT + 1].into_boxed_slice(),
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
    fn oversized_malformed_forall_maps_directly_to_validation_resource() {
        let file = source();
        let arena = super::super::dialect::ArenaId::new(100);
        let parameters = (0..crate::types::TYPE_WORK_LIMIT)
            .map(|index| {
                crate::types::TypeVariableId::new(u32::try_from(index).expect("parameter identity"))
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            arena,
            nodes: vec![StoredNode {
                dialect: DialectId::PURE,
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
            arena,
            nodes: vec![
                StoredNode {
                    dialect: DialectId::PURE,
                    ty: Type::Variable(parameter),
                    origin: Some(origin(&file)),
                    kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    ty: Type::Forall(
                        vec![parameter].into_boxed_slice(),
                        Box::new(Type::Variable(parameter)),
                    ),
                    origin: Some(origin(&file)),
                    kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                        super::super::type_ops::TypeAbstractionNode::new(
                            vec![parameter],
                            NodeId::new(arena, 0),
                        ),
                    )),
                },
            ],
            root: NodeId::new(arena, 1),
        };
        let validator = Validator::new(&program, &[&file]);
        validator
            .charge_type_work(TYPE_WORK_LIMIT - 3)
            .expect("test setup leaves the old structural allowance");

        let error = validator
            .validate_type_scopes()
            .expect_err("retained type-scope requirements must be charged");
        assert_eq!(error.reason(), ValidationReason::Resource);
    }

    #[test]
    fn linear_type_scope_chain_uses_the_exact_proportional_budget() {
        const WIDTH: usize = 4_096;
        const EXPECTED_WORK: usize = 5 * WIDTH + 2;
        let file = source();
        let origin = origin(&file);
        let arena = super::super::dialect::ArenaId::new(104);
        let parameters = (0..WIDTH)
            .map(|index| {
                crate::types::TypeVariableId::new(u32::try_from(index).expect("parameter identity"))
            })
            .collect::<Vec<_>>();
        let mut nodes = vec![StoredNode {
            dialect: DialectId::PURE,
            ty: Type::Unit,
            origin: Some(origin.clone()),
            kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
        }];
        for (index, parameter) in parameters.iter().copied().enumerate() {
            nodes.push(StoredNode {
                dialect: DialectId::PURE,
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
            ty: Type::Forall(parameters.clone().into_boxed_slice(), Box::new(Type::Unit)),
            origin: Some(origin),
            kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                super::super::type_ops::TypeAbstractionNode::new(parameters, body),
            )),
        });
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            arena,
            nodes,
            root,
        };
        let validator = Validator::new(&program, &[&file]);
        validator
            .charge_type_work(TYPE_WORK_LIMIT - EXPECTED_WORK)
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
            vec![parameter].into_boxed_slice(),
            Box::new(Type::Variable(parameter)),
        );
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            arena,
            nodes: vec![
                StoredNode {
                    dialect: DialectId::PURE,
                    ty: Type::Variable(parameter),
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    ty: scheme.clone(),
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                        super::super::type_ops::TypeAbstractionNode::new(
                            vec![parameter],
                            occurrence,
                        ),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    ty: Type::Forall(
                        vec![outer_parameter].into_boxed_slice(),
                        Box::new(Type::Unit),
                    ),
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                        super::super::type_ops::TypeAbstractionNode::new(
                            vec![outer_parameter],
                            inner,
                        ),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    ty: scheme,
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                        super::super::type_ops::TypeAbstractionNode::new(
                            vec![parameter],
                            occurrence,
                        ),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
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
            crate::types::TypeVariableId::new(0),
            crate::types::TypeVariableId::new(1),
        ]
        .into_boxed_slice();
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
            arena,
            nodes: vec![StoredNode {
                dialect: DialectId::PURE,
                ty: Type::Unit,
                origin: Some(origin(&file)),
                kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
            }],
            root: NodeId::new(arena, 0),
        };
        let validator = Validator::new(&program, &[&file]);
        validator
            .charge_type_work(TYPE_WORK_LIMIT - 4)
            .expect("test setup leaves four type-work cells");

        assert!(
            validator
                .valid_type(Some(&Type::Forall(parameters, Box::new(Type::Unit))))
                .expect("the exact quantifier boundary validates")
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
            arena,
            nodes: vec![
                StoredNode {
                    dialect: DialectId::PURE,
                    ty: Type::Unit,
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    ty: Type::Forall(vec![parameter].into_boxed_slice(), Box::new(Type::Unit)),
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Computation(PureComputation::TypeAbstraction(
                        super::super::type_ops::TypeAbstractionNode::new(vec![parameter], body),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
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

        let abstraction_validator = Validator::new(&program, &[&file]);
        abstraction_validator
            .charge_type_work(TYPE_WORK_LIMIT - 1)
            .expect("test setup leaves one abstraction-binder entry");
        abstraction_validator
            .validate_computation(
                abstraction,
                &program.nodes[1],
                match &program.nodes[1].kind {
                    PureExprKind::Computation(computation) => computation,
                    _ => unreachable!("test abstraction computation"),
                },
            )
            .expect("one abstraction binder fits exactly");
        assert_eq!(
            abstraction_validator
                .charge_type_work(1)
                .expect_err("the binder consumed the remaining work")
                .reason(),
            ValidationReason::Resource
        );

        let application_validator = Validator::new(&program, &[&file]);
        application_validator
            .charge_type_work(TYPE_WORK_LIMIT - 3)
            .expect("test setup leaves argument, index, and substitution work");
        application_validator
            .validate_computation(
                application,
                &program.nodes[2],
                match &program.nodes[2].kind {
                    PureExprKind::Computation(computation) => computation,
                    _ => unreachable!("test application computation"),
                },
            )
            .expect("one argument, replacement entry, and result cell fit exactly");
        assert_eq!(
            application_validator
                .charge_type_work(1)
                .expect_err("type application consumed the remaining work")
                .reason(),
            ValidationReason::Resource
        );
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
            ty: Type::Unit,
            origin: Some(origin(&file)),
            kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
        };
        let function = StoredNode {
            dialect: DialectId::PURE,
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
            arena,
            nodes: vec![stored],
            root: NodeId::new(arena, 0),
        };
        let error = validate(program, &[&file]).expect_err("out-of-bounds child");
        assert_eq!(error.reason(), ValidationReason::NodeBounds);

        let cyclic = StoredNode {
            dialect: DialectId::PURE,
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
            ty: function_type,
            origin: Some(node_origin.clone()),
            kind: PureExprKind::Value(PureValue::Function(
                super::super::function::FunctionNode::new(parameter, NodeId::new(arena, 2)),
            )),
        };
        let unit = StoredNode {
            dialect: DialectId::PURE,
            ty: Type::Unit,
            origin: Some(node_origin),
            kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
        };
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
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
