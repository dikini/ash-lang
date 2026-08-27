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
        CORE_PATTERN_DEPTH_LIMIT, DialectId, NodeId, PureComputation, PureExprKind, PureProgram,
        PureValue, StoredNode, TypedExpr, UnvalidatedProgram, ValidatedProgram,
        origin_depth_within_limit,
    },
    variable::TypedBinder,
};
use crate::{
    core::{CorePattern, CorePatternKind},
    module::ModuleId,
    pattern::{UsefulnessBudget, missing_witness_for_types_with_budget, usefulness_with_budget},
    resolved::{
        BinderId, ResolvedConstructor, ResolvedNominalType, ResolvedTypeVariable,
        same_resolved_type_variables_with_charge,
    },
    source::{Origin, SourceFile, SourceId, Span},
    types::{
        ConstructorId, IterativeTypeOwner, Kind, TYPE_WORK_LIMIT, Type, discard_type_iteratively,
        same_type_with_budget, substitute_type_variables_with,
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

impl OwnedTypeSequence {
    fn next(&mut self) -> Option<Type> {
        self.0.next()
    }
}

type CoreTypeBinders<'a> = HashMap<crate::types::TypeVariableId, (&'a Kind, NodeId)>;
type CoreAbstractionOwners = HashMap<NodeId, BinderId>;

#[derive(Clone, Copy)]
enum MonotypeVariableKinds<'scope, 'kind> {
    Core(&'scope CoreTypeBinders<'kind>),
    Registry {
        owner: crate::types::NominalTypeId,
        parameter_owners:
            &'scope HashMap<crate::types::TypeVariableId, crate::types::NominalTypeId>,
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

    let (registry, arena, stored_nodes, root) = program.into_parts();
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
            origin,
            kind: stored.kind,
        });
    }

    Ok(ValidatedProgram::new(PureProgram::new(
        registry, arena, nodes, root,
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
    let validator = match Validator::new_modules(&program, sources, module_sources) {
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

    let (registry, arena, stored_nodes, root) = program.into_parts();
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
            origin,
            kind: stored.kind,
        });
    }

    Ok(ValidatedProgram::new(PureProgram::new(
        registry, arena, nodes, root,
    )))
}

struct Validator<'program, 'source> {
    program: &'program UnvalidatedProgram,
    sources: HashMap<SourceId, &'source SourceFile>,
    module_sources: Option<HashMap<ModuleId, SourceId>>,
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
            module_sources: None,
            binders: HashMap::new(),
            type_work: Cell::new(0),
            #[cfg(test)]
            owner_parameter_index_work: Cell::new(0),
            #[cfg(test)]
            type_validation_pending_peak: Cell::new(0),
        }
    }

    fn new_modules(
        program: &'program UnvalidatedProgram,
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

    fn run(mut self) -> Result<(), ValidationError> {
        let nominal_parameter_owners = self.validate_registry()?;
        self.validate_envelopes()?;
        self.validate_graph()?;
        let abstraction_owners = self.collect_binders()?;
        let type_binders =
            self.collect_type_binders(&nominal_parameter_owners, &abstraction_owners)?;
        self.validate_node_types(&nominal_parameter_owners, &type_binders)?;
        self.validate_scopes()?;
        self.validate_type_scopes()
    }

    fn validate_registry(
        &self,
    ) -> Result<HashMap<crate::types::TypeVariableId, crate::types::NominalTypeId>, ValidationError>
    {
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
                if parameter_owners.insert(parameter.id, nominal.id).is_some()
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
        nominal_parameter_owners: &HashMap<
            crate::types::TypeVariableId,
            crate::types::NominalTypeId,
        >,
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

    fn validate_module_registry(
        &self,
    ) -> Result<HashMap<crate::types::TypeVariableId, crate::types::NominalTypeId>, ValidationError>
    {
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
                    || parameter_owners.insert(parameter.id, nominal.id).is_some()
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
                Type::Nominal(id) => {
                    if self.program.registry.nominal_parameters(*id).is_none() {
                        return Ok(false);
                    }
                }
                Type::Variable(variable) if parameter_owners.get(variable) == Some(&owner) => {}
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
            }
        }
        Ok(true)
    }

    fn valid_registry_payload_kind(
        &self,
        root: Option<&Type>,
        owner: crate::types::NominalTypeId,
        parameter_owners: &HashMap<crate::types::TypeVariableId, crate::types::NominalTypeId>,
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
                (Kind::Type, Kind::Type) => {}
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
                            if parameter_owners.get(identity) != Some(&owner) {
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

    fn collect_binders(&mut self) -> Result<CoreAbstractionOwners, ValidationError> {
        let mut abstraction_owners = HashMap::new();
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
                        let initializer = member.initializer();
                        if self.module_sources.is_some()
                            && matches!(
                                self.node(initializer)?.kind,
                                PureExprKind::Computation(PureComputation::TypeAbstraction(_))
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
                PureExprKind::Computation(PureComputation::Match(match_node)) => {
                    for arm in match_node.arms() {
                        for binder in arm.pattern().binder_iter() {
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
        Ok(abstraction_owners)
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
        if let (Some(relation), Some(module)) = (&self.module_sources, binder.id().module())
            && relation.get(&module).copied() != Some(binder.origin().primary_span().source())
        {
            return Err(ValidationError::new(ValidationReason::Registry, Some(node)));
        }
        let type_valid = if allow_scheme {
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
        nominal_parameter_owners: &HashMap<
            crate::types::TypeVariableId,
            crate::types::NominalTypeId,
        >,
        abstraction_owners: &CoreAbstractionOwners,
    ) -> Result<CoreTypeBinders<'program>, ValidationError> {
        let mut definitions = HashMap::new();
        let mut consumed_rows = 0_usize;
        for (index, node) in self.program.nodes.iter().enumerate() {
            let PureExprKind::Computation(PureComputation::TypeAbstraction(abstraction)) =
                &node.kind
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
        nominal_parameter_owners: &HashMap<
            crate::types::TypeVariableId,
            crate::types::NominalTypeId,
        >,
        type_binders: &CoreTypeBinders<'program>,
    ) -> Result<(), ValidationError> {
        for (index, node) in self.program.nodes.iter().enumerate() {
            let id = node_id(self.program.arena, index)?;
            if !matches!(
                &node.kind,
                PureExprKind::Computation(PureComputation::TypeAbstraction(_))
            ) && !self
                .valid_core_type_kind(&node.ty, type_binders)
                .map_err(|error| error.at_node(id))?
            {
                return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
            }
            match &node.kind {
                PureExprKind::Value(value) => self
                    .validate_value(id, node, value)
                    .map_err(|error| error.at_node(id))?,
                PureExprKind::Variable(variable) => {
                    let Some(binder) = self.binders.get(&variable.binder()) else {
                        return Err(ValidationError::new(ValidationReason::Scope, Some(id)));
                    };
                    if !self.same_type_charged(&node.ty, binder.ty())? {
                        return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                    }
                }
                PureExprKind::Computation(computation) => {
                    self.validate_computation(
                        id,
                        node,
                        computation,
                        type_binders,
                        nominal_parameter_owners,
                    )
                    .map_err(|error| error.at_node(id))?;
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
                let Type::Function(actual_domain, actual_codomain) = &node.ty else {
                    return Err(ValidationError::new(ValidationReason::NodeType, Some(id)));
                };
                if !self.same_type_charged(actual_domain, function.parameter().ty())?
                    || !self.same_type_charged(actual_codomain, &body.ty)?
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
        node: &StoredNode,
        computation: &PureComputation,
        type_binders: &CoreTypeBinders<'program>,
        nominal_parameter_owners: &HashMap<
            crate::types::TypeVariableId,
            crate::types::NominalTypeId,
        >,
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
                            initializer.kind,
                            PureExprKind::Value(PureValue::Function(_))
                        ),
                        ty if ty.outer_nominal().is_some() => match ty.outer_nominal() {
                            Some(owner) => {
                                self.guarded_data_root(member.initializer(), owner, &recursive)?
                            }
                            None => false,
                        },
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
                            self.same_kinded_parameters(
                                abstraction.parameters(),
                                parameters.as_ref(),
                            )? && matches!(
                                self.node(abstraction.body())?.kind,
                                PureExprKind::Value(PureValue::Function(_))
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
                let Type::Function(domain, codomain) = &function.ty else {
                    return Err(ValidationError::new(
                        ValidationReason::ApplicationType,
                        Some(id),
                    ));
                };
                if !self.same_type_charged(domain, &argument.ty)?
                    || !self.same_type_charged(codomain, &node.ty)?
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
                    || matches!(scheme_body.as_ref(), Type::Forall(_, _))
                    || !self.valid_core_type_kind(&node.ty, type_binders)?
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
                for ((_, expected_kind), argument) in parameters.iter().zip(application.arguments())
                {
                    let Some(argument_kind) = self.synthesize_monotype_kind(
                        argument,
                        MonotypeVariableKinds::Core(type_binders),
                    )?
                    else {
                        invalid_argument = true;
                        continue;
                    };
                    invalid_argument |= !self.same_kind_charged(expected_kind, &argument_kind)?;
                }
                if parameters.len() != application.arguments().len() || invalid_argument {
                    return Err(ValidationError::new(
                        ValidationReason::TypeOperation,
                        Some(id),
                    ));
                }
                for argument in application.arguments() {
                    self.charge_type_structure(argument)?;
                }
                self.charge_type_work(parameters.len())?;
                let mut replacements = TypeReplacementMap::new();
                replacements
                    .try_reserve(parameters.len())
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?;
                for ((parameter, _), argument) in parameters.iter().zip(application.arguments()) {
                    replacements.insert_replacing(*parameter, argument.clone());
                }
                let instantiated = IterativeTypeOwner::new(substitute_type_variables_with(
                    body,
                    replacements.as_map(),
                    |cells| self.charge_type_work(cells),
                )?);
                if !self.same_type_charged(&node.ty, &instantiated)? {
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
                            for (parameter, _) in operation.parameters() {
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
                                for binder in arm.pattern().binder_iter() {
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
        core::{
            CoreBuilder, PureValue,
            type_ops::{TypeAbstractionNode, TypeApplicationNode},
        },
        elaborate::{Elaborator, check_module, link_modules},
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
                    | PureComputation::Tuple(_),
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
    ) -> HashMap<crate::types::TypeVariableId, crate::types::NominalTypeId> {
        fixture
            .program
            .registry
            .nominal_parameter_entries()
            .flat_map(|(owner, parameters)| {
                parameters
                    .iter()
                    .map(move |parameter| (parameter.id, owner))
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
            .collect_binders()
            .expect("the direct scan validates the same binder metadata");
        assert!(direct_owners.is_empty());
        let direct_work = direct.type_work.get();

        let mut measured =
            Validator::new_modules(&fixture.program, &sources, &fixture.module_sources)
                .expect("the measured relation is canonical");
        let measured_owners = measured
            .collect_binders()
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
                .collect_binders()
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
            .collect_binders()
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
            .collect_binders()
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
            .collect_binders()
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
            .collect_binders()
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
            .collect_binders()
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
            .collect_binders()
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
            .collect_binders()
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

    fn node_type_carriers_mention(node: &StoredNode, sought: crate::types::TypeVariableId) -> bool {
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
                | PureComputation::Tuple(_),
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
        node: &mut StoredNode,
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

    fn origin(source: &SourceFile) -> Origin {
        let range = ByteRange::new(0, 2).expect("ordered range");
        Origin::Source(source.span(range).expect("source span"))
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
                        id: first_nominal,
                        spelling: "Shared".into(),
                        constructors: vec![first_constructor].into_boxed_slice(),
                        origin: range_origin(first_source, 0, 13),
                    },
                    crate::resolved::ResolvedNominalType {
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
    fn core_validation_type_work_capacity_is_exact_and_atomic() {
        const EXPECTED_CAPACITY: usize = CORE_VALIDATION_TYPE_WORK_LIMIT;

        let file = source();
        let program = UnvalidatedProgram {
            registry: Arc::new(crate::resolved::ResolvedRegistry::default()),
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
            arena,
            nodes: vec![StoredNode {
                dialect: DialectId::PURE,
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
            arena,
            nodes: vec![StoredNode {
                dialect: DialectId::PURE,
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
            .collect_binders()
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
            ty: Type::Unit,
            origin: Some(origin.clone()),
            kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
        }];
        for (index, parameter) in parameter_ids.iter().copied().enumerate() {
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
                            vec![type_parameter(parameter)],
                            occurrence,
                        ),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
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
            arena,
            nodes: vec![StoredNode {
                dialect: DialectId::PURE,
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
                    ty: Type::Unit,
                    origin: Some(origin.clone()),
                    kind: PureExprKind::Value(PureValue::Unit(super::super::literal::UnitNode)),
                },
                StoredNode {
                    dialect: DialectId::PURE,
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
                let exact_owners = HashMap::from([(parameter, owner)]);
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
                let short_owners = HashMap::from([(parameter, owner)]);
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
            arena,
            nodes: Vec::new(),
            root: NodeId::new(arena, 0),
        };
        let validator = Validator::new(&program, &[&file]);
        let parameter_owners = HashMap::from([(parameter, owner)]);
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
                    id: pair,
                    spelling: "Pair".into(),
                    constructors: Box::new([]),
                    origin: origin(&file),
                },
                crate::resolved::ResolvedNominalType {
                    id: higher,
                    spelling: "Higher".into(),
                    constructors: Box::new([]),
                    origin: origin(&file),
                },
                crate::resolved::ResolvedNominalType {
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
            arena,
            nodes: Vec::new(),
            root: NodeId::new(arena, 0),
        };
        let validator = Validator::new(&program, &[&file]);
        let parameter_owners =
            HashMap::from([(left, pair), (right, pair), (constructor_parameter, higher)]);
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
            arena,
            nodes: Vec::new(),
            root: NodeId::new(arena, 0),
        };
        let validator = Validator::new(&program, &[&file]);
        let parameter_owners = HashMap::from([(parameter, owner)]);
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
            arena,
            nodes: vec![
                StoredNode {
                    dialect: DialectId::PURE,
                    ty: Type::Bool,
                    origin: Some(node_origin.clone()),
                    kind: PureExprKind::Value(PureValue::Boolean(
                        super::super::literal::BooleanNode::new(false),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    ty: function_type,
                    origin: Some(node_origin.clone()),
                    kind: PureExprKind::Value(PureValue::Function(
                        super::super::function::FunctionNode::new(binder, body),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
                    ty: constructor_type,
                    origin: Some(node_origin.clone()),
                    kind: PureExprKind::Value(PureValue::Constructor(
                        super::super::data::ConstructorNode::new(constructor_id),
                    )),
                },
                StoredNode {
                    dialect: DialectId::PURE,
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
                    id: monomorphic,
                    spelling: "Mono".into(),
                    constructors: vec![mono_nullary, mono_payload].into_boxed_slice(),
                    origin: node_origin.clone(),
                },
                crate::resolved::ResolvedNominalType {
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
                ty: ty.clone(),
                origin: Some(node_origin.clone()),
                kind: PureExprKind::Value(PureValue::Constructor(
                    super::super::data::ConstructorNode::new(*constructor),
                )),
            })
            .collect::<Vec<_>>();
        let program = UnvalidatedProgram {
            registry: Arc::new(registry),
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
                    arena,
                    nodes: vec![
                        StoredNode {
                            dialect: DialectId::PURE,
                            ty: function_type(DEPTH),
                            origin: Some(node_origin.clone()),
                            kind: PureExprKind::Value(PureValue::Unit(
                                super::super::literal::UnitNode,
                            )),
                        },
                        StoredNode {
                            dialect: DialectId::PURE,
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
                    arena,
                    nodes: vec![
                        StoredNode {
                            dialect: DialectId::PURE,
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
                    arena,
                    nodes: vec![
                        StoredNode {
                            dialect: DialectId::PURE,
                            ty: deep,
                            origin: Some(node_origin.clone()),
                            kind: PureExprKind::Value(PureValue::Unit(
                                super::super::literal::UnitNode,
                            )),
                        },
                        StoredNode {
                            dialect: DialectId::PURE,
                            ty: Type::Unit,
                            origin: Some(node_origin.clone()),
                            kind: PureExprKind::Value(PureValue::Unit(
                                super::super::literal::UnitNode,
                            )),
                        },
                        StoredNode {
                            dialect: DialectId::PURE,
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
                    arena,
                    nodes: vec![
                        StoredNode {
                            dialect: DialectId::PURE,
                            ty: deep,
                            origin: Some(node_origin.clone()),
                            kind: PureExprKind::Value(PureValue::Unit(
                                super::super::literal::UnitNode,
                            )),
                        },
                        StoredNode {
                            dialect: DialectId::PURE,
                            ty: Type::Unit,
                            origin: Some(node_origin.clone()),
                            kind: PureExprKind::Value(PureValue::Unit(
                                super::super::literal::UnitNode,
                            )),
                        },
                        StoredNode {
                            dialect: DialectId::PURE,
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
                    arena,
                    nodes: vec![StoredNode {
                        dialect: DialectId::PURE,
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
                    arena,
                    nodes: vec![StoredNode {
                        dialect: DialectId::PURE,
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
        let raw_field = ["replacements", ".0"].concat();
        assert!(!source.contains(&raw_field));
        let raw_insert = [".0", ".insert("].concat();
        let raw_reserve = [".0", ".try_reserve("].concat();
        assert_eq!(source.matches(&raw_insert).count(), 1);
        assert_eq!(source.matches(&raw_reserve).count(), 1);
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
