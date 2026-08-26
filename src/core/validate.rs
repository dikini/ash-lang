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
    resolved::{BinderId, ResolvedConstructor, ResolvedNominalType, ResolvedTypeVariable},
    source::{Origin, SourceFile, SourceId, Span},
    types::{
        ConstructorId, IterativeTypeOwner, TYPE_WORK_LIMIT, Type, discard_type_iteratively,
        same_type, substitute_type_variables_with,
    },
};

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

fn function_value_type_matches(annotation: &Type, domain: &Type, codomain: &Type) -> bool {
    let Type::Function(actual_domain, actual_codomain) = annotation else {
        return false;
    };
    same_type(actual_domain, domain) && same_type(actual_codomain, codomain)
}

fn nominal_application_head_and_arity(ty: &Type) -> Option<(crate::types::NominalTypeId, usize)> {
    let mut arity = 0usize;
    let mut function = ty;
    while let Type::Application(next, argument) = function {
        let _ = argument;
        arity = arity.checked_add(1)?;
        function = next;
    }
    let Type::Nominal(owner) = function else {
        return None;
    };
    Some((*owner, arity))
}

fn constructor_value_type_matches(
    annotation: &Type,
    constructor: &ResolvedConstructor,
    parameters: &[ResolvedTypeVariable],
) -> bool {
    let monotype = if parameters.is_empty() {
        annotation
    } else {
        let Type::Forall(actual_parameters, body) = annotation else {
            return false;
        };
        if actual_parameters.len() != parameters.len()
            || !actual_parameters
                .iter()
                .zip(parameters)
                .all(|(actual, expected)| *actual == expected.id)
        {
            return false;
        }
        body
    };
    let result = if let Some(payload) = constructor.payload.as_ref() {
        let Type::Function(actual_payload, result) = monotype else {
            return false;
        };
        if !same_type(actual_payload, payload) {
            return false;
        }
        result.as_ref()
    } else {
        monotype
    };
    let mut current = result;
    for parameter in parameters.iter().rev() {
        let Type::Application(function, argument) = current else {
            return false;
        };
        if !matches!(argument.as_ref(), Type::Variable(identity) if *identity == parameter.id) {
            return false;
        }
        current = function;
    }
    matches!(current, Type::Nominal(owner) if *owner == constructor.owner)
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
        self.collect_binders()?;
        self.validate_node_types(&nominal_parameter_owners)?;
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
                    || registry.type_variable(parameter.id) != Some(parameter)
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
        Ok(parameter_owners)
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
                    || registry.type_variable(parameter.id) != Some(parameter)
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
            let names = constructor_names.entry(module).or_default();
            if constructor.id.owner() != constructor.owner
                || !nominal_ids.contains(&constructor.owner)
                || constructor_span.source() != source
                || !origin_depth_within_limit(&constructor.origin)
                || !valid_upper_spelling(&constructor.spelling)
                || !constructor_ids.insert(constructor.id)
                || !names.insert(constructor.spelling.as_str())
                || !payload_valid
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
                        Type::Int | Type::Bool | Type::Unit if applied_arguments == 0 => {}
                        Type::Int | Type::Bool | Type::Unit => return Ok(false),
                        Type::Nominal(id) => {
                            let Some(parameters) = self.program.registry.nominal_parameters(*id)
                            else {
                                return Ok(false);
                            };
                            if parameters.len() != applied_arguments {
                                return Ok(false);
                            }
                        }
                        Type::Variable(_) if applied_arguments == 0 => {}
                        Type::Variable(_) => return Ok(false),
                        Type::Inference(_) => return Ok(false),
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
                            work.push(Task::Visit(body, false, depth.saturating_add(1), 0));
                        }
                        Type::Forall(_, _) => return Ok(false),
                        Type::Tuple(elements) if applied_arguments == 0 && elements.len() >= 2 => {
                            work.push(Task::Sequence(elements.iter(), depth.saturating_add(1)));
                        }
                        Type::Tuple(_) => return Ok(false),
                        Type::Function(domain, codomain) if applied_arguments == 0 => {
                            let child_depth = depth.saturating_add(1);
                            work.push(Task::Visit(codomain, false, child_depth, 0));
                            work.push(Task::Visit(domain, false, child_depth, 0));
                        }
                        Type::Function(_, _) => return Ok(false),
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
            Visit(&'a Type, usize, usize),
            Sequence(std::slice::Iter<'a, Type>, usize),
        }
        let mut work = vec![Task::Visit(root, 0, 0)];
        while let Some(task) = work.pop() {
            let Task::Visit(ty, depth, applied_arguments) = task else {
                let Task::Sequence(mut remaining, depth) = task else {
                    unreachable!()
                };
                if let Some(ty) = remaining.next() {
                    work.push(Task::Sequence(remaining, depth));
                    work.push(Task::Visit(ty, depth, 0));
                }
                continue;
            };
            if depth > super::dialect::CORE_PAYLOAD_DEPTH_LIMIT {
                return Ok(false);
            }
            self.charge_type_work(1)?;
            match ty {
                Type::Int | Type::Bool | Type::Unit if applied_arguments == 0 => {}
                Type::Int | Type::Bool | Type::Unit => return Ok(false),
                Type::Nominal(id) => {
                    let Some(parameters) = self.program.registry.nominal_parameters(*id) else {
                        return Ok(false);
                    };
                    if parameters.len() != applied_arguments {
                        return Ok(false);
                    }
                }
                Type::Variable(variable)
                    if applied_arguments == 0 && parameter_owners.get(variable) == Some(&owner) => {
                }
                Type::Variable(_) | Type::Inference(_) | Type::Forall(_, _) => return Ok(false),
                Type::Application(function, argument) => {
                    let child_depth = depth.saturating_add(1);
                    work.push(Task::Visit(argument, child_depth, 0));
                    work.push(Task::Visit(
                        function,
                        depth,
                        applied_arguments.saturating_add(1),
                    ));
                }
                Type::Tuple(elements) if applied_arguments == 0 && elements.len() >= 2 => {
                    work.push(Task::Sequence(elements.iter(), depth.saturating_add(1)));
                }
                Type::Tuple(_) => return Ok(false),
                Type::Function(domain, codomain) if applied_arguments == 0 => {
                    let child_depth = depth.saturating_add(1);
                    work.push(Task::Visit(codomain, child_depth, 0));
                    work.push(Task::Visit(domain, child_depth, 0));
                }
                Type::Function(_, _) => return Ok(false),
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

    fn validate_node_types(
        &self,
        nominal_parameter_owners: &HashMap<
            crate::types::TypeVariableId,
            crate::types::NominalTypeId,
        >,
    ) -> Result<(), ValidationError> {
        let mut type_abstraction_definitions = HashMap::new();
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
                    self.validate_computation(
                        id,
                        node,
                        computation,
                        &mut type_abstraction_definitions,
                        nominal_parameter_owners,
                    )?;
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
                if !function_value_type_matches(&node.ty, function.parameter().ty(), &body.ty) {
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
                if !constructor_value_type_matches(&node.ty, info, parameters) {
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
        type_abstraction_definitions: &mut HashMap<crate::types::TypeVariableId, NodeId>,
        nominal_parameter_owners: &HashMap<
            crate::types::TypeVariableId,
            crate::types::NominalTypeId,
        >,
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
                let mut matrix = CorePatternMatrix(Vec::new());
                let mut coverage_budget = UsefulnessBudget::default();
                for arm in match_node.arms() {
                    self.validate_origin(arm.origin(), id)?;
                    self.validate_pattern(arm.pattern(), &scrutinee.ty, id)?;
                    if !same_type(&self.node(arm.body())?.ty, &node.ty) {
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
                            .module()
                            .is_some_and(|module| relation.get(&module).copied() != Some(source))
                    }) {
                        return Err(ValidationError::new(ValidationReason::Registry, Some(id)));
                    }
                }
                type_abstraction_definitions
                    .try_reserve(abstraction.parameters().len())
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?;
                if abstraction.parameters().is_empty()
                    || !abstraction.parameters().iter().copied().all(|parameter| {
                        type_abstraction_definitions.insert(parameter, id).is_none()
                    })
                    || abstraction
                        .parameters()
                        .iter()
                        .any(|parameter| nominal_parameter_owners.contains_key(parameter))
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
                for argument in application.arguments() {
                    self.charge_type_structure(argument)?;
                }
                self.charge_type_work(parameters.len())?;
                let mut replacements = TypeReplacementMap::new();
                replacements
                    .try_reserve(parameters.len())
                    .map_err(|_| ValidationError::new(ValidationReason::Resource, Some(id)))?;
                for (parameter, argument) in parameters.iter().zip(application.arguments()) {
                    replacements.insert_replacing(*parameter, argument.clone());
                }
                let instantiated = IterativeTypeOwner::new(substitute_type_variables_with(
                    body,
                    replacements.as_map(),
                    |cells| self.charge_type_work(cells),
                )?);
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
                        nominal_application_head_and_arity(expected.as_type())
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

    fn range_origin(source: &SourceFile, start: u32, end: u32) -> Origin {
        Origin::Source(
            source
                .span(ByteRange::new(start, end).expect("ordered range"))
                .expect("source span"),
        )
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
                        origin: range_origin(first_source, 7, 8),
                    }],
                ),
                (
                    second_nominal,
                    vec![crate::resolved::ResolvedTypeVariable {
                        id: second_parameter,
                        spelling: "A".into(),
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
            .charge_type_work(TYPE_WORK_LIMIT - ALLOWANCE)
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
                &mut HashMap::new(),
                &HashMap::new(),
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
            .charge_type_work(TYPE_WORK_LIMIT - 4)
            .expect("test setup leaves argument validation, clone, index, and substitution work");
        application_validator
            .validate_computation(
                application,
                &program.nodes[2],
                match &program.nodes[2].kind {
                    PureExprKind::Computation(computation) => computation,
                    _ => unreachable!("test application computation"),
                },
                &mut HashMap::new(),
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
        const EXPECTED_WORK: usize = ARGUMENT_CELLS * 2 + 2;
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
            .charge_type_work(TYPE_WORK_LIMIT - EXPECTED_WORK)
            .expect("test setup leaves the exact retained-work allowance");
        exact_validator
            .validate_computation(
                application,
                &program.nodes[2],
                computation,
                &mut HashMap::new(),
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
            .charge_type_work(TYPE_WORK_LIMIT - (EXPECTED_WORK - 1))
            .expect("test setup leaves one cell less than the retained work");
        let error = short_validator
            .validate_computation(
                application,
                &program.nodes[2],
                computation,
                &mut HashMap::new(),
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
        const REPLACEMENT_STORAGE: usize = WIDTH * 2;
        const PAYLOAD_WORK: usize = 2;
        const EXACT_WORK: usize = ROOT_TYPE_CELLS + REPLACEMENT_STORAGE + PAYLOAD_WORK;

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
            .charge_type_work(TYPE_WORK_LIMIT - EXACT_WORK)
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
            .charge_type_work(TYPE_WORK_LIMIT - (ROOT_TYPE_CELLS + REPLACEMENT_STORAGE - 1))
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
        let scheme = Type::Forall(vec![parameter].into_boxed_slice(), Box::new(Type::Unit));
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
                            vec![parameter],
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
                            vec![parameter],
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
    fn borrowed_value_type_matching_handles_wide_function_and_constructor_shapes() {
        const WIDTH: usize = 4_096;
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
            origin: node_origin.clone(),
        }];
        let constructor_type = Type::Forall(
            vec![parameter].into_boxed_slice(),
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
            vec![parameter].into_boxed_slice(),
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
            .charge_type_work(TYPE_WORK_LIMIT)
            .expect("test setup reaches the exact validation boundary");

        for id in [function, constructor_node] {
            let node = validator.node(id).expect("test value node");
            let PureExprKind::Value(value) = &node.kind else {
                unreachable!("test node is a value")
            };
            validator
                .validate_value(id, node, value)
                .expect("borrowed value-type validation retains no derived type tree");
        }
        assert_eq!(validator.type_work.get(), TYPE_WORK_LIMIT);

        for id in [malformed_function, malformed_constructor] {
            let node = validator.node(id).expect("malformed test value node");
            let PureExprKind::Value(value) = &node.kind else {
                unreachable!("test node is a value")
            };
            let error = validator
                .validate_value(id, node, value)
                .expect_err("malformed value types remain node-type failures at the budget edge");
            assert_eq!(error.reason(), ValidationReason::NodeType);
            assert_eq!(error.node(), Some(id));
        }
        assert_eq!(validator.type_work.get(), TYPE_WORK_LIMIT);
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
        let parameterized_scheme =
            |body| Type::Forall(vec![parameter].into_boxed_slice(), Box::new(body));
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
                                vec![parameter].into_boxed_slice(),
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
                        &mut HashMap::new(),
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
                        &mut HashMap::new(),
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
                        &mut HashMap::new(),
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
