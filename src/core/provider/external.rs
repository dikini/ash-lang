//! Authenticated, unpublished references to actually imported plain globals.

use super::super::{NodeId, UnvalidatedEffectProgram};
#[cfg(test)]
use super::EffectInstance;
use super::{
    BinderId, DraftStateAssociation, EffectExprKind, EffectOperation, HashMap, HashSet,
    PureComputation, PureExprKind, PureValue, Type, TypeWorkBudget, ValidationError,
    ValidationReason, charge, invalid, node, resource, same_type_with_budget,
};
use crate::types::{
    IterativeTypeOwner, clone_kinded_type_parameters_with_budget, clone_type_with_budget,
    qualify_scheme_row_replacements_with_budget, substitute_type_and_row_variables_with,
};
use crate::{
    module::ModuleId,
    resolved::{ImportedFacts, ProviderExternalFacts, ProviderGlobalFact},
    source::{SourceFile, SourceId},
};

/// Source-only declared method authority. Construction stays at the
/// independently authenticated original family boundary; relocation stays in
/// its exact source-forest reconstruction. Flat IDs alone cannot construct it.
#[derive(Clone, Copy, Debug)]
pub(crate) struct DeclaredLayoutMethod {
    node: NodeId,
    requirement: crate::interface::RequirementId,
    method: crate::interface::MethodId,
    binder: BinderId,
    witness: crate::types::NominalTypeId,
    payload: crate::types::TypeVariableId,
}
impl DeclaredLayoutMethod {
    pub(crate) fn payload(&self) -> crate::types::TypeVariableId {
        self.payload
    }

    pub(crate) fn matches(&self, node: NodeId, method: crate::interface::MethodId) -> bool {
        self.node == node && self.method == method
    }

    fn authenticate_header<F: super::super::dialect::CoreOperationFamily>(
        &self,
        nodes: &[super::super::dialect::StoredNode<F>],
        ordinal: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ()> {
        work.charge(1)?;
        let Some(stored) = nodes.get(ordinal) else {
            return Ok(false);
        };
        if self.node.index().ok() != Some(ordinal)
            || !matches!(
                self.requirement.owner(),
                crate::interface::RequirementOwner::ResourceFamily(_)
            )
            || !F::effect_row(&stored.effects).is_empty()
            || !matches!(F::pure(&stored.kind), Some(PureExprKind::Variable(variable)) if variable.binder() == self.binder)
        {
            return Ok(false);
        }
        let Some(function) = stored.ty.function_view() else {
            return Ok(false);
        };
        let Type::Application(head, payload) = function.value() else {
            return Ok(false);
        };
        if function.effects().is_some()
            || !matches!(&**head, Type::Nominal(witness) if *witness == self.witness)
            || !matches!(&**payload, Type::Variable(payload) if *payload == self.payload)
        {
            return Ok(false);
        }
        same_type_with_budget(function.domain(), &Type::Unit, work)
    }
}

/// Immutable analysis loan from the completed authenticated source projection.
/// Descriptors copied out of this loan have no authority. Borrowing both owners
/// prevents mutation, reallocation or address reuse throughout graph construction.
pub(crate) struct DeclaredLayoutMethods<'a> {
    nodes: &'a [super::super::dialect::StoredNode<super::super::effect::EffectOperationFamily>],
    routes: &'a [super::super::capture::MethodUse],
}
impl DeclaredLayoutMethods<'_> {
    pub(in crate::core) fn authenticates<F: super::super::dialect::CoreOperationFamily>(
        &self,
        nodes: &[super::super::dialect::StoredNode<F>],
        method: &super::super::capture::MethodUse,
        route: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ()> {
        work.charge(1)?;
        if std::any::TypeId::of::<F>()
            != std::any::TypeId::of::<super::super::effect::EffectOperationFamily>()
            || nodes.len() != self.nodes.len()
            || nodes.as_ptr().cast::<()>() != self.nodes.as_ptr().cast::<()>()
        {
            return Ok(false);
        }
        work.charge(1)?;
        if self
            .routes
            .get(route)
            .is_none_or(|original| !std::ptr::eq(original, method))
        {
            return Ok(false);
        }
        let super::super::capture::MethodTarget::DeclaredLayout(declared) = method.target else {
            return Ok(false);
        };
        if !declared.matches(method.node, method.method) {
            return Ok(false);
        }
        let Ok(ordinal) = method.node.index() else {
            return Ok(false);
        };
        declared.authenticate_header(nodes, ordinal, work)
    }
}

pub(crate) struct AuthenticatedProviderExternals<'a> {
    program: &'a UnvalidatedEffectProgram,
    types: HashMap<BinderId, IterativeTypeOwner>,
    captures: HashMap<BinderId, &'a super::super::capture::CaptureValueSummary>,
    staged_captures: HashMap<NodeId, ProviderSourceRelation>,
    source_occurrences: HashMap<NodeId, ProviderSourceOccurrence<'a>>,
    // Exact original source nodes, admitted only from selected canonical
    // dictionary producers and independently reconstructed method metadata.
    native_layout_nodes: HashMap<NodeId, crate::foreign::ForeignLayoutProducer>,
    dictionary_edges: HashMap<NodeId, (BinderId, NodeId)>,
    dictionary_variables: HashSet<NodeId>,
    // Exact original direct method occurrences, distinct from dictionary
    // installation edges. Only the sealed Layout contract is admitted here.
    dictionary_methods: HashMap<NodeId, DeclaredLayoutMethod>,
    dictionary_installers: HashSet<NodeId>,
    imported: &'a ImportedFacts,
    defining: Option<&'a crate::resolved::ProviderDefiningFacts>,
    entry: Option<&'a super::HandlerFragmentEntry<'a>>,
    family: Option<super::ProviderFamilyIdentity>,
}

/// Canonical source inputs retained only after authenticating the actual ABI
/// occurrence, its selections, and the complete original program structure.
struct ProviderSourceOccurrence<'a> {
    checked_evidence: Vec<(
        crate::interface::InterfaceApplication,
        crate::interface::EvidenceSelection,
    )>,
    global: ProviderGlobalFact<'a>,
    arguments: IterativeArguments,
    rows: Vec<crate::types::EffectRow>,
    methods: Vec<(
        crate::interface::RequirementId,
        crate::interface::MethodId,
        super::super::capture::MethodTarget,
    )>,
    adapters: Vec<super::super::capture::MethodAdapter>,
}

/// Exact imported owner provenance after independent catalog reconstruction.
/// The draft arena/catalog and every unanchored dictionary root stay bound to
/// this private proof; ordinary Core validation cannot construct it.
pub(crate) struct AuthenticatedProviderMethodEvidence<'a> {
    arena: super::super::dialect::ArenaId,
    catalog: &'a std::sync::Arc<super::super::dialect::MethodEvidenceCatalog>,
    owners: HashSet<super::super::dialect::MethodEvidenceOwner>,
    roots: Vec<ProviderDictionaryRoot>,
}
pub(crate) struct ProviderDictionaryRoot {
    pub(crate) slot: usize,
    pub(crate) selection_node: crate::interface::EvidenceNodeId,
    pub(crate) implementation: crate::interface::ImplMethodId,
    pub(crate) node: NodeId,
}
impl AuthenticatedProviderMethodEvidence<'_> {
    pub(in crate::core) fn owner(
        &self,
        arena: super::super::dialect::ArenaId,
        catalog: &std::sync::Arc<super::super::dialect::MethodEvidenceCatalog>,
        owner: super::super::dialect::MethodEvidenceOwner,
    ) -> bool {
        self.arena == arena
            && std::sync::Arc::ptr_eq(self.catalog, catalog)
            && self.owners.contains(&owner)
    }
    pub(in crate::core) fn roots(
        &self,
        arena: super::super::dialect::ArenaId,
        catalog: &std::sync::Arc<super::super::dialect::MethodEvidenceCatalog>,
    ) -> Option<&[ProviderDictionaryRoot]> {
        (self.arena == arena && std::sync::Arc::ptr_eq(self.catalog, catalog))
            .then_some(&self.roots)
    }
}

pub(crate) struct AuthenticatedProviderStateAccesses<'a> {
    program: &'a UnvalidatedEffectProgram,
    nodes: HashSet<NodeId>,
}
impl AuthenticatedProviderStateAccesses<'_> {
    pub(crate) fn contains(&self, program: &UnvalidatedEffectProgram, id: NodeId) -> bool {
        std::ptr::eq(self.program, program) && self.nodes.contains(&id)
    }
}

pub(in crate::core) fn authenticate_state_accesses<'a>(
    program: &'a UnvalidatedEffectProgram,
    associations: &[DraftStateAssociation<'_>],
    work: &mut TypeWorkBudget,
) -> Result<AuthenticatedProviderStateAccesses<'a>, ValidationError> {
    super::access::check_state_access_associations(program, associations, work)?;
    let mut nodes = HashSet::new();
    charge(work, program.nodes.len())?;
    for (ordinal, stored) in program.nodes.iter().enumerate() {
        if matches!(
            &stored.kind,
            EffectExprKind::Operation(EffectOperation::ProviderStateAccess(_))
        ) {
            charge(work, 1)?;
            nodes.try_reserve(1).map_err(|_| resource())?;
            nodes.insert(NodeId::new(
                program.arena,
                u32::try_from(ordinal).map_err(|_| resource())?,
            ));
        }
    }
    Ok(AuthenticatedProviderStateAccesses { program, nodes })
}

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(crate) fn authenticate_plain_externals_with_defining<'a>(
    program: &'a UnvalidatedEffectProgram,
    imported: &'a ImportedFacts,
    defining: Option<&'a crate::resolved::ProviderDefiningFacts>,
    sources: &[&SourceFile],
    module_sources: &[(ModuleId, SourceId)],
    canonical: &crate::resolved::ResolvedRegistry,
    associations: &[DraftStateAssociation<'_>],
    work: &mut TypeWorkBudget,
) -> Result<AuthenticatedProviderExternals<'a>, ValidationError> {
    authenticate_plain_externals_context(
        program,
        imported,
        defining,
        sources,
        module_sources,
        canonical,
        associations,
        None,
        work,
    )
}

pub(in crate::core) fn authenticate_handler_externals<'a>(
    entry: &'a super::HandlerFragmentEntry<'a>,
    sources: &[&SourceFile],
    module_sources: &[(ModuleId, SourceId)],
    associations: &[DraftStateAssociation<'_>],
    work: &mut TypeWorkBudget,
) -> Result<AuthenticatedProviderExternals<'a>, ValidationError> {
    authenticate_plain_externals_context(
        &entry.draft.program,
        entry.module.imported_facts(),
        entry.draft.defining_facts.as_deref(),
        sources,
        module_sources,
        &entry.canonical,
        associations,
        Some(entry),
        work,
    )
}

#[expect(
    clippy::too_many_arguments,
    reason = "plain imported facts are authenticated in either ordinary or sealed canonical fragment context"
)]
fn authenticate_plain_externals_context<'a>(
    program: &'a UnvalidatedEffectProgram,
    imported: &'a ImportedFacts,
    defining: Option<&'a crate::resolved::ProviderDefiningFacts>,
    sources: &[&SourceFile],
    module_sources: &[(ModuleId, SourceId)],
    canonical: &crate::resolved::ResolvedRegistry,
    associations: &[DraftStateAssociation<'_>],
    entry: Option<&'a super::HandlerFragmentEntry<'a>>,
    work: &mut TypeWorkBudget,
) -> Result<AuthenticatedProviderExternals<'a>, ValidationError> {
    let facts = ProviderExternalFacts { imported, defining };
    let mut types = HashMap::new();
    let mut captures = HashMap::new();
    let mut origins = HashMap::new();
    let mut source_variables = HashSet::new();
    charge(work, program.nodes.len())?;
    for (ordinal, stored) in program.nodes.iter().enumerate() {
        let EffectExprKind::Pure(PureExprKind::Variable(variable)) = &stored.kind else {
            continue;
        };
        let binder = variable.binder();
        let Some(fact) = facts.global(binder) else {
            continue;
        };
        charge(work, 1)?;
        if let Some(entry) = entry {
            let id = NodeId::new(
                program.arena,
                u32::try_from(ordinal).map_err(|_| resource())?,
            );
            let span = stored
                .origin
                .as_ref()
                .ok_or_else(|| invalid(id))?
                .primary_span();
            let source = entry.imports.get(&span).ok_or_else(|| invalid(id))?;
            if source.global_binder() != Some(binder) {
                return Err(invalid(id));
            }
            require_origin(program, id, &source.origin, work)?;
            charge(work, 1)?;
            source_variables.try_reserve(1).map_err(|_| resource())?;
            if !source_variables.insert(span) {
                return Err(invalid(id));
            }
        }
        if types.contains_key(&binder) {
            continue;
        }
        if !fact.scheme().requirements.is_empty() {
            return Err(invalid(program.root));
        }
        let empty = HashMap::new();
        let mut rows = HashMap::new();
        qualify_scheme_row_replacements_with_budget(
            &fact.scheme().value_type,
            &empty,
            &mut rows,
            true,
            work,
        )
        .map_err(|()| resource())?;
        let body = IterativeTypeOwner::new(if rows.is_empty() {
            clone_type_with_budget(&fact.scheme().value_type, work).map_err(|()| resource())?
        } else {
            substitute_type_and_row_variables_with(
                &fact.scheme().value_type,
                &empty,
                &rows,
                |cells| work.charge(cells),
                || (),
            )
            .map_err(|()| resource())?
            .map_err(|_| invalid(program.root))?
        });
        let scheme = if fact.scheme().type_parameters.is_empty() {
            body
        } else {
            charge(work, 1)?;
            let parameters =
                clone_kinded_type_parameters_with_budget(&fact.scheme().type_parameters, work)
                    .map_err(|()| resource())?;
            IterativeTypeOwner::new(Type::Forall(
                parameters.into_boxed_slice(),
                Box::new(body.into_inner()),
            ))
        };
        charge(work, 3)?;
        origins.try_reserve(1).map_err(|_| resource())?;
        origins.insert(binder, fact.origin());
        types.try_reserve(1).map_err(|_| resource())?;
        captures.try_reserve(1).map_err(|_| resource())?;
        types.insert(binder, scheme);
        captures.insert(binder, fact.capture());
    }
    if let Some(entry) = entry {
        let count = if entry.family_definition().is_some() {
            charge(work, entry.imports.len())?;
            entry
                .imports
                .values()
                .filter(|source| source.global_binder().is_some())
                .count()
        } else {
            entry.imports.len()
        };
        if count != source_variables.len() {
            return Err(invalid(program.root));
        }
    }
    let accesses = authenticate_state_accesses(program, associations, work)?;
    super::super::validate::check_provider_external_structure(
        program,
        sources,
        module_sources,
        canonical,
        &origins,
        &types,
        &accesses,
        None,
        entry,
        entry.map(|entry| entry.fragment_locals.as_slice()),
        None,
        work,
    )?;
    Ok(AuthenticatedProviderExternals {
        program,
        types,
        captures,
        staged_captures: HashMap::new(),
        source_occurrences: HashMap::new(),
        native_layout_nodes: HashMap::new(),
        dictionary_edges: HashMap::new(),
        dictionary_variables: HashSet::new(),
        dictionary_methods: HashMap::new(),
        dictionary_installers: HashSet::new(),
        imported,
        defining,
        entry,
        family: None,
    })
}

impl AuthenticatedProviderExternals<'_> {
    pub(super) fn authenticates_program(&self, program: &UnvalidatedEffectProgram) -> bool {
        std::ptr::eq(self.program, program)
    }
    fn facts(&self) -> ProviderExternalFacts<'_> {
        ProviderExternalFacts {
            imported: self.imported,
            defining: self.defining,
        }
    }

    pub(super) fn contains(&self, binder: BinderId) -> bool {
        self.captures.contains_key(&binder)
    }

    pub(super) fn dictionary_variable(
        &self,
        program: &UnvalidatedEffectProgram,
        id: NodeId,
    ) -> bool {
        std::ptr::eq(self.program, program) && self.dictionary_variables.contains(&id)
    }

    /// The caller preserves the exact original producer through lexical
    /// aliases. A same-typed variable supplies no declared method authority.
    pub(super) fn dictionary_method(
        &self,
        program: &UnvalidatedEffectProgram,
        source: NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        if self.dictionary_methods.is_empty() {
            return Ok(false);
        }
        charge(work, 1)?;
        Ok(std::ptr::eq(self.program, program) && self.dictionary_methods.contains_key(&source))
    }

    /// Invokes only an original, authenticated Layout dictionary formal. Its
    /// canonical pure Unit arrow produces the opaque witness, not a callable.
    /// Installer membership and arbitrary interface methods grant no such fact.
    pub(super) fn dictionary_invocation(
        &self,
        program: &UnvalidatedEffectProgram,
        source: NodeId,
        call: NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        if !self.dictionary_method(program, source, work)? {
            return Err(invalid(call));
        }
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(application))) =
            &node(program, call)?.kind
        else {
            return Err(invalid(call));
        };
        let original = node(program, source)?;
        let function = original.ty.function_view().ok_or_else(|| invalid(source))?;
        if function.effects().is_some()
            || !original.effects.is_empty()
            || !node(program, application.function())?.effects.is_empty()
            || !node(program, call)?.effects.is_empty()
        {
            return Err(invalid(call));
        }
        require_same(
            &node(program, application.function())?.ty,
            &original.ty,
            call,
            work,
        )?;
        require_same(
            &node(program, application.argument())?.ty,
            function.domain(),
            call,
            work,
        )?;
        require_same(&node(program, call)?.ty, function.value(), call, work)
    }

    fn declared_witness_type(
        &self,
        program: &UnvalidatedEffectProgram,
        ty: &Type,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        if self.dictionary_methods.is_empty() {
            return Ok(false);
        }
        charge(work, 1)?;
        if !std::ptr::eq(self.program, program) {
            return Err(invalid(program.root));
        }
        let Type::Application(head, payload) = ty else {
            return Ok(false);
        };
        for declared in self.dictionary_methods.values() {
            charge(work, 1)?;
            if matches!(&**head, Type::Nominal(witness) if *witness == declared.witness)
                && matches!(&**payload, Type::Variable(payload) if *payload == declared.payload)
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) fn dictionary_installation(
        &self,
        program: &UnvalidatedEffectProgram,
        id: NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        charge(work, 1)?;
        Ok(std::ptr::eq(self.program, program) && self.dictionary_installers.contains(&id))
    }

    pub(super) fn dictionary_application(
        &self,
        program: &UnvalidatedEffectProgram,
        call: NodeId,
        binder: BinderId,
        occurrence: NodeId,
    ) -> bool {
        std::ptr::eq(self.program, program)
            && self.dictionary_edges.get(&call) == Some(&(binder, occurrence))
    }

    /// Reconstruct the real local callable from this independently checked
    /// draft and canonical imports. No generated source wrapper is involved.
    pub(super) fn independent_local_call(
        &self,
        program: &UnvalidatedEffectProgram,
        call: NodeId,
        target: NodeId,
        environment: &HashMap<BinderId, usize>,
        facts: &super::Facts,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        if !std::ptr::eq(self.program, program) {
            return Err(invalid(call));
        }
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(application))) =
            &node(program, call)?.kind
        else {
            return Err(invalid(call));
        };
        if !matches!(
            node(program, target)?.kind,
            EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(_)))
        ) {
            return Err(invalid(target));
        }
        let actual = &node(program, application.function())?.ty;
        require_same(actual, &node(program, target)?.ty, call, work)?;
        let function = actual.function_view().ok_or_else(|| invalid(call))?;
        if function
            .effects()
            .is_some_and(|effects| !effects.is_empty())
        {
            return Err(invalid(call));
        }
        if !self.declared_witness_type(program, function.domain(), work)? {
            closed_data_type(program, self.imported, function.domain(), call, work)?;
        }
        if !self.declared_witness_type(program, function.value(), work)? {
            closed_data_type(program, self.imported, function.value(), call, work)?;
        }
        let imports = canonical_capture_imports(self.facts(), work)?;
        charge(work, environment.len())?;
        let mut lexical = Vec::new();
        lexical
            .try_reserve_exact(environment.len())
            .map_err(|_| resource())?;
        lexical.extend(environment.keys().copied());
        let data = independent_flow_data_bindings(program, self, call, environment, facts, work)?;
        let view = if self.source_occurrences.is_empty()
            && self.native_layout_nodes.is_empty()
            && self.dictionary_methods.is_empty()
        {
            None
        } else {
            Some(self.source_capture_view(program, target, work)?)
        };
        let (nodes, target, routes, adapters, instantiations, dictionary_variables) =
            if let Some(view) = &view {
                let target = view
                    .correspondence
                    .get(target.value() as usize)
                    .copied()
                    .flatten()
                    .ok_or_else(|| invalid(target))?;
                (
                    &view.builder.nodes[..],
                    target,
                    &view.routes[..],
                    &view.adapters[..],
                    &view.instantiations[..],
                    &view.dictionary_variables[..],
                )
            } else {
                (
                    &program.nodes[..],
                    target,
                    &[][..],
                    &[][..],
                    &[][..],
                    &[][..],
                )
            };
        let declared = if self.dictionary_methods.is_empty() {
            None
        } else {
            view.as_ref()
                .map(ProviderSourceCaptureView::declared_methods)
        };
        let flow = ProviderLocalFlow {
            nodes,
            target,
            lexical,
            data,
            instantiations,
            dictionary_variables,
            declared: declared.as_ref(),
        };
        let mut summaries = super::super::capture::check_provider_roots_with_methods(
            nodes,
            &flow,
            &imports,
            |kind| match kind {
                EffectExprKind::Operation(op) => Some(op),
                _ => None,
            },
            routes,
            adapters,
            work,
        )
        .map_err(|failure| match failure {
            super::super::capture::Failure::Resource => resource(),
            _ => invalid(call),
        })?;
        let summary = summaries.pop().ok_or_else(|| invalid(call))?;
        if !summaries.is_empty() {
            return Err(invalid(call));
        }
        summary
            .check_provider_independent_typed_call(actual, work)
            .map_err(|failure| match failure {
                super::super::capture::Failure::Resource => resource(),
                _ => invalid(call),
            })
    }

    /// One logical source-analysis graph, rebuilt only from the authenticated
    /// final ABI program and canonical occurrence records. This is not final
    /// validated Core and confers no publication or execution authority.
    fn source_capture_view(
        &self,
        program: &UnvalidatedEffectProgram,
        target: NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<ProviderSourceCaptureView, ValidationError> {
        self.source_capture_view_context(program, target, true, work)
    }

    fn source_capture_view_context(
        &self,
        program: &UnvalidatedEffectProgram,
        target: NodeId,
        callable: bool,
        work: &mut TypeWorkBudget,
    ) -> Result<ProviderSourceCaptureView, ValidationError> {
        if !std::ptr::eq(program, self.program) {
            return Err(invalid(target));
        }
        let mut cuts = HashSet::new();
        charge(work, self.source_occurrences.len())?;
        cuts.try_reserve(self.source_occurrences.len())
            .map_err(|_| resource())?;
        cuts.extend(self.source_occurrences.keys().copied());
        let roots = self
            .entry
            .map_or(std::slice::from_ref(&program.root), |entry| entry.roots());
        let order = super::super::transform::provider_fragment_order(program, roots, &cuts, work)
            .map_err(|failure| capture_transform_failure(failure, target))?;
        let mut patterns = Vec::new();
        if let Some(entry) = self.entry {
            charge(work, entry.draft.clauses.len())?;
            patterns
                .try_reserve_exact(entry.draft.clauses.len())
                .map_err(|_| resource())?;
            patterns.extend(entry.draft.clauses.iter().map(|clause| clause.pattern()));
        }
        let mut states = Vec::new();
        if let Some(entry) = self.entry {
            charge(
                work,
                entry
                    .dictionary_parameters()
                    .len()
                    .checked_add(1)
                    .ok_or_else(resource)?,
            )?;
            states
                .try_reserve_exact(entry.dictionary_parameters().len() + 1)
                .map_err(|_| resource())?;
            states.push(&entry.draft.state);
            states.extend(entry.dictionary_parameters());
        }
        let mut builder = super::super::transform::prepare_provider_fragment_builder_with_catalog(
            program,
            &order,
            std::sync::Arc::clone(&program.method_evidence),
            &states,
            &patterns,
            work,
        )
        .map_err(|failure| capture_transform_failure(failure, target))?;
        let mut correspondence = Vec::new();
        charge(work, program.nodes.len())?;
        correspondence
            .try_reserve_exact(program.nodes.len())
            .map_err(|_| resource())?;
        correspondence.resize(program.nodes.len(), None);
        let mut routes = Vec::new();
        let mut adapters = Vec::new();
        let mut instantiations = Vec::new();
        for original in order {
            charge(work, 1)?;
            super::super::transform::begin_provider_draft_work(&mut builder, work.remaining());
            let result = (|| {
                if let Some(source) = self.source_occurrences.get(&original) {
                    let origin = node(program, original)?
                        .origin
                        .as_ref()
                        .ok_or_else(|| invalid(original))?;
                    let (emitted, actual) = emit_source_occurrence(
                        &mut builder,
                        source.global,
                        &source.arguments.0,
                        &source.rows,
                        origin,
                        original,
                        work,
                    )?;
                    require_same(&actual, &node(program, original)?.ty, original, work)?;
                    charge(work, 1)?;
                    instantiations.try_reserve(1).map_err(|_| resource())?;
                    instantiations.push(emitted);
                    let offset = adapters.len();
                    append_source_adapters(&source.adapters, &mut adapters, work)?;
                    charge(work, source.methods.len())?;
                    routes
                        .try_reserve(source.methods.len())
                        .map_err(|_| resource())?;
                    for (requirement, method, target) in &source.methods {
                        let target = match *target {
                            super::super::capture::MethodTarget::Adapter { value, binder } => {
                                let value = offset.checked_add(value).ok_or_else(resource)?;
                                if adapters
                                    .get(value)
                                    .is_none_or(|producer| producer.binder != binder)
                                {
                                    return Err(invalid(original));
                                }
                                super::super::capture::MethodTarget::Adapter { value, binder }
                            }
                            super::super::capture::MethodTarget::Abstract(requirement) => {
                                super::super::capture::MethodTarget::Abstract(requirement)
                            }
                            super::super::capture::MethodTarget::NativeLayout(producer)
                                if *method == producer.method() =>
                            {
                                super::super::capture::MethodTarget::NativeLayout(producer)
                            }
                            _ => return Err(invalid(original)),
                        };
                        routes.push(super::super::capture::MethodUse {
                            node: emitted,
                            target,
                            method: *method,
                            requirement: Some(*requirement),
                            arguments: 0,
                        });
                    }
                    Ok(emitted)
                } else {
                    super::super::transform::rebuild_provider_draft_node(
                        &mut builder,
                        program,
                        &correspondence,
                        original,
                    )
                    .map_err(|failure| capture_transform_failure(failure, original))
                }
            })();
            super::super::transform::discharge_provider_draft_work(&builder, work)
                .map_err(|_| resource())?;
            let emitted = result?;
            if !self.native_layout_nodes.is_empty() {
                charge(work, 1)?;
                if let Some(producer) = self.native_layout_nodes.get(&original) {
                    charge(work, 1)?;
                    routes.try_reserve(1).map_err(|_| resource())?;
                    routes.push(super::super::capture::MethodUse {
                        node: emitted,
                        target: super::super::capture::MethodTarget::NativeLayout(*producer),
                        method: producer.method(),
                        requirement: None,
                        arguments: 0,
                    });
                }
            }
            if !self.dictionary_methods.is_empty() {
                charge(work, 1)?;
                if let Some(original_method) = self.dictionary_methods.get(&original) {
                    charge(work, 1)?;
                    routes.try_reserve(1).map_err(|_| resource())?;
                    let method = DeclaredLayoutMethod {
                        node: emitted,
                        ..*original_method
                    };
                    routes.push(super::super::capture::MethodUse {
                        node: emitted,
                        target: super::super::capture::MethodTarget::DeclaredLayout(method),
                        method: method.method,
                        requirement: None,
                        arguments: 0,
                    });
                }
            }
            correspondence[original.value() as usize] = Some(emitted);
        }
        let projected = correspondence
            .get(target.value() as usize)
            .copied()
            .flatten()
            .ok_or_else(|| invalid(target))?;
        let projected_node = builder
            .nodes
            .get(projected.value() as usize)
            .ok_or_else(|| invalid(target))?;
        require_same(&node(program, target)?.ty, &projected_node.ty, target, work)?;
        if callable
            && !matches!(
                projected_node.kind,
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(_)))
            )
        {
            return Err(invalid(target));
        }
        let mut dictionary_variables = Vec::new();
        charge(work, self.dictionary_variables.len())?;
        dictionary_variables
            .try_reserve_exact(self.dictionary_variables.len())
            .map_err(|_| resource())?;
        for (index, projected) in correspondence.iter().enumerate() {
            charge(work, 1)?;
            let original =
                NodeId::new(program.arena, u32::try_from(index).map_err(|_| resource())?);
            // Direct declared calls retain their exact Abstract method route.
            // Unselected installer variables remain Unknown in source analysis.
            let direct_method = if self.dictionary_methods.is_empty() {
                false
            } else {
                charge(work, 1)?;
                self.dictionary_methods.contains_key(&original)
            };
            if self.dictionary_variables.contains(&original)
                && !direct_method
                && let Some(projected) = projected
            {
                dictionary_variables.push(*projected);
            }
        }
        let arena = builder
            .provider_node_at_ordinal(projected, 0)
            .map_err(|failure| match failure {
                super::super::BuildError::TypeWorkExceeded => resource(),
                _ => invalid(target),
            })?
            .arena();
        let view = ProviderSourceCaptureView {
            arena,
            builder,
            correspondence,
            routes,
            adapters,
            instantiations,
            dictionary_variables,
        };
        #[cfg(test)]
        if !self.dictionary_methods.is_empty() {
            check_declared_layout_view_for_test(&view);
        }
        Ok(view)
    }

    pub(in crate::core) fn conditional_handler_capture(
        &self,
        entry: &super::HandlerFragmentEntry<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<super::super::capture::ConditionalCaptureGraph, ValidationError> {
        if !std::ptr::eq(self.program, &entry.draft.program)
            || self.entry.is_none_or(|actual| !std::ptr::eq(actual, entry))
        {
            return Err(invalid(entry.draft.program.root));
        }
        let imports = canonical_capture_imports(self.facts(), work)?;
        let view = if self.source_occurrences.is_empty()
            && self.native_layout_nodes.is_empty()
            && self.dictionary_methods.is_empty()
        {
            None
        } else {
            Some(self.source_capture_view_context(self.program, self.program.root, false, work)?)
        };
        let mut identity = Vec::new();
        let (nodes, arena, correspondence, routes, adapters, instantiations, dictionary_variables) =
            if let Some(view) = &view {
                (
                    &view.builder.nodes[..],
                    view.arena,
                    &view.correspondence[..],
                    &view.routes[..],
                    &view.adapters[..],
                    &view.instantiations[..],
                    &view.dictionary_variables[..],
                )
            } else {
                charge(work, self.program.nodes.len())?;
                identity
                    .try_reserve_exact(self.program.nodes.len())
                    .map_err(|_| resource())?;
                for ordinal in 0..self.program.nodes.len() {
                    identity.push(Some(NodeId::new(
                        self.program.arena,
                        u32::try_from(ordinal).map_err(|_| resource())?,
                    )));
                }
                (
                    &self.program.nodes[..],
                    self.program.arena,
                    &identity[..],
                    &[][..],
                    &[][..],
                    &[][..],
                    &[][..],
                )
            };
        let declared = if self.dictionary_methods.is_empty() {
            None
        } else {
            view.as_ref()
                .map(ProviderSourceCaptureView::declared_methods)
        };
        super::super::capture::reconstruct_conditional_handler_capture(
            &entry.handler_graph(),
            nodes,
            arena,
            correspondence,
            &imports,
            routes,
            adapters,
            instantiations,
            dictionary_variables,
            declared.as_ref(),
            work,
        )
        .map_err(|failure| match failure {
            super::super::capture::Failure::Resource => resource(),
            _ => invalid(self.program.root),
        })
    }

    pub(super) fn independent_call(
        &self,
        program: &UnvalidatedEffectProgram,
        call: NodeId,
        binder: BinderId,
        occurrence: NodeId,
        allow_owned_scopes: bool,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        if !std::ptr::eq(self.program, program) {
            return Err(invalid(call));
        }
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(application))) =
            &node(program, call)?.kind
        else {
            return Err(invalid(call));
        };
        closed_data_type(
            program,
            self.imported,
            &node(program, application.argument())?.ty,
            call,
            work,
        )?;
        closed_data_type(program, self.imported, &node(program, call)?.ty, call, work)?;
        if let Some(capture) = self.staged_captures.get(&occurrence) {
            capture
                .check(&node(program, occurrence)?.ty, allow_owned_scopes, work)
                .map_err(|failure| match failure {
                    super::super::capture::Failure::Resource => resource(),
                    _ => invalid(call),
                })?;
            return Ok(());
        }
        let scheme = self.types.get(&binder).ok_or_else(|| invalid(call))?;
        let mut metadata = Vec::new();
        match (&**scheme, &node(program, occurrence)?.kind) {
            (
                Type::Forall(parameters, _),
                EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
                    applied,
                ))),
            ) => {
                if !matches!(&node(program, applied.function())?.kind, EffectExprKind::Pure(PureExprKind::Variable(variable)) if variable.binder() == binder)
                {
                    return Err(invalid(call));
                }
                charge(work, parameters.len())?;
                metadata
                    .try_reserve(parameters.len())
                    .map_err(|_| resource())?;
                let mut types = applied.arguments().iter();
                let mut rows = applied.row_arguments().iter();
                for (parameter, kind) in parameters {
                    match kind {
                        crate::types::Kind::Type => closed_data_type(
                            program,
                            self.imported,
                            types.next().ok_or_else(|| invalid(call))?,
                            call,
                            work,
                        )?,
                        crate::types::Kind::EffectRow => {
                            if !rows.next().ok_or_else(|| invalid(call))?.is_empty() {
                                return Err(invalid(call));
                            }
                        }
                        _ => return Err(invalid(call)),
                    }
                    metadata.push(*parameter);
                }
                if types.next().is_some() || rows.next().is_some() {
                    return Err(invalid(call));
                }
            }
            (Type::Forall(_, _), _) => return Err(invalid(call)),
            (_, EffectExprKind::Pure(PureExprKind::Variable(variable)))
                if variable.binder() == binder => {}
            _ => return Err(invalid(call)),
        }
        let fact = self.facts().global(binder).ok_or_else(|| invalid(call))?;
        let arguments = match &node(program, occurrence)?.kind {
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
                applied,
            ))) => applied.arguments(),
            _ => &[],
        };
        let row_arguments = match &node(program, occurrence)?.kind {
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
                applied,
            ))) => applied.row_arguments(),
            _ => &[],
        };
        let capture = source_capture_relation(
            program,
            fact,
            arguments,
            row_arguments,
            &[],
            &[],
            self.facts(),
            work,
        )?;
        capture
            .check(&node(program, occurrence)?.ty, allow_owned_scopes, work)
            .map_err(|failure| match failure {
                super::super::capture::Failure::Resource => resource(),
                _ => invalid(call),
            })
    }
}

struct ProviderSourceCaptureView {
    arena: super::super::dialect::ArenaId,
    builder: super::super::CoreBuilder<super::super::effect::EffectOperationFamily>,
    correspondence: Vec<Option<NodeId>>,
    routes: Vec<super::super::capture::MethodUse>,
    adapters: Vec<super::super::capture::MethodAdapter>,
    instantiations: Vec<NodeId>,
    dictionary_variables: Vec<NodeId>,
}
impl ProviderSourceCaptureView {
    fn declared_methods(&self) -> DeclaredLayoutMethods<'_> {
        DeclaredLayoutMethods {
            nodes: &self.builder.nodes,
            routes: &self.routes,
        }
    }
}
#[cfg(test)]
std::thread_local! {
    static CHECK_DECLARED_LAYOUT: std::cell::Cell<(bool, usize)> = const { std::cell::Cell::new((false, 0)) };
}

#[cfg(test)]
pub(crate) fn with_declared_layout_checks_for_test<R>(run: impl FnOnce() -> R) -> R {
    struct Restore((bool, usize));
    impl Drop for Restore {
        fn drop(&mut self) {
            CHECK_DECLARED_LAYOUT.with(|state| state.set(self.0));
        }
    }
    let restore = Restore(CHECK_DECLARED_LAYOUT.with(|state| state.replace((true, 0))));
    let result = run();
    assert!(
        CHECK_DECLARED_LAYOUT.with(|state| state.get().1) > 0,
        "the genuine source fixture must reach the authenticated declared Layout loan"
    );
    drop(restore);
    result
}

#[cfg(test)]
fn check_declared_layout_view_for_test(view: &ProviderSourceCaptureView) {
    if !CHECK_DECLARED_LAYOUT.with(|state| state.get().0) {
        return;
    }
    let (route, method) = view
        .routes
        .iter()
        .enumerate()
        .find(|(_, method)| {
            matches!(
                method.target,
                super::super::capture::MethodTarget::DeclaredLayout(_)
            )
        })
        .expect("the real source projection must retain a declared method");
    let loan = view.declared_methods();
    let nodes = &view.builder.nodes;
    let mut measured = TypeWorkBudget::unbounded();
    assert!(
        loan.authenticates(nodes, method, route, &mut measured)
            .unwrap()
    );
    let cost = measured.used();
    assert!(cost > 0);
    for prefix in [0, 17] {
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert!(
            loan.authenticates(nodes, method, route, &mut short)
                .is_err()
        );
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            assert!(
                loan.authenticates(nodes, method, route, &mut exact)
                    .unwrap()
            );
            assert_eq!(exact.used(), prefix + cost);
        }
    }
    let copied = nodes
        .iter()
        .map(|node| super::super::dialect::StoredNode::<
            super::super::effect::EffectOperationFamily,
        > {
            dialect: node.dialect,
            ty: node.ty.clone(),
            effects: node.effects.clone(),
            origin: node.origin.clone(),
            kind: node.kind.clone(),
        })
        .collect::<Vec<_>>();
    assert!(
        !loan
            .authenticates(&copied, method, route, &mut TypeWorkBudget::unbounded())
            .unwrap(),
        "a same-shaped copied slice cannot reuse a source loan"
    );
    let stolen = super::super::capture::MethodUse {
        node: method.node,
        target: method.target,
        method: method.method,
        requirement: method.requirement,
        arguments: method.arguments,
    };
    assert!(
        !loan
            .authenticates(nodes, &stolen, route, &mut TypeWorkBudget::unbounded())
            .unwrap(),
        "a copied descriptor is not the borrowed original route"
    );
    assert!(
        !loan
            .authenticates(
                nodes,
                method,
                view.routes.len(),
                &mut TypeWorkBudget::unbounded()
            )
            .unwrap()
    );
    let super::super::capture::MethodTarget::DeclaredLayout(descriptor) = method.target else {
        unreachable!();
    };
    let ordinal = method.node.index().unwrap();
    assert!(
        !descriptor
            .authenticate_header(nodes, nodes.len(), &mut TypeWorkBudget::unbounded())
            .unwrap()
    );
    let other = nodes
        .iter()
        .find_map(|stored| match &stored.kind {
            EffectExprKind::Pure(PureExprKind::Variable(variable))
                if variable.binder() != descriptor.binder =>
            {
                Some(variable.binder())
            }
            _ => None,
        })
        .expect("the genuine family forest has a distinct real binder");
    let mut changed = copied;
    changed[ordinal].kind = EffectExprKind::Pure(PureExprKind::Variable(
        super::super::variable::VariableNode::new(other),
    ));
    assert!(
        !descriptor
            .authenticate_header(&changed, ordinal, &mut TypeWorkBudget::unbounded())
            .unwrap(),
        "the canonical declared method still requires its exact formal binder"
    );
    changed[ordinal].kind = nodes[ordinal].kind.clone();
    changed[ordinal].ty = Type::Unit;
    assert!(
        !descriptor
            .authenticate_header(&changed, ordinal, &mut TypeWorkBudget::unbounded())
            .unwrap(),
        "the actual pure Unit to canonical Witness header is mandatory"
    );
    CHECK_DECLARED_LAYOUT.with(|state| {
        let (enabled, count) = state.get();
        state.set((enabled, count + 1));
    });
}

fn capture_transform_failure(
    failure: super::super::transform::TransformError,
    at: NodeId,
) -> ValidationError {
    match failure {
        super::super::transform::TransformError::Build(
            super::super::BuildError::TypeWorkExceeded,
        ) => resource(),
        _ => invalid(at),
    }
}
fn append_source_adapters(
    source: &[super::super::capture::MethodAdapter],
    output: &mut Vec<super::super::capture::MethodAdapter>,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let offset = output.len();
    charge(work, source.len())?;
    output.try_reserve(source.len()).map_err(|_| resource())?;
    for adapter in source {
        let mut copied = super::super::capture::MethodAdapter {
            binder: adapter.binder,
            head_arguments: Vec::new(),
            method_parameters: adapter.method_parameters,
            prerequisites: Vec::new(),
            source: adapter.source,
        };
        charge(
            work,
            adapter.head_arguments.len() + adapter.prerequisites.len(),
        )?;
        copied
            .head_arguments
            .try_reserve_exact(adapter.head_arguments.len())
            .map_err(|_| resource())?;
        for argument in &adapter.head_arguments {
            copied
                .head_arguments
                .push(clone_type_with_budget(argument, work).map_err(|_| resource())?);
        }
        copied
            .prerequisites
            .try_reserve_exact(adapter.prerequisites.len())
            .map_err(|_| resource())?;
        for (requirement, method, target) in &adapter.prerequisites {
            let target = match *target {
                super::super::capture::MethodTarget::Adapter { value, binder } => {
                    super::super::capture::MethodTarget::Adapter {
                        value: offset.checked_add(value).ok_or_else(resource)?,
                        binder,
                    }
                }
                other => other,
            };
            copied.prerequisites.push((*requirement, *method, target));
        }
        output.push(copied);
    }
    Ok(())
}

/// Constructed only by the authenticated actual-call boundary after proving
/// real flow values and canonical parameter/pattern storage types.
pub(in crate::core) struct ProviderLocalFlow<'a> {
    nodes: &'a [super::super::dialect::StoredNode<super::super::effect::EffectOperationFamily>],
    target: NodeId,
    lexical: Vec<BinderId>,
    data: Vec<BinderId>,
    instantiations: &'a [NodeId],
    dictionary_variables: &'a [NodeId],
    declared: Option<&'a DeclaredLayoutMethods<'a>>,
}
// Actual target, available lexical binders, proven independent data binders,
// canonical source-instantiation roots, and unproved raw dictionary roots.
type ProviderLocalFlowInputs<'a> = (
    NodeId,
    &'a [BinderId],
    &'a [BinderId],
    &'a [NodeId],
    &'a [NodeId],
    Option<&'a DeclaredLayoutMethods<'a>>,
);

impl ProviderLocalFlow<'_> {
    pub(in crate::core) fn inputs(
        &self,
        nodes: &[super::super::dialect::StoredNode<super::super::effect::EffectOperationFamily>],
    ) -> Option<ProviderLocalFlowInputs<'_>> {
        (std::ptr::eq(self.nodes, nodes)).then_some((
            self.target,
            &self.lexical,
            &self.data,
            self.instantiations,
            self.dictionary_variables,
            self.declared,
        ))
    }
}

fn independent_flow_data_bindings(
    program: &UnvalidatedEffectProgram,
    externals: &AuthenticatedProviderExternals<'_>,
    call: NodeId,
    environment: &HashMap<BinderId, usize>,
    facts: &super::Facts,
    work: &mut TypeWorkBudget,
) -> Result<Vec<BinderId>, ValidationError> {
    let mut data = Vec::new();
    let retain = |binder: &super::super::TypedBinder,
                  data: &mut Vec<BinderId>,
                  work: &mut TypeWorkBudget| {
        charge(work, 1)?;
        if let Some(value) = environment.get(&binder.id())
            && facts.independent_data(*value, work)?
        {
            // An unrelated ambient owner may be present in the flow. It
            // supplies no data seed; a real capture still encounters its
            // unresolved slot in the strict typed-call query.
            if !externals.declared_witness_type(program, binder.ty(), work)? {
                match closed_data_type(program, externals.imported, binder.ty(), call, work) {
                    Ok(()) => {}
                    Err(failure) if failure.reason() == ValidationReason::Resource => {
                        return Err(failure);
                    }
                    Err(_) => return Ok(()),
                }
            }
            charge(work, 1)?;
            data.try_reserve(1).map_err(|_| resource())?;
            data.push(binder.id());
        }
        Ok(())
    };
    let mut patterns = Vec::new();
    charge(work, program.nodes.len())?;
    for stored in &program.nodes {
        match &stored.kind {
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding)))
                if !externals.dictionary_methods.is_empty() =>
            {
                retain(binding.binder(), &mut data, work)?;
            }
            EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) => {
                retain(function.parameter(), &mut data, work)?
            }
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(matching))) => {
                charge(work, matching.arms().len())?;
                patterns
                    .try_reserve(matching.arms().len())
                    .map_err(|_| resource())?;
                patterns.extend(matching.arms().iter().map(|arm| arm.pattern()));
            }
            _ => {}
        }
    }
    while let Some(pattern) = patterns.pop() {
        charge(work, 1)?;
        match &pattern.kind {
            super::super::data::CorePatternKind::Binder(binder) => retain(binder, &mut data, work)?,
            super::super::data::CorePatternKind::Tuple(elements) => {
                charge(work, elements.len())?;
                patterns
                    .try_reserve(elements.len())
                    .map_err(|_| resource())?;
                patterns.extend(elements);
            }
            super::super::data::CorePatternKind::Constructor {
                payload: Some(payload),
                ..
            } => {
                charge(work, 1)?;
                patterns.try_reserve(1).map_err(|_| resource())?;
                patterns.push(payload);
            }
            _ => {}
        }
    }
    Ok(data)
}

/// Storage independence follows every payload of each exact instantiated
/// canonical data relation. Source access and canonical storage authority are
/// separate: opaque Data without retained payload facts remains unsupported.
fn closed_data_type(
    program: &UnvalidatedEffectProgram,
    imported: &ImportedFacts,
    ty: &Type,
    call: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let mut pending: Vec<IterativeTypeOwner> = Vec::new();
    let mut visited: Vec<IterativeTypeOwner> = Vec::new();
    charge(work, 1)?;
    pending.try_reserve(1).map_err(|_| resource())?;
    pending.push(IterativeTypeOwner::new(
        clone_type_with_budget(ty, work).map_err(|()| resource())?,
    ));
    while let Some(ty) = pending.pop() {
        charge(work, 1)?;
        match &*ty {
            Type::Bytes | Type::String | Type::Int | Type::Bool | Type::Unit => {}
            Type::Tuple(elements) => {
                charge(work, elements.len())?;
                pending
                    .try_reserve(elements.len())
                    .map_err(|_| resource())?;
                for element in elements {
                    pending.push(IterativeTypeOwner::new(
                        clone_type_with_budget(element, work).map_err(|()| resource())?,
                    ));
                }
            }
            Type::Nominal(_) | Type::Application(_, _) => {
                let mut head = &*ty;
                let mut arguments = Vec::new();
                while let Type::Application(function, argument) = head {
                    charge(work, 1)?;
                    arguments.try_reserve(1).map_err(|_| resource())?;
                    arguments.push(argument.as_ref());
                    head = function;
                }
                let Type::Nominal(id) = head else {
                    return Err(invalid(call));
                };
                if program.registry.foreign_state(*id).is_some()
                    || crate::resolved::ResourceApi::for_module(id.module())
                        .is_some_and(|api| api.handle() == *id)
                {
                    return Err(invalid(call));
                }
                arguments.reverse();
                let fact = imported
                    .canonical_nominal_fact(*id)
                    .ok_or_else(|| invalid(call))?;
                if fact.parameter_count != arguments.len()
                    || fact.parameters.len() != arguments.len()
                {
                    return Err(invalid(call));
                }
                let mut replacements = ExternalTypes(HashMap::new());
                charge(work, arguments.len())?;
                replacements
                    .0
                    .try_reserve(arguments.len())
                    .map_err(|_| resource())?;
                // Check actual arguments even if an exact recursive shape has
                // already been scheduled: phantom/function/owner transport is
                // not authorized by a safe nominal head.
                for (parameter, argument) in fact.parameters.iter().zip(&arguments) {
                    if !matches!(parameter.kind, crate::types::Kind::Type) {
                        return Err(invalid(call));
                    }
                    if let Some(displaced) = replacements.0.insert(
                        parameter.id,
                        clone_type_with_budget(argument, work).map_err(|()| resource())?,
                    ) {
                        drop(IterativeTypeOwner::new(displaced));
                        return Err(invalid(call));
                    }
                }
                charge(work, visited.len())?;
                let mut repeated = false;
                for previous in &visited {
                    if same_type_with_budget(previous, &ty, work).map_err(|()| resource())? {
                        repeated = true;
                        break;
                    }
                }
                if !repeated {
                    charge(work, 1)?;
                    visited.try_reserve(1).map_err(|_| resource())?;
                    visited.push(IterativeTypeOwner::new(
                        clone_type_with_budget(&ty, work).map_err(|()| resource())?,
                    ));
                    match fact.declaration_kind {
                        crate::resolved::ResolvedNominalDeclarationKind::Data => {
                            // Hidden source constructors are not empty storage.
                            if fact.constructor_count != fact.constructors.len() {
                                return Err(invalid(call));
                            }
                            charge(work, fact.constructors.len())?;
                            pending
                                .try_reserve(fact.constructors.len())
                                .map_err(|_| resource())?;
                            for (index, id) in fact.constructors.iter().enumerate() {
                                if id.owner() != fact.id || id.constructor() as usize != index {
                                    return Err(invalid(call));
                                }
                                let constructor =
                                    imported.constructor(*id).ok_or_else(|| invalid(call))?;
                                if let Some(payload) = &constructor.payload {
                                    pending.push(substitute(
                                        payload,
                                        &replacements,
                                        &HashMap::new(),
                                        call,
                                        work,
                                    )?);
                                }
                            }
                        }
                        crate::resolved::ResolvedNominalDeclarationKind::Newtype => {
                            charge(work, 1)?;
                            pending.try_reserve(1).map_err(|_| resource())?;
                            pending.push(substitute(
                                fact.representation.ok_or_else(|| invalid(call))?,
                                &replacements,
                                &HashMap::new(),
                                call,
                                work,
                            )?);
                        }
                    }
                }
                // LIFO traversal checks introduced actual arguments before
                // expanding recursive payloads, including repeated shapes.
                charge(work, arguments.len())?;
                pending
                    .try_reserve(arguments.len())
                    .map_err(|_| resource())?;
                for argument in arguments {
                    pending.push(IterativeTypeOwner::new(
                        clone_type_with_budget(argument, work).map_err(|()| resource())?,
                    ));
                }
            }
            _ => return Err(invalid(call)),
        }
    }
    Ok(())
}

#[cfg(test)]
pub(crate) enum ExternalMutation {
    Binder(BinderId),
    Type,
    Kind,
    Row,
}

#[cfg(test)]
pub(crate) fn mutate_external_for_test(
    program: &mut UnvalidatedEffectProgram,
    binder: BinderId,
    mutation: ExternalMutation,
) {
    let stored = program.nodes.iter_mut().find(|stored| matches!(&stored.kind, EffectExprKind::Pure(PureExprKind::Variable(variable)) if variable.binder() == binder)).unwrap();
    match mutation {
        ExternalMutation::Binder(binder) => {
            stored.kind = EffectExprKind::Pure(PureExprKind::Variable(
                super::super::variable::VariableNode::new(binder),
            ))
        }
        ExternalMutation::Type => {
            crate::types::discard_type_iteratively(std::mem::replace(&mut stored.ty, Type::Int))
        }
        ExternalMutation::Kind => {
            let Type::Forall(parameters, _) = &mut stored.ty else {
                panic!("generic external")
            };
            parameters[0].1 = crate::types::Kind::EffectRow;
        }
        ExternalMutation::Row => {
            let Type::Forall(_, body) = &mut stored.ty else {
                panic!("generic external")
            };
            let Type::Function(input, output) = body.as_mut() else {
                panic!("pure arrow")
            };
            let input = std::mem::replace(input, Box::new(Type::Unit));
            let output = std::mem::replace(output, Box::new(Type::Unit));
            let effect = program.registry.foreign_modules().next().unwrap().effects[0];
            **body = Type::EffectfulFunction(
                input,
                Box::new(crate::types::ComputationType::new(
                    *output,
                    crate::types::EffectRow::closed(
                        vec![EffectInstance::new(effect, Box::new([]))].into_boxed_slice(),
                    ),
                )),
            );
        }
    }
}

#[cfg(test)]
pub(crate) fn introduce_external_for_test(
    program: &mut UnvalidatedEffectProgram,
    binder: BinderId,
    scheme: &crate::interface::ConstrainedScheme,
) {
    let stored = program
        .nodes
        .iter_mut()
        .find(|stored| {
            matches!(
                &stored.kind,
                EffectExprKind::Pure(PureExprKind::Variable(_))
            )
        })
        .unwrap();
    let ty = if scheme.type_parameters.is_empty() {
        scheme.value_type.clone()
    } else {
        Type::Forall(
            scheme.type_parameters.clone(),
            Box::new(scheme.value_type.clone()),
        )
    };
    crate::types::discard_type_iteratively(std::mem::replace(&mut stored.ty, ty));
    stored.kind = EffectExprKind::Pure(PureExprKind::Variable(
        super::super::variable::VariableNode::new(binder),
    ));
}

#[cfg(test)]
pub(crate) fn replace_external_registry_for_test(
    program: &mut UnvalidatedEffectProgram,
    registry: std::sync::Arc<crate::resolved::ResolvedRegistry>,
) {
    program.registry = registry;
}

/// Exact checked source occurrence whose final Core chain remains unpublished.
pub(crate) struct ProviderExternalOccurrence<'a> {
    pub(crate) root: NodeId,
    pub(crate) source: &'a crate::resolved::ResolvedOccurrence,
    pub(crate) arguments: &'a [Type],
    pub(crate) row_arguments: &'a [crate::types::EffectRow],
}

struct ExternalTypes(HashMap<crate::types::TypeVariableId, Type>);
impl ExternalTypes {
    fn insert_discarding_replaced(&mut self, parameter: crate::types::TypeVariableId, ty: Type) {
        if let Some(displaced) = self.0.insert(parameter, ty) {
            crate::types::discard_type_iteratively(displaced);
        }
    }
}

impl Drop for ExternalTypes {
    fn drop(&mut self) {
        for ty in self.0.drain().map(|(_, ty)| ty) {
            crate::types::discard_type_iteratively(ty);
        }
    }
}
fn substitutions(
    parameters: &[(crate::types::TypeVariableId, crate::types::Kind)],
    arguments: &[Type],
    rows: &[crate::types::EffectRow],
    at: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<
    (
        ExternalTypes,
        HashMap<crate::types::TypeVariableId, crate::types::EffectRow>,
    ),
    ValidationError,
> {
    let mut types = ExternalTypes(HashMap::new());
    let mut row_substitutions = HashMap::new();
    let mut arguments = arguments.iter();
    let mut rows = rows.iter();
    charge(work, parameters.len())?;
    types
        .0
        .try_reserve(parameters.len())
        .map_err(|_| resource())?;
    row_substitutions
        .try_reserve(parameters.len())
        .map_err(|_| resource())?;
    for (parameter, kind) in parameters {
        if matches!(kind, crate::types::Kind::EffectRow) {
            row_substitutions.insert(
                *parameter,
                crate::types::clone_effect_row_with_budget(
                    rows.next().ok_or_else(|| invalid(at))?,
                    work,
                )
                .map_err(|()| resource())?,
            );
        } else {
            if !matches!(kind, crate::types::Kind::Type) {
                return Err(invalid(at));
            }
            types.insert_discarding_replaced(
                *parameter,
                clone_type_with_budget(arguments.next().ok_or_else(|| invalid(at))?, work)
                    .map_err(|()| resource())?,
            );
        }
    }
    if arguments.next().is_some() || rows.next().is_some() {
        return Err(invalid(at));
    }
    Ok((types, row_substitutions))
}
fn substitute(
    source: &Type,
    types: &ExternalTypes,
    rows: &HashMap<crate::types::TypeVariableId, crate::types::EffectRow>,
    at: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<IterativeTypeOwner, ValidationError> {
    Ok(IterativeTypeOwner::new(
        substitute_type_and_row_variables_with(
            source,
            &types.0,
            rows,
            |cells| work.charge(cells),
            || (),
        )
        .map_err(|()| resource())?
        .map_err(|_| invalid(at))?,
    ))
}
fn substitute_argument(
    source: &crate::types::KindedArgument,
    types: &ExternalTypes,
    rows: &HashMap<crate::types::TypeVariableId, crate::types::EffectRow>,
    at: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<crate::types::IterativeArgumentOwner, ValidationError> {
    let value = crate::types::substitute_kinded_argument_with(source, &types.0, rows, |cells| {
        work.charge(cells)
    })
    .map_err(|()| resource())?
    .map_err(|_| invalid(at))?;
    Ok(crate::types::IterativeArgumentOwner::new(value))
}

fn require_same_argument(
    left: &crate::types::KindedArgument,
    right: &crate::types::KindedArgument,
    at: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    if crate::types::same_kinded_argument_with_budget(left, right, work).map_err(|()| resource())? {
        Ok(())
    } else {
        Err(invalid(at))
    }
}

fn require_same(
    left: &Type,
    right: &Type,
    at: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    if !same_type_with_budget(left, right, work).map_err(|()| resource())? {
        return Err(invalid(at));
    }
    Ok(())
}
fn require_origin(
    program: &UnvalidatedEffectProgram,
    id: NodeId,
    source: &crate::source::Origin,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    if !crate::resolved::same_origin_with_budget(
        node(program, id)?
            .origin
            .as_ref()
            .ok_or_else(|| invalid(id))?,
        source,
        work,
    )
    .map_err(|()| resource())?
    {
        return Err(invalid(id));
    }
    Ok(())
}

/// Independently reconstruct the final dictionary ABI from canonical checked facts.
fn canonical_scheme(
    scheme: &crate::interface::ConstrainedScheme,
    facts: ProviderExternalFacts<'_>,
    at: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<IterativeTypeOwner, ValidationError> {
    let mut rows = HashMap::new();
    qualify_scheme_row_replacements_with_budget(
        &scheme.value_type,
        &HashMap::new(),
        &mut rows,
        true,
        work,
    )
    .map_err(|()| resource())?;
    let mut body = substitute(
        &scheme.value_type,
        &ExternalTypes(HashMap::new()),
        &rows,
        at,
        work,
    )?;
    for requirement in scheme.requirements.iter().rev() {
        let interface = facts
            .interface(requirement.interface(), work)
            .map_err(|()| resource())?
            .ok_or_else(|| invalid(at))?;
        if requirement.arguments().len() != interface.parameters.len() {
            return Err(invalid(at));
        }
        for method in interface.methods.iter().rev() {
            let mut replacements = ExternalTypes(HashMap::new());
            charge(work, interface.parameters.len())?;
            replacements
                .0
                .try_reserve(interface.parameters.len())
                .map_err(|_| resource())?;
            let mut method_rows = HashMap::new();
            charge(work, rows.len() + interface.parameters.len())?;
            method_rows
                .try_reserve(rows.len() + interface.parameters.len())
                .map_err(|_| resource())?;
            for (variable, row) in &rows {
                method_rows.insert(
                    *variable,
                    crate::types::clone_effect_row_with_budget(row, work)
                        .map_err(|()| resource())?,
                );
            }
            for (parameter, argument) in interface.parameters.iter().zip(requirement.arguments()) {
                match (&parameter.kind, argument) {
                    (crate::types::Kind::EffectRow, crate::types::KindedArgument::RowArg(row)) => {
                        if method_rows
                            .insert(
                                parameter.id,
                                crate::types::clone_effect_row_with_budget(row, work)
                                    .map_err(|()| resource())?,
                            )
                            .is_some()
                        {
                            return Err(invalid(at));
                        }
                    }
                    (kind, crate::types::KindedArgument::TypeArg(ty))
                        if *kind != crate::types::Kind::EffectRow =>
                    {
                        replacements.insert_discarding_replaced(
                            parameter.id,
                            clone_type_with_budget(ty, work).map_err(|()| resource())?,
                        )
                    }
                    _ => return Err(invalid(at)),
                }
            }
            let mut domain = substitute(&method.value_type, &replacements, &method_rows, at, work)?;
            if !method.authoritative_type_parameters().is_empty() {
                let mut parameters = Vec::new();
                charge(work, method.authoritative_type_parameters().len())?;
                parameters
                    .try_reserve_exact(method.authoritative_type_parameters().len())
                    .map_err(|_| resource())?;
                for parameter in method.authoritative_type_parameters() {
                    // This data-only checkpoint does not claim continuation-row
                    // relocation or higher-kinded method argument support.
                    if !matches!(parameter.kind, crate::types::Kind::Type) {
                        return Err(invalid(at));
                    }
                    parameters.push((parameter.id, crate::types::Kind::Type));
                }
                charge(work, 1)?;
                domain = IterativeTypeOwner::new(Type::Forall(
                    parameters.into_boxed_slice(),
                    Box::new(domain.into_inner()),
                ));
            }
            charge(work, 1)?;
            body = IterativeTypeOwner::new(Type::Function(
                Box::new(domain.into_inner()),
                Box::new(body.into_inner()),
            ));
        }
    }
    if !scheme.type_parameters.is_empty() {
        let parameters = clone_kinded_type_parameters_with_budget(&scheme.type_parameters, work)
            .map_err(|()| resource())?;
        charge(work, 1)?;
        body = IterativeTypeOwner::new(Type::Forall(
            parameters.into_boxed_slice(),
            Box::new(body.into_inner()),
        ));
    }
    Ok(body)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn authenticate_staged_externals_with_defining<'a>(
    program: &'a UnvalidatedEffectProgram,
    imported: &'a ImportedFacts,
    defining: Option<&'a crate::resolved::ProviderDefiningFacts>,
    publication: &crate::evidence::PendingEvidencePublication,
    occurrences: &[ProviderExternalOccurrence<'_>],
    sources: &[&SourceFile],
    module_sources: &[(ModuleId, SourceId)],
    canonical: &crate::resolved::ResolvedRegistry,
    associations: &[DraftStateAssociation<'_>],
    occurrence_module: ModuleId,
    definition: &crate::resolved::ResolvedResourceDefinition,
    phase: super::LifecyclePhase,
    native_authentication: Option<&crate::foreign::NativeAuthenticationSession>,
    work: &mut TypeWorkBudget,
) -> Result<AuthenticatedProviderExternals<'a>, ValidationError> {
    if definition.id.module() != occurrence_module {
        return Err(invalid(program.root));
    }
    // The source constructor has authenticated this exact original declaration.
    // Reconstruct its phase inventory independently of candidate Core nodes.
    // A canonical registry without lexical definitions admits no source locals.
    let fragment_locals = if canonical.lexical_nominals().is_empty() {
        Vec::new()
    } else {
        super::handler::source_fragment_locals(
            match phase {
                super::LifecyclePhase::Acquire => &definition.acquire,
                super::LifecyclePhase::Finish => &definition.finish,
            },
            work,
        )?
    };
    authenticate_staged_externals_context(
        program,
        imported,
        defining,
        publication,
        occurrences,
        sources,
        module_sources,
        canonical,
        associations,
        occurrence_module,
        None,
        Some(&fragment_locals),
        native_authentication,
        work,
    )
}

#[allow(clippy::too_many_arguments)] // Independent source, actual and work authorities stay explicit.
pub(in crate::core) fn authenticate_handler_staged_externals<'a>(
    entry: &'a super::HandlerFragmentEntry<'a>,
    publication: &crate::evidence::PendingEvidencePublication,
    occurrences: &[ProviderExternalOccurrence<'_>],
    sources: &[&SourceFile],
    module_sources: &[(ModuleId, SourceId)],
    associations: &[DraftStateAssociation<'_>],
    native_authentication: Option<&crate::foreign::NativeAuthenticationSession>,
    work: &mut TypeWorkBudget,
) -> Result<AuthenticatedProviderExternals<'a>, ValidationError> {
    let import_count = if entry.family_definition().is_some() {
        charge(work, entry.imports.len())?;
        entry
            .imports
            .values()
            .filter(|source| source.global_binder().is_some())
            .count()
    } else {
        entry.imports.len()
    };
    if occurrences.len() != import_count {
        return Err(invalid(entry.draft.program.root));
    }
    let mut canonical_occurrences = Vec::new();
    let mut used = HashSet::new();
    charge(work, occurrences.len().checked_mul(2).ok_or_else(resource)?)?;
    canonical_occurrences
        .try_reserve_exact(occurrences.len())
        .map_err(|_| resource())?;
    used.try_reserve(occurrences.len())
        .map_err(|_| resource())?;
    for claimed in occurrences {
        let span = claimed.source.origin.primary_span();
        let canonical = entry
            .imports
            .get(&span)
            .ok_or_else(|| invalid(claimed.root))?;
        charge(
            work,
            canonical
                .spelling
                .len()
                .checked_add(canonical.evidence.len())
                .ok_or_else(resource)?,
        )?;
        if !used.insert(span)
            || claimed.source.term != canonical.term
            || claimed.source.spelling != canonical.spelling
            || claimed.source.import_span() != canonical.import_span()
            || claimed.source.evidence.len() != canonical.evidence.len()
            || !crate::resolved::same_origin_with_budget(
                &claimed.source.origin,
                &canonical.origin,
                work,
            )
            .map_err(|()| resource())?
            || claimed
                .source
                .evidence
                .iter()
                .zip(&canonical.evidence)
                .any(|(left, right)| {
                    left.storage_id() != right.storage_id()
                        || left.selection().is_some()
                        || right.selection().is_some()
                })
        {
            return Err(invalid(claimed.root));
        }
        canonical_occurrences.push(ProviderExternalOccurrence {
            root: claimed.root,
            source: canonical,
            arguments: claimed.arguments,
            row_arguments: claimed.row_arguments,
        });
    }
    authenticate_staged_externals_context(
        &entry.draft.program,
        entry.module.imported_facts(),
        entry.draft.defining_facts.as_deref(),
        publication,
        &canonical_occurrences,
        sources,
        module_sources,
        &entry.canonical,
        associations,
        entry.module.module(),
        Some(entry),
        Some(&entry.fragment_locals),
        native_authentication,
        work,
    )
}

#[expect(
    clippy::too_many_arguments,
    reason = "ordinary and handler drafts share complete selected ABI authentication without synthetic entry wrappers"
)]
fn authenticate_staged_externals_context<'a>(
    program: &'a UnvalidatedEffectProgram,
    imported: &'a ImportedFacts,
    defining: Option<&'a crate::resolved::ProviderDefiningFacts>,
    publication: &crate::evidence::PendingEvidencePublication,
    occurrences: &[ProviderExternalOccurrence<'_>],
    sources: &[&SourceFile],
    module_sources: &[(ModuleId, SourceId)],
    canonical: &crate::resolved::ResolvedRegistry,
    associations: &[DraftStateAssociation<'_>],
    occurrence_module: ModuleId,
    entry: Option<&'a super::HandlerFragmentEntry<'a>>,
    fragment_locals: Option<&[crate::types::NominalTypeId]>,
    native_authentication: Option<&crate::foreign::NativeAuthenticationSession>,
    work: &mut TypeWorkBudget,
) -> Result<AuthenticatedProviderExternals<'a>, ValidationError> {
    let facts = ProviderExternalFacts { imported, defining };
    use crate::interface::EvidenceNode;
    let mut types: HashMap<BinderId, IterativeTypeOwner> = HashMap::new();
    let mut origins = HashMap::new();
    let mut captures = HashMap::new();
    let mut staged_captures = HashMap::new();
    let mut source_occurrences = HashMap::new();
    let mut native_layout_nodes = HashMap::new();
    let mut dictionary_edges = HashMap::new();
    let mut dictionary_variables = HashSet::new();
    let mut dictionary_methods = HashMap::new();
    let mut dictionary_installers = HashSet::new();
    let mut authenticated_variables = HashSet::new();
    let mut seen_occurrences = HashSet::new();
    let mut roots = Vec::new();
    let mut constraints = crate::interface::InterfaceConstraintBudget::with_limit(work.remaining());
    let mut family_formals = Vec::new();
    if let Some(entry) = entry.filter(|entry| entry.family_definition().is_some()) {
        charge(work, entry.dictionary_parameters().len())?;
        family_formals
            .try_reserve_exact(entry.dictionary_parameters().len())
            .map_err(|_| resource())?;
        family_formals.extend(entry.dictionary_parameters());
    }
    let family_scope = entry.and_then(|entry| {
        entry.family_definition().map(|definition| {
            crate::evidence_validation::ProviderFamilyEvidenceScope {
                definition,
                requirements: entry.family_requirements(),
                dictionary_parameters: &family_formals,
            }
        })
    });
    // The source inventory is a map. Use alleged catalogue slots only to
    // order the independently authenticated inputs, with an exact bijection;
    // the claimed metadata supplies no method or application authority.
    let mut family_methods = Vec::new();
    if let Some(entry) = entry.filter(|entry| entry.family_definition().is_some()) {
        charge(work, entry.imports.len())?;
        let mut methods_by_slot = HashMap::new();
        methods_by_slot
            .try_reserve(entry.imports.len())
            .map_err(|_| resource())?;
        for source in entry.source_methods() {
            let [slot] = source.evidence.as_ref() else {
                return Err(invalid(program.root));
            };
            if methods_by_slot.insert(slot.storage_id(), source).is_some() {
                return Err(invalid(program.root));
            }
        }
        charge(work, program.method_evidence.occurrences().len())?;
        family_methods
            .try_reserve_exact(methods_by_slot.len())
            .map_err(|_| resource())?;
        for occurrence in program.method_evidence.occurrences() {
            if occurrence.checked_method.is_some() {
                family_methods.push(
                    methods_by_slot
                        .remove(&occurrence.slot)
                        .ok_or_else(|| invalid(program.root))?,
                );
            }
        }
        if !methods_by_slot.is_empty() {
            return Err(invalid(program.root));
        }
    }
    let expected_catalog =
        crate::evidence_validation::build_provider_method_evidence_catalog_with_family_scope(
            facts,
            canonical,
            occurrences
                .first()
                .map(|o| o.source.origin.primary_span())
                .map(Ok)
                .unwrap_or_else(|| {
                    super::super::transform::provider_draft_span(program, program.root)
                })
                .map_err(|_| invalid(program.root))?,
            occurrences
                .iter()
                .map(|o| o.source)
                .chain(family_methods.iter().copied()),
            publication,
            &mut constraints,
            work,
            family_scope,
        );
    charge(work, constraints.used())?;
    let expected_catalog = expected_catalog.map_err(|failure| match failure.reason() {
        crate::evidence_validation::EvidenceValidationReason::ConstraintResourceExhausted
        | crate::evidence_validation::EvidenceValidationReason::TypeResourceExhausted => resource(),
        _ => invalid(program.root),
    })?;
    if !super::super::dialect::same_imported_method_evidence_catalog(
        &program.method_evidence,
        &expected_catalog,
        work,
    )
    .map_err(|()| resource())?
    {
        return Err(invalid(program.root));
    }
    let mut external_owners = HashSet::new();
    charge(
        work,
        expected_catalog
            .domains()
            .len()
            .checked_add(expected_catalog.implementation_owners().len())
            .ok_or_else(resource)?,
    )?;
    external_owners
        .try_reserve(
            expected_catalog
                .domains()
                .len()
                .checked_add(expected_catalog.implementation_owners().len())
                .ok_or_else(resource)?,
        )
        .map_err(|_| resource())?;
    for domain in expected_catalog.domains() {
        external_owners.insert(domain.owner);
    }
    for owner in expected_catalog.implementation_owners() {
        external_owners.insert(super::super::dialect::MethodEvidenceOwner::Implementation(
            owner.implementation,
        ));
    }

    if let Some(scope) = family_scope {
        charge(work, 1)?;
        external_owners.try_reserve(1).map_err(|_| resource())?;
        external_owners.insert(super::super::dialect::MethodEvidenceOwner::ResourceFamily(
            scope.definition.id,
        ));
        for source in &family_methods {
            charge(work, 1)?;
            let crate::resolved::ResolvedTermName::Method(method) = source.term else {
                return Err(invalid(program.root));
            };
            let [slot] = source.evidence.as_ref() else {
                return Err(invalid(program.root));
            };
            let pending = publication
                .occurrence(slot.storage_id(), Some(method), work)
                .map_err(|failure| match failure {
                    crate::evidence::SelectionFailure::TypeResource => resource(),
                    _ => invalid(program.root),
                })?;
            if let Some(EvidenceNode::Abstract { requirement, .. }) =
                pending.selection.node(pending.selection.root())
            {
                authenticate_family_abstract_selection(
                    program,
                    facts,
                    scope,
                    pending.selection,
                    pending.application,
                    program.root,
                    work,
                )?;
                let value_type = pending.value_type.ok_or_else(|| invalid(program.root))?;
                let (witness, payload) = authenticate_family_layout_method(
                    canonical,
                    scope,
                    method,
                    pending.application,
                    value_type,
                    program.root,
                    work,
                )?;
                let mut found = false;
                for (ordinal, stored) in program.nodes.iter().enumerate() {
                    charge(work, 1)?;
                    if !matches!(
                        &stored.kind,
                        EffectExprKind::Pure(PureExprKind::Variable(_))
                    ) {
                        continue;
                    }
                    let Some(origin) = stored.origin.as_ref() else {
                        continue;
                    };
                    if !crate::resolved::same_origin_with_budget(origin, &source.origin, work)
                        .map_err(|()| resource())?
                    {
                        continue;
                    }
                    let id = NodeId::new(
                        program.arena,
                        u32::try_from(ordinal).map_err(|_| resource())?,
                    );
                    authenticate_family_dictionary_variable(
                        program,
                        facts,
                        scope,
                        requirement,
                        method,
                        id,
                        &source.origin,
                        work,
                    )?;
                    require_same(value_type, &stored.ty, id, work)?;
                    dictionary_variables
                        .try_reserve(1)
                        .map_err(|_| resource())?;
                    dictionary_variables.insert(id);
                    charge(work, 1)?;
                    dictionary_methods.try_reserve(1).map_err(|_| resource())?;
                    let EffectExprKind::Pure(PureExprKind::Variable(variable)) = &stored.kind
                    else {
                        return Err(invalid(id));
                    };
                    if dictionary_methods
                        .insert(
                            id,
                            DeclaredLayoutMethod {
                                node: id,
                                requirement,
                                method,
                                binder: variable.binder(),
                                witness,
                                payload,
                            },
                        )
                        .is_some()
                    {
                        return Err(invalid(id));
                    }
                    found = true;
                }
                if !found {
                    return Err(invalid(program.root));
                }
            } else if let Some(EvidenceNode::NativeLayout { producer }) =
                pending.selection.node(pending.selection.root())
            {
                if producer.method() != method
                    || pending.method != Some(method)
                    || !pending.method_arguments.is_empty()
                {
                    return Err(invalid(program.root));
                }
                // Reuse the closed canonical selection check for the complete
                // Layout goal, plan, payload, method and original dictionary.
                let mut selected_work =
                    crate::interface::InterfaceConstraintBudget::with_limit(work.remaining());
                let selected = crate::evidence_validation::validate_provider_closed_selection(
                    facts,
                    canonical,
                    occurrence_module,
                    pending.selection,
                    pending.application,
                    &mut selected_work,
                    work,
                    source.origin.primary_span(),
                );
                charge(work, selected_work.used())?;
                selected.map_err(|failure| match failure.reason() {
                    crate::evidence_validation::EvidenceValidationReason::ConstraintResourceExhausted
                    | crate::evidence_validation::EvidenceValidationReason::TypeResourceExhausted => resource(),
                    _ => invalid(program.root),
                })?;
                let value_type = pending.value_type.ok_or_else(|| invalid(program.root))?;
                let mut found = false;
                for anchor in &program.method_evidence_anchors {
                    charge(work, 1)?;
                    if anchor.occurrence != Some(slot.storage_id())
                        || anchor.method != method
                        || anchor.role
                            != (super::super::dialect::MethodEvidenceAnchorRole::NativeLayoutUse {
                                producer,
                                selection_node: pending.selection.root(),
                            })
                    {
                        continue;
                    }
                    if found {
                        return Err(invalid(anchor.node));
                    }
                    // The canonical catalogue and subsequent whole-structure
                    // check authenticate the anchor. This also checks the
                    // actual node's complete intrinsic header, type and origin.
                    authenticate_native_layout_dictionary_node(
                        program,
                        canonical,
                        anchor.node,
                        producer,
                        &source.origin,
                        work,
                    )?;
                    require_same(
                        value_type,
                        &node(program, anchor.node)?.ty,
                        anchor.node,
                        work,
                    )?;
                    charge(work, 1)?;
                    native_layout_nodes.try_reserve(1).map_err(|_| resource())?;
                    if native_layout_nodes.insert(anchor.node, producer).is_some() {
                        return Err(invalid(anchor.node));
                    }
                    found = true;
                }
                if !found {
                    return Err(invalid(program.root));
                }
            }
        }
    }

    for occurrence in occurrences {
        charge(work, 1)?;
        seen_occurrences.try_reserve(1).map_err(|_| resource())?;
        if !seen_occurrences.insert(occurrence.root) {
            return Err(invalid(occurrence.root));
        }
        let binder = occurrence
            .source
            .global_binder()
            .ok_or_else(|| invalid(occurrence.root))?;
        let global = facts
            .global(binder)
            .ok_or_else(|| invalid(occurrence.root))?;
        if global.scheme().requirements.len() != occurrence.source.evidence.len() {
            return Err(invalid(occurrence.root));
        }
        let (actual_types, actual_rows) = substitutions(
            &global.scheme().type_parameters,
            occurrence.arguments,
            occurrence.row_arguments,
            occurrence.root,
            work,
        )?;
        for argument in occurrence.arguments {
            if !family_scope.is_some_and(|scope| matches!(argument, Type::Variable(id)
                if scope.definition.family_template.as_ref().is_some_and(|family| family.parameter.id == *id))) {
                closed_data_type(program, imported, argument, occurrence.root, work)?;
            }
        }
        if occurrence.row_arguments.iter().any(|row| !row.is_empty()) {
            return Err(invalid(occurrence.root));
        }
        let result = substitute(
            &global.scheme().value_type,
            &actual_types,
            &actual_rows,
            occurrence.root,
            work,
        )?;
        require_same(
            &result,
            &node(program, occurrence.root)?.ty,
            occurrence.root,
            work,
        )?;
        let scheme = canonical_scheme(global.scheme(), facts, occurrence.root, work)?;
        let mut edge_count = 0usize;
        for requirement in &global.scheme().requirements {
            let interface = facts
                .interface(requirement.interface(), work)
                .map_err(|()| resource())?
                .ok_or_else(|| invalid(occurrence.root))?;
            edge_count = edge_count
                .checked_add(interface.methods.len())
                .ok_or_else(resource)?;
        }
        charge(work, edge_count)?;
        let mut edges = Vec::new();
        edges
            .try_reserve_exact(edge_count)
            .map_err(|_| resource())?;
        let mut head = occurrence.root;
        for _ in 0..edge_count {
            let stored = node(program, head)?;
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                application,
            ))) = &stored.kind
            else {
                return Err(invalid(head));
            };
            if !stored.effects.is_empty() {
                return Err(invalid(head));
            }
            require_origin(program, head, &occurrence.source.origin, work)?;
            edges.push((head, application.function(), application.argument()));
            head = application.function();
        }
        edges.reverse();
        let variable = if global.scheme().type_parameters.is_empty() {
            if !occurrence.arguments.is_empty() || !occurrence.row_arguments.is_empty() {
                return Err(invalid(head));
            }
            head
        } else {
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
                application,
            ))) = &node(program, head)?.kind
            else {
                return Err(invalid(head));
            };
            compare_actual_arguments(
                application.arguments(),
                application.row_arguments(),
                occurrence.arguments,
                occurrence.row_arguments,
                head,
                work,
            )?;
            require_origin(program, head, &occurrence.source.origin, work)?;
            application.function()
        };
        if !matches!(&node(program, variable)?.kind, EffectExprKind::Pure(PureExprKind::Variable(variable)) if variable.binder() == binder)
        {
            return Err(invalid(variable));
        }
        require_same(&scheme, &node(program, variable)?.ty, variable, work)?;
        require_origin(program, variable, &occurrence.source.origin, work)?;
        charge(work, 4)?;
        authenticated_variables
            .try_reserve(1)
            .map_err(|_| resource())?;
        authenticated_variables.insert(variable);
        types.try_reserve(1).map_err(|_| resource())?;
        origins.try_reserve(1).map_err(|_| resource())?;
        captures.try_reserve(1).map_err(|_| resource())?;
        if let Some(previous) = types.get(&binder) {
            require_same(previous, &scheme, variable, work)?;
        } else {
            types.insert(binder, scheme);
        }
        origins.insert(binder, global.origin());
        captures.insert(binder, global.capture());
        let mut methods = Vec::new();
        let mut adapters = Vec::new();
        charge(work, occurrence.source.evidence.len())?;
        let mut checked_evidence = Vec::new();
        checked_evidence
            .try_reserve_exact(occurrence.source.evidence.len())
            .map_err(|_| resource())?;
        let mut edge = edges.iter();
        for (requirement, slot) in global
            .scheme()
            .requirements
            .iter()
            .zip(&occurrence.source.evidence)
        {
            let pending = publication
                .occurrence(slot.storage_id(), None, work)
                .map_err(|failure| match failure {
                    crate::evidence::SelectionFailure::TypeResource => resource(),
                    _ => invalid(occurrence.root),
                })?;
            if pending.method.is_some()
                || pending.value_type.is_some()
                || !pending.method_arguments.is_empty()
            {
                return Err(invalid(occurrence.root));
            }
            if pending.application.interface() != requirement.interface()
                || pending.application.arguments().len() != requirement.arguments().len()
                || pending.selection.interface() != requirement.interface()
                || pending.selection.arguments().len() != requirement.arguments().len()
            {
                return Err(invalid(occurrence.root));
            }
            for ((formal, checked), selected) in requirement
                .arguments()
                .iter()
                .zip(pending.application.arguments())
                .zip(pending.selection.arguments())
            {
                let expected = substitute_argument(
                    formal,
                    &actual_types,
                    &actual_rows,
                    occurrence.root,
                    work,
                )?;
                require_same_argument(expected.as_ref(), checked, occurrence.root, work)?;
                require_same_argument(expected.as_ref(), selected, occurrence.root, work)?;
            }
            let mut constraints =
                crate::interface::InterfaceConstraintBudget::with_limit(work.remaining());
            let selected = if let Some(scope) = family_scope
                && matches!(
                    pending.selection.node(pending.selection.root()),
                    Some(EvidenceNode::Abstract { .. })
                ) {
                authenticate_family_abstract_selection(
                    program,
                    facts,
                    scope,
                    pending.selection,
                    pending.application,
                    occurrence.root,
                    work,
                )
            } else {
                let selected = crate::evidence_validation::validate_provider_closed_selection(
                    facts,
                    canonical,
                    occurrence_module,
                    pending.selection,
                    pending.application,
                    &mut constraints,
                    work,
                    occurrence.source.origin.primary_span(),
                );
                selected.map_err(|failure| match failure.reason() {
                    crate::evidence_validation::EvidenceValidationReason::ConstraintResourceExhausted
                    | crate::evidence_validation::EvidenceValidationReason::TypeResourceExhausted => resource(),
                    _ => invalid(occurrence.root),
                })
            };
            charge(work, constraints.used())?;
            selected?;
            let checked_application = pending
                .application
                .clone_with_budget(work)
                .map_err(|()| resource())?;
            charge(work, 1)?;
            checked_evidence.push((checked_application, pending.selection.clone()));
            for index in 0..pending.selection.node_count() {
                let Some(selected) = pending
                    .selection
                    .node(crate::interface::EvidenceNodeId::new(index))
                else {
                    return Err(invalid(occurrence.root));
                };
                let substitution = match selected {
                    EvidenceNode::Implementation { substitution, .. } => substitution,
                    EvidenceNode::NativeLayout { .. } => continue,
                    EvidenceNode::Abstract { .. } if family_scope.is_some() => continue,
                    _ => return Err(invalid(occurrence.root)),
                };
                for binding in substitution {
                    closed_data_type(program, imported, binding.argument(), occurrence.root, work)?;
                }
            }
            let targets = super::super::capture::selection_targets(
                pending.selection,
                None,
                |id, work| {
                    charge(work, 1).map_err(|_| super::super::capture::Failure::Resource)?;
                    facts
                        .implementation(id, work)
                        .map_err(|()| super::super::capture::Failure::Resource)?
                        .ok_or(super::super::capture::Failure::Invalid)
                },
                |_, _, _| Err(super::super::capture::Failure::Invalid),
                canonical,
                // Original handler family formals use Abstract evidence. A
                // concrete family requires its separate source certificate.
                |_, _, _, _| Err(super::super::capture::Failure::Invalid),
                &mut adapters,
                work,
            )
            .map_err(|failure| match failure {
                super::super::capture::Failure::Resource => resource(),
                _ => invalid(occurrence.root),
            })?;
            let interface = facts
                .interface(requirement.interface(), work)
                .map_err(|()| resource())?
                .ok_or_else(|| invalid(occurrence.root))?;
            if let Some(EvidenceNode::Abstract {
                requirement: formal_requirement,
                methods: selected,
            }) = pending.selection.node(pending.selection.root())
            {
                let scope = family_scope.ok_or_else(|| invalid(occurrence.root))?;
                if targets.len() != interface.methods.len() || selected.len() != targets.len() {
                    return Err(invalid(occurrence.root));
                }
                for ((method, selected), (target_method, target)) in
                    interface.methods.iter().zip(selected).zip(targets)
                {
                    if method.id != *selected
                        || target_method != method.id
                        || !matches!(target, super::super::capture::MethodTarget::Abstract(id) if id == formal_requirement)
                    {
                        return Err(invalid(occurrence.root));
                    }
                    let &(application, previous, argument) =
                        edge.next().ok_or_else(|| invalid(occurrence.root))?;
                    authenticate_family_dictionary_variable(
                        program,
                        facts,
                        scope,
                        formal_requirement,
                        method.id,
                        argument,
                        &occurrence.source.origin,
                        work,
                    )?;
                    charge(work, 2)?;
                    dictionary_edges.try_reserve(1).map_err(|_| resource())?;
                    if dictionary_edges
                        .insert(application, (binder, previous))
                        .is_some()
                    {
                        return Err(invalid(application));
                    }
                    dictionary_variables
                        .try_reserve(1)
                        .map_err(|_| resource())?;
                    dictionary_variables.insert(argument);
                    methods.try_reserve(1).map_err(|_| resource())?;
                    methods.push((requirement.id, method.id, target));
                }
                continue;
            }
            if let Some(EvidenceNode::NativeLayout { producer }) =
                pending.selection.node(pending.selection.root())
            {
                let [(target_method, super::super::capture::MethodTarget::NativeLayout(target))] =
                    targets.as_slice()
                else {
                    return Err(invalid(occurrence.root));
                };
                if interface.methods.len() != 1
                    || interface.methods[0].id != producer.method()
                    || *target_method != producer.method()
                    || *target != producer
                {
                    return Err(invalid(occurrence.root));
                }
                let &(application, previous, argument) =
                    edge.next().ok_or_else(|| invalid(occurrence.root))?;
                authenticate_native_layout_dictionary_node(
                    program,
                    canonical,
                    argument,
                    producer,
                    &occurrence.source.origin,
                    work,
                )?;
                charge(work, 2)?;
                dictionary_edges.try_reserve(1).map_err(|_| resource())?;
                if dictionary_edges
                    .insert(application, (binder, previous))
                    .is_some()
                {
                    return Err(invalid(application));
                }
                methods.try_reserve(1).map_err(|_| resource())?;
                methods.push((
                    requirement.id,
                    producer.method(),
                    super::super::capture::MethodTarget::NativeLayout(producer),
                ));
                continue;
            }
            let EvidenceNode::Implementation {
                methods: selected, ..
            } = pending
                .selection
                .node(pending.selection.root())
                .ok_or_else(|| invalid(occurrence.root))?
            else {
                return Err(invalid(occurrence.root));
            };
            if targets.len() != interface.methods.len() || selected.len() != targets.len() {
                return Err(invalid(occurrence.root));
            }
            for ((method, selected), (target_method, target)) in
                interface.methods.iter().zip(selected).zip(targets)
            {
                let super::super::capture::MethodTarget::Adapter { value: adapter, .. } = target
                else {
                    return Err(invalid(occurrence.root));
                };
                if method.id != target_method || selected.method() != method.id {
                    return Err(invalid(occurrence.root));
                }
                let &(application, previous, argument) =
                    edge.next().ok_or_else(|| invalid(occurrence.root))?;
                charge(work, 3)?;
                roots.try_reserve(1).map_err(|_| resource())?;
                roots.push(ProviderDictionaryRoot {
                    slot: slot.storage_id(),
                    selection_node: pending.selection.root(),
                    implementation: *selected,
                    node: argument,
                });
                authenticate_dictionary_variables(
                    program,
                    argument,
                    pending.selection,
                    &occurrence.source.origin,
                    facts,
                    canonical,
                    &mut types,
                    &mut origins,
                    &mut authenticated_variables,
                    &mut dictionary_variables,
                    &mut dictionary_installers,
                    work,
                )?;
                dictionary_edges.try_reserve(1).map_err(|_| resource())?;
                if dictionary_edges
                    .insert(application, (binder, previous))
                    .is_some()
                {
                    return Err(invalid(application));
                }
                methods.try_reserve(1).map_err(|_| resource())?;
                methods.push((
                    requirement.id,
                    method.id,
                    super::super::capture::MethodTarget::Adapter {
                        value: adapter,
                        binder: adapters
                            .get(adapter)
                            .ok_or_else(|| invalid(occurrence.root))?
                            .binder,
                    },
                ));
            }
        }
        if edge.next().is_some() {
            return Err(invalid(occurrence.root));
        }
        let capture = source_capture_relation(
            program,
            global,
            occurrence.arguments,
            occurrence.row_arguments,
            &methods,
            &adapters,
            facts,
            work,
        )?;
        charge(work, 1)?;
        staged_captures.try_reserve(1).map_err(|_| resource())?;
        staged_captures.insert(occurrence.root, capture);
        let mut arguments = IterativeArguments(Vec::new());
        charge(
            work,
            occurrence.arguments.len() + occurrence.row_arguments.len() + 1,
        )?;
        arguments
            .0
            .try_reserve_exact(occurrence.arguments.len())
            .map_err(|_| resource())?;
        for argument in occurrence.arguments {
            arguments
                .0
                .push(clone_type_with_budget(argument, work).map_err(|()| resource())?);
        }
        let mut rows = Vec::new();
        rows.try_reserve_exact(occurrence.row_arguments.len())
            .map_err(|_| resource())?;
        for row in occurrence.row_arguments {
            rows.push(
                crate::types::clone_effect_row_with_budget(row, work).map_err(|()| resource())?,
            );
        }
        source_occurrences.try_reserve(1).map_err(|_| resource())?;
        source_occurrences.insert(
            occurrence.root,
            ProviderSourceOccurrence {
                checked_evidence,
                global,
                arguments,
                rows,
                methods,
                adapters,
            },
        );
    }

    for (ordinal, stored) in program.nodes.iter().enumerate() {
        charge(work, 1)?;
        if let EffectExprKind::Pure(PureExprKind::Variable(variable)) = &stored.kind
            && types.contains_key(&variable.binder())
            && !authenticated_variables.contains(&NodeId::new(
                program.arena,
                u32::try_from(ordinal).map_err(|_| resource())?,
            ))
        {
            return Err(invalid(program.root));
        }
    }
    let method_evidence = AuthenticatedProviderMethodEvidence {
        arena: program.arena,
        catalog: &program.method_evidence,
        owners: external_owners,
        roots,
    };
    let accesses = authenticate_state_accesses(program, associations, work)?;

    super::super::validate::check_provider_external_structure(
        program,
        sources,
        module_sources,
        canonical,
        &origins,
        &types,
        &accesses,
        Some(&method_evidence),
        entry,
        fragment_locals,
        native_authentication,
        work,
    )?;

    Ok(AuthenticatedProviderExternals {
        program,
        types,
        captures,
        staged_captures,
        source_occurrences,
        native_layout_nodes,
        dictionary_edges,
        dictionary_variables,
        dictionary_methods,
        dictionary_installers,
        imported,
        defining,
        entry,
        family: entry.and_then(|entry| entry.family_identity()),
    })
}

struct IterativeArguments(Vec<Type>);
impl IterativeArguments {
    fn into_vec(mut self) -> Vec<Type> {
        std::mem::take(&mut self.0)
    }
}
impl Drop for IterativeArguments {
    fn drop(&mut self) {
        for ty in std::mem::take(&mut self.0) {
            crate::types::discard_type_iteratively(ty);
        }
    }
}

fn compare_actual_arguments(
    actual: &[Type],
    actual_rows: &[crate::types::EffectRow],
    expected: &[Type],
    expected_rows: &[crate::types::EffectRow],
    at: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    if actual.len() != expected.len() || actual_rows.len() != expected_rows.len() {
        return Err(invalid(at));
    }
    for (actual, expected) in actual.iter().zip(expected) {
        require_same(actual, expected, at, work)?;
    }
    for (actual, expected) in actual_rows.iter().zip(expected_rows) {
        if !crate::types::same_effect_rows_with_budget(actual, expected, work)
            .map_err(|()| resource())?
        {
            return Err(invalid(at));
        }
    }
    Ok(())
}
/// Authenticates only an original family formal. The enclosing catalogue
/// reconstruction has already checked the entire written family scope.
fn authenticate_family_abstract_selection(
    program: &UnvalidatedEffectProgram,
    facts: ProviderExternalFacts<'_>,
    scope: crate::evidence_validation::ProviderFamilyEvidenceScope<'_>,
    selection: &crate::interface::EvidenceSelection,
    application: &crate::interface::InterfaceApplication,
    at: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let Some(crate::interface::EvidenceNode::Abstract {
        requirement,
        methods,
    }) = selection.node(selection.root())
    else {
        return Err(invalid(at));
    };
    charge(
        work,
        scope
            .requirements
            .len()
            .checked_add(methods.len())
            .ok_or_else(resource)?,
    )?;
    if selection.node_count() != 1
        || requirement.owner()
            != crate::interface::RequirementOwner::ResourceFamily(scope.definition.id)
    {
        return Err(invalid(at));
    }
    let checked = scope
        .requirements
        .iter()
        .find(|checked| checked.id == requirement)
        .ok_or_else(|| invalid(at))?;
    if checked.interface() != application.interface()
        || selection.interface() != application.interface()
        || checked.arguments().len() != application.arguments().len()
        || selection.arguments().len() != application.arguments().len()
    {
        return Err(invalid(at));
    }
    for ((formal, actual), selected) in checked
        .arguments()
        .iter()
        .zip(application.arguments())
        .zip(selection.arguments())
    {
        require_same_argument(formal, actual, at, work)?;
        require_same_argument(formal, selected, at, work)?;
    }
    let interface = facts
        .interface(checked.interface(), work)
        .map_err(|()| resource())?
        .ok_or_else(|| invalid(at))?;
    charge(work, interface.methods.len())?;
    if !methods
        .iter()
        .copied()
        .eq(interface.methods.iter().map(|method| method.id))
    {
        return Err(invalid(at));
    }
    node(program, at)?;
    Ok(())
}

/// Matches the actual dictionary argument to its ordered, genuine family
/// formal. No variable of the same type is accepted as a replacement.
#[expect(
    clippy::too_many_arguments,
    reason = "original family scope and actual argument provenance are independent inputs"
)]
fn authenticate_family_dictionary_variable(
    program: &UnvalidatedEffectProgram,
    facts: ProviderExternalFacts<'_>,
    scope: crate::evidence_validation::ProviderFamilyEvidenceScope<'_>,
    requirement: crate::interface::RequirementId,
    method: crate::interface::MethodId,
    at: NodeId,
    origin: &crate::source::Origin,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    charge(work, scope.requirements.len())?;
    let mut position = 0usize;
    for checked in scope.requirements {
        let interface = facts
            .interface(checked.interface(), work)
            .map_err(|()| resource())?
            .ok_or_else(|| invalid(at))?;
        charge(work, interface.methods.len())?;
        for declaration in &interface.methods {
            let formal = scope
                .dictionary_parameters
                .get(position)
                .ok_or_else(|| invalid(at))?;
            if checked.id == requirement && declaration.id == method {
                if !matches!(&node(program, at)?.kind,
                    EffectExprKind::Pure(PureExprKind::Variable(variable))
                        if variable.binder() == formal.id())
                {
                    return Err(invalid(at));
                }
                require_same(formal.ty(), &node(program, at)?.ty, at, work)?;
                require_origin(program, at, origin, work)?;
                return Ok(());
            }
            position = position.checked_add(1).ok_or_else(resource)?;
        }
    }
    Err(invalid(at))
}

/// A rigid payload is admitted through the declared Layout requirement, not
/// by guessing a closed scalar dictionary. The canonical foreign fact fixes
/// the original method and opaque witness family; the checked catalog has
/// independently authenticated the complete method substitution and formal.
fn authenticate_family_layout_method(
    canonical: &crate::resolved::ResolvedRegistry,
    scope: crate::evidence_validation::ProviderFamilyEvidenceScope<'_>,
    method: crate::interface::MethodId,
    application: &crate::interface::InterfaceApplication,
    value_type: &Type,
    at: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<(crate::types::NominalTypeId, crate::types::TypeVariableId), ValidationError> {
    let mut layout = None;
    for module in canonical.foreign_modules() {
        charge(work, 1)?;
        if let Some(candidate) = module.layout.as_ref()
            && candidate.method() == method
            && layout.replace(candidate).is_some()
        {
            return Err(invalid(at));
        }
    }
    let layout = layout.ok_or_else(|| invalid(at))?;
    let [crate::types::KindedArgument::TypeArg(payload)] = application.arguments() else {
        return Err(invalid(at));
    };
    let family = scope
        .definition
        .family_template
        .as_ref()
        .ok_or_else(|| invalid(at))?;
    let Type::Variable(payload_parameter) = payload else {
        return Err(invalid(at));
    };
    if *payload_parameter != family.parameter.id {
        return Err(invalid(at));
    }
    let function = value_type.function_view().ok_or_else(|| invalid(at))?;
    let Type::Application(head, witness_payload) = function.value() else {
        return Err(invalid(at));
    };
    if layout.interface() != application.interface()
        || method.interface() != layout.interface()
        || function.effects().is_some()
        || !matches!(&**head, Type::Nominal(witness) if *witness == layout.witness())
    {
        return Err(invalid(at));
    }
    require_same(function.domain(), &Type::Unit, at, work)?;
    require_same(payload, witness_payload, at, work)?;
    Ok((layout.witness(), *payload_parameter))
}

/// The original registry table and exact copied intrinsic establish native
/// dictionary identity; no source variable or numeric tag can replace it.
fn authenticate_native_layout_dictionary_node(
    program: &UnvalidatedEffectProgram,
    canonical: &crate::resolved::ResolvedRegistry,
    at: NodeId,
    producer: crate::foreign::ForeignLayoutProducer,
    origin: &crate::source::Origin,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let dictionary = canonical
        .foreign_layout_dictionary(producer, work)
        .map_err(|failure| {
            if failure.is_resource_exhaustion() {
                resource()
            } else {
                invalid(at)
            }
        })?;
    let stored = node(program, at)?;
    require_origin(program, at, origin, work)?;
    let EffectExprKind::Pure(PureExprKind::Value(PureValue::Intrinsic(intrinsic))) = &stored.kind
    else {
        return Err(invalid(at));
    };
    if !stored.effects.is_empty()
        || dictionary.producer() != producer
        || intrinsic.module() != producer.interface().module()
        || intrinsic.operation()
            != (super::super::packed::Intrinsic::ForeignLayoutWitness { producer })
        || !matches!(
            dictionary.payload_type(),
            Type::Unit | Type::Bool | Type::Int
        )
    {
        return Err(invalid(at));
    }
    require_same(&stored.ty, &producer.producer_type(), at, work)
}

#[expect(
    clippy::too_many_arguments,
    reason = "original registry authenticates native prerequisites beside lexical producer records"
)]
fn authenticate_dictionary_variables<'a>(
    program: &UnvalidatedEffectProgram,
    root: NodeId,
    selection: &crate::interface::EvidenceSelection,
    origin: &crate::source::Origin,
    facts: ProviderExternalFacts<'a>,
    canonical: &crate::resolved::ResolvedRegistry,
    types: &mut HashMap<BinderId, IterativeTypeOwner>,
    origins: &mut HashMap<BinderId, &'a crate::source::Origin>,
    authenticated: &mut HashSet<NodeId>,
    dictionary_variables: &mut HashSet<NodeId>,
    dictionary_installers: &mut HashSet<NodeId>,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let mut pending = Vec::new();
    let mut visited = HashSet::new();
    charge(work, 1)?;
    pending.try_reserve(1).map_err(|_| resource())?;
    pending.push(root);
    while let Some(id) = pending.pop() {
        charge(work, 1)?;
        visited.try_reserve(1).map_err(|_| resource())?;
        if !visited.insert(id) {
            continue;
        }
        let stored = node(program, id)?;
        require_origin(program, id, origin, work)?;
        if !stored.effects.is_empty() {
            return Err(invalid(id));
        }
        match &stored.kind {
            EffectExprKind::Pure(PureExprKind::Variable(variable)) => {
                let mut producer = None;
                for index in 0..selection.node_count() {
                    charge(work, 1)?;
                    let (implementation, methods) =
                        match selection.node(crate::interface::EvidenceNodeId::new(index)) {
                            Some(crate::interface::EvidenceNode::Implementation {
                                implementation,
                                methods,
                                ..
                            }) => (implementation, methods),
                            Some(crate::interface::EvidenceNode::NativeLayout { .. }) => continue,
                            _ => return Err(invalid(id)),
                        };
                    let owner = facts
                        .implementation(implementation, work)
                        .map_err(|()| resource())?
                        .ok_or_else(|| invalid(id))?;
                    charge(
                        work,
                        owner
                            .methods
                            .len()
                            .checked_mul(methods.len())
                            .ok_or_else(resource)?,
                    )?;
                    for selected in methods {
                        if let Some(method) = owner.methods.iter().find(|method| {
                            method.id == *selected && method.binder == variable.binder()
                        }) {
                            producer = Some(method);
                        }
                    }
                }
                let producer = producer.ok_or_else(|| invalid(id))?;
                authenticate_producer_variable(program, id, producer, facts, work)?;
                let expected = IterativeTypeOwner::new(
                    clone_type_with_budget(&stored.ty, work).map_err(|()| resource())?,
                );
                // A producer's fresh scheme parameters cannot capture an
                // adapter abstraction or another producer's scheme envelope.
                if let Type::Forall(parameters, _) = &*expected {
                    for (parameter, _) in parameters {
                        charge(
                            work,
                            program
                                .nodes
                                .len()
                                .checked_add(types.len())
                                .ok_or_else(resource)?,
                        )?;
                        for stored in &program.nodes {
                            if let EffectExprKind::Pure(PureExprKind::Computation(
                                PureComputation::TypeAbstraction(abstraction),
                            )) = &stored.kind
                            {
                                charge(work, abstraction.parameters().len())?;
                                if abstraction
                                    .parameters()
                                    .iter()
                                    .any(|(bound, _)| bound == parameter)
                                {
                                    return Err(invalid(id));
                                }
                            }
                        }
                        for (owner, scheme) in types.iter() {
                            if *owner != producer.binder
                                && let Type::Forall(bound, _) = &**scheme
                            {
                                charge(work, bound.len())?;
                                if bound.iter().any(|(bound, _)| bound == parameter) {
                                    return Err(invalid(id));
                                }
                            }
                        }
                    }
                }
                if let Some(previous) = types.get(&producer.binder) {
                    require_same(previous, &expected, id, work)?;
                } else {
                    charge(work, 1)?;
                    types.try_reserve(1).map_err(|_| resource())?;
                    types.insert(producer.binder, expected);
                }
                charge(work, 3)?;
                origins.try_reserve(1).map_err(|_| resource())?;
                origins.insert(producer.binder, &producer.origin);
                authenticated.try_reserve(1).map_err(|_| resource())?;
                authenticated.insert(id);
                dictionary_variables
                    .try_reserve(1)
                    .map_err(|_| resource())?;
                dictionary_variables.insert(id);
            }
            EffectExprKind::Pure(PureExprKind::Value(PureValue::Intrinsic(intrinsic))) => {
                let super::super::packed::Intrinsic::ForeignLayoutWitness { producer } =
                    intrinsic.operation()
                else {
                    return Err(invalid(id));
                };
                charge(work, selection.node_count())?;
                let admitted = (0..selection.node_count()).any(|ordinal| matches!(
                    selection.node(crate::interface::EvidenceNodeId::new(ordinal)),
                    Some(crate::interface::EvidenceNode::NativeLayout { producer: selected }) if selected == producer));
                if !admitted {
                    return Err(invalid(id));
                }
                authenticate_native_layout_dictionary_node(
                    program, canonical, id, producer, origin, work,
                )?;
            }
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                application,
            ))) => {
                // These are prerequisite installation edges. The exact
                // canonical catalog/source-chain validation below must also
                // succeed before this private set is returned to flow.
                charge(work, 3)?;
                dictionary_installers
                    .try_reserve(1)
                    .map_err(|_| resource())?;
                dictionary_installers.insert(id);
                pending.try_reserve(2).map_err(|_| resource())?;
                pending.push(application.function());
                pending.push(application.argument());
            }
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeApplication(
                application,
            ))) => {
                charge(work, 1)?;
                pending.try_reserve(1).map_err(|_| resource())?;
                pending.push(application.function());
            }
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::TypeAbstraction(
                abstraction,
            ))) => {
                charge(work, 1)?;
                pending.try_reserve(1).map_err(|_| resource())?;
                pending.push(abstraction.body());
            }
            _ => return Err(invalid(id)),
        }
    }
    Ok(())
}

fn authenticate_producer_variable(
    program: &UnvalidatedEffectProgram,
    variable: NodeId,
    producer: &crate::resolved::CheckedImplementationMethodFact,
    facts: ProviderExternalFacts<'_>,
    work: &mut TypeWorkBudget,
) -> Result<NodeId, ValidationError> {
    if !matches!(&node(program, variable)?.kind, EffectExprKind::Pure(PureExprKind::Variable(variable)) if variable.binder() == producer.binder)
    {
        return Err(invalid(variable));
    }
    let actual = &node(program, variable)?.ty;
    let canonical = canonical_scheme(&producer.scheme, facts, variable, work)?;
    if producer.scheme.type_parameters.is_empty() {
        require_same(actual, &canonical, variable, work)?;
    } else {
        let Type::Forall(actual_parameters, actual_body) = actual else {
            return Err(invalid(variable));
        };
        if actual_parameters.len() != producer.scheme.type_parameters.len() {
            return Err(invalid(variable));
        }
        let mut replacements = ExternalTypes(HashMap::new());
        let mut seen = HashSet::new();
        charge(
            work,
            actual_parameters
                .len()
                .checked_mul(2)
                .ok_or_else(resource)?,
        )?;
        replacements
            .0
            .try_reserve(actual_parameters.len())
            .map_err(|_| resource())?;
        seen.try_reserve(actual_parameters.len())
            .map_err(|_| resource())?;
        for ((source, kind), (generated, actual_kind)) in producer
            .scheme
            .type_parameters
            .iter()
            .zip(actual_parameters)
        {
            if !matches!(generated, crate::types::TypeVariableId::Generated(_))
                || !seen.insert(*generated)
                || !crate::types::same_kind_with_charge(kind, actual_kind, || work.charge(1))
                    .map_err(|()| resource())?
            {
                return Err(invalid(variable));
            }
            replacements.insert_discarding_replaced(*source, Type::Variable(*generated));
        }
        let Type::Forall(_, canonical_body) = &*canonical else {
            return Err(invalid(variable));
        };
        let expected = substitute(
            canonical_body,
            &replacements,
            &HashMap::new(),
            variable,
            work,
        )?;
        require_same(&expected, actual_body, variable, work)?;
    }
    Ok(variable)
}

/// Source relation reconstructed only from authenticated imported inputs.
pub(crate) struct ProviderSourceRelation {
    summary: super::super::capture::CaptureValueSummary,
}
impl ProviderSourceRelation {
    pub(crate) fn summary(&self) -> &super::super::capture::CaptureValueSummary {
        &self.summary
    }
    fn check(
        &self,
        actual: &Type,
        allow_owned_scopes: bool,
        work: &mut TypeWorkBudget,
    ) -> Result<(), super::super::capture::Failure> {
        super::super::capture::CaptureValueSummary::check_provider_source_wrapper_call(
            self,
            actual,
            allow_owned_scopes,
            work,
        )
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "canonical source capture reconstruction keeps actual arguments and selected routes explicit"
)]
fn source_capture_relation(
    program: &UnvalidatedEffectProgram,
    global: ProviderGlobalFact<'_>,
    arguments: &[Type],
    rows: &[crate::types::EffectRow],
    selected: &[(
        crate::interface::RequirementId,
        crate::interface::MethodId,
        super::super::capture::MethodTarget,
    )],
    adapters: &[super::super::capture::MethodAdapter],
    facts: ProviderExternalFacts<'_>,
    work: &mut TypeWorkBudget,
) -> Result<ProviderSourceRelation, ValidationError> {
    let mut builder = super::super::CoreBuilder::<super::super::effect::EffectOperationFamily>::with_registry_for_family(std::sync::Arc::clone(&program.registry));
    builder.type_work = TypeWorkBudget::with_limit(work.remaining());
    let result = source_capture_relation_builder(
        program,
        global,
        arguments,
        rows,
        selected,
        adapters,
        facts,
        &mut builder,
        work,
    );
    charge(work, builder.type_work.used())?;
    result.map(|summary| ProviderSourceRelation { summary })
}

fn emit_source_occurrence(
    builder: &mut super::super::CoreBuilder<super::super::effect::EffectOperationFamily>,
    global: ProviderGlobalFact<'_>,
    arguments: &[Type],
    rows: &[crate::types::EffectRow],
    origin: &crate::source::Origin,
    at: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<(NodeId, IterativeTypeOwner), ValidationError> {
    if !super::super::dialect::origin_depth_within_limit(origin) {
        return Err(invalid(at));
    }
    let (types, row_substitutions) =
        substitutions(&global.scheme().type_parameters, arguments, rows, at, work)?;
    let actual = substitute(
        &global.scheme().value_type,
        &types,
        &row_substitutions,
        at,
        work,
    )?;
    actual.function_view().ok_or_else(|| invalid(at))?;
    let mut source_scheme = IterativeTypeOwner::new(
        clone_type_with_budget(&global.scheme().value_type, work).map_err(|()| resource())?,
    );
    if !global.scheme().type_parameters.is_empty() {
        charge(work, 1)?;
        source_scheme = IterativeTypeOwner::new(Type::Forall(
            clone_kinded_type_parameters_with_budget(&global.scheme().type_parameters, work)
                .map_err(|()| resource())?
                .into_boxed_slice(),
            Box::new(source_scheme.into_inner()),
        ));
    }
    let variable_origin = clone_external_origin(origin, work)?;
    let mut occurrence = builder
        .variable(global.binder(), source_scheme.into_inner(), variable_origin)
        .map_err(|_| resource())?;
    if !arguments.is_empty() || !rows.is_empty() {
        let mut retained = IterativeArguments(Vec::new());
        charge(work, arguments.len() + rows.len())?;
        retained
            .0
            .try_reserve_exact(arguments.len())
            .map_err(|_| resource())?;
        for argument in arguments {
            retained
                .0
                .push(clone_type_with_budget(argument, work).map_err(|()| resource())?);
        }
        let mut retained_rows = Vec::new();
        retained_rows
            .try_reserve_exact(rows.len())
            .map_err(|_| resource())?;
        for row in rows {
            retained_rows.push(
                crate::types::clone_effect_row_with_budget(row, work).map_err(|()| resource())?,
            );
        }
        let actual_type = IterativeTypeOwner::new(
            clone_type_with_budget(&actual, work).map_err(|()| resource())?,
        );
        let application_origin = clone_external_origin(origin, work)?;
        occurrence = builder
            .type_application_with_row_arguments(
                occurrence,
                retained.into_vec(),
                retained_rows,
                actual_type.into_inner(),
                application_origin,
            )
            .map_err(|_| resource())?;
    }
    Ok((occurrence, actual))
}

#[expect(
    clippy::too_many_arguments,
    reason = "the bounded builder and caller ledger accompany exact source capture inputs"
)]
fn source_capture_relation_builder(
    program: &UnvalidatedEffectProgram,
    global: ProviderGlobalFact<'_>,
    arguments: &[Type],
    rows: &[crate::types::EffectRow],
    selected: &[(
        crate::interface::RequirementId,
        crate::interface::MethodId,
        super::super::capture::MethodTarget,
    )],
    adapters: &[super::super::capture::MethodAdapter],
    facts: ProviderExternalFacts<'_>,
    builder: &mut super::super::CoreBuilder<super::super::effect::EffectOperationFamily>,
    work: &mut TypeWorkBudget,
) -> Result<super::super::capture::CaptureValueSummary, ValidationError> {
    let at = program.root;
    let origin = &global.origin();
    let (occurrence, actual) =
        emit_source_occurrence(builder, global, arguments, rows, origin, at, work)?;
    let function = actual.function_view().ok_or_else(|| invalid(at))?;
    // Prepare every fallible argument while recursive type owners remain
    // guarded; builder ownership begins only when the call is entered.
    let parameter_origin = clone_external_origin(origin, work)?;
    let parameter_type = IterativeTypeOwner::new(
        clone_type_with_budget(function.domain(), work).map_err(|()| resource())?,
    );
    let parameter = builder
        .binder(parameter_type.into_inner(), parameter_origin)
        .map_err(|_| resource())?;
    let argument_origin = clone_external_origin(origin, work)?;
    let argument_type = IterativeTypeOwner::new(
        clone_type_with_budget(function.domain(), work).map_err(|()| resource())?,
    );
    let argument = builder
        .variable(parameter.id(), argument_type.into_inner(), argument_origin)
        .map_err(|_| resource())?;
    let body_origin = clone_external_origin(origin, work)?;
    let body_type = IterativeTypeOwner::new(
        clone_type_with_budget(function.value(), work).map_err(|()| resource())?,
    );
    let body = builder
        .application(occurrence, argument, body_type.into_inner(), body_origin)
        .map_err(|_| resource())?;
    let wrapper_origin = clone_external_origin(origin, work)?;
    let wrapper = builder
        .function(parameter, body, actual.into_inner(), wrapper_origin)
        .map_err(|_| resource())?;
    let root_origin = clone_external_origin(origin, work)?;
    let root = builder
        .binder(Type::Unit, root_origin)
        .map_err(|_| resource())?;
    let mut routes = Vec::new();
    charge(work, selected.len())?;
    routes
        .try_reserve_exact(selected.len())
        .map_err(|_| resource())?;
    for (requirement, method, target) in selected {
        match *target {
            super::super::capture::MethodTarget::Adapter { value, binder }
                if adapters
                    .get(value)
                    .is_some_and(|producer| producer.binder == binder) => {}
            super::super::capture::MethodTarget::Abstract(_) => {}
            super::super::capture::MethodTarget::NativeLayout(producer)
                if *method == producer.method() => {}
            _ => return Err(invalid(at)),
        }
        routes.push(super::super::capture::MethodUse {
            node: occurrence,
            target: *target,
            method: *method,
            requirement: Some(*requirement),
            arguments: 0,
        });
    }
    let imports = canonical_capture_imports(facts, work)?;
    let mut captures = super::super::capture::check_builder(
        builder,
        &[(root.id(), wrapper)],
        &imports,
        |kind| match kind {
            EffectExprKind::Operation(operation) => Some(operation),
            _ => None,
        },
        &routes,
        adapters,
        work,
    )
    .map_err(|failure| match failure {
        super::super::capture::Failure::Resource => resource(),
        _ => invalid(at),
    })?;
    if captures.len() != 1 {
        return Err(invalid(at));
    }
    captures.pop().ok_or_else(|| invalid(at))
}

fn canonical_capture_imports<'a>(
    facts: ProviderExternalFacts<'a>,
    work: &mut TypeWorkBudget,
) -> Result<Vec<(BinderId, &'a super::super::capture::CaptureValueSummary)>, ValidationError> {
    let mut imports = Vec::new();
    for global in facts.globals() {
        charge(work, 1)?;
        imports.try_reserve(1).map_err(|_| resource())?;
        imports.push((global.binder(), global.capture()));
    }
    for implementation in facts.imported.implementations() {
        charge(work, 1)?;
        for method in &implementation.fact.methods {
            charge(work, 1)?;
            imports.try_reserve(1).map_err(|_| resource())?;
            imports.push((method.binder, &method.capture));
        }
    }
    if let Some(defining) = facts.defining {
        charge(work, defining.implementations.len())?;
        for implementation in &defining.implementations {
            charge(work, implementation.methods.len())?;
            imports
                .try_reserve(implementation.methods.len())
                .map_err(|_| resource())?;
            imports.extend(
                implementation
                    .methods
                    .iter()
                    .map(|method| (method.binder, &method.capture)),
            );
        }
    }
    Ok(imports)
}

fn clone_external_origin(
    origin: &crate::source::Origin,
    work: &mut TypeWorkBudget,
) -> Result<crate::source::Origin, ValidationError> {
    if !super::super::dialect::origin_depth_within_limit(origin) {
        return Err(resource());
    }
    let mut current = origin;
    loop {
        charge(work, 2)?;
        match current {
            crate::source::Origin::Source(_) => break,
            crate::source::Origin::Generated { cause, .. } => current = cause,
            crate::source::Origin::Related { primary, related } => {
                charge(work, related.len().checked_mul(2).ok_or_else(resource)?)?;
                current = primary;
            }
        }
    }
    Ok(origin.clone())
}

#[cfg(test)]
pub(crate) fn external_scheme_for_test(
    program: &UnvalidatedEffectProgram,
    binder: BinderId,
) -> &Type {
    &program.nodes.iter().find(|node| matches!(&node.kind, EffectExprKind::Pure(PureExprKind::Variable(v)) if v.binder() == binder)).unwrap().ty
}

#[cfg(test)]
pub(crate) fn swap_dictionary_methods_for_test(
    program: &mut UnvalidatedEffectProgram,
    root: NodeId,
) {
    let application = |id: NodeId| match &program.nodes[id.value() as usize].kind {
        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(a))) => *a,
        _ => panic!("dictionary chain"),
    };
    let second_id = application(root).function();
    let second = application(second_id);
    let first_id = second.function();
    let first = application(first_id);
    assert!(
        crate::types::same_type_with_budget(
            &program.nodes[first.argument().value() as usize].ty,
            &program.nodes[second.argument().value() as usize].ty,
            &mut TypeWorkBudget::unbounded()
        )
        .unwrap()
    );
    program.nodes[first_id.value() as usize].kind =
        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
            super::super::function::ApplicationNode::new(first.function(), second.argument()),
        )));
    program.nodes[second_id.value() as usize].kind =
        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
            super::super::function::ApplicationNode::new(second.function(), first.argument()),
        )));
}

#[cfg(test)]
pub(crate) fn wrong_dictionary_producer_for_test(
    program: &mut UnvalidatedEffectProgram,
    root: NodeId,
) {
    let apply = |id: NodeId| match &program.nodes[id.value() as usize].kind {
        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(a))) => *a,
        _ => panic!("dictionary chain"),
    };
    let second = apply(apply(root).function());
    let first = apply(second.function());
    let replacement = match &program.nodes[second.argument().value() as usize].kind {
        EffectExprKind::Pure(PureExprKind::Variable(v)) => v.binder(),
        _ => panic!("concrete producer"),
    };
    program.nodes[first.argument().value() as usize].kind = EffectExprKind::Pure(
        PureExprKind::Variable(super::super::variable::VariableNode::new(replacement)),
    );
}

#[cfg(test)]
pub(crate) fn check_external_data_type_for_test(
    program: &UnvalidatedEffectProgram,
    imported: &ImportedFacts,
    ty: &Type,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    closed_data_type(program, imported, ty, program.root, work)
}

#[cfg(test)]
pub(crate) fn mutate_method_catalog_for_test(
    program: &mut UnvalidatedEffectProgram,
    mutation: super::super::dialect::MethodEvidenceCatalogMutationForTest,
) {
    assert!(std::sync::Arc::make_mut(&mut program.method_evidence).corrupt_for_core_test(mutation));
}

#[cfg(test)]
pub(crate) fn mutate_polymorphic_prerequisite_for_test(
    program: &mut UnvalidatedEffectProgram,
    mutation: usize,
) {
    use super::super::dialect::{
        MethodEvidenceAnchorRole, MethodEvidenceExpectedProducer, MethodEvidenceExpectedRole,
    };
    let catalog = &program.method_evidence;
    if mutation == 4 {
        let candidates = program
            .method_evidence_anchors
            .iter()
            .filter_map(|anchor| {
                let MethodEvidenceAnchorRole::AdapterEdge {
                    adapter, ordinal, ..
                } = anchor.role
                else {
                    return None;
                };
                let owner = catalog.implementation_owner(adapter)?;
                if ordinal == 0 || owner.source_parameters.len() != owner.head_type_parameter_count
                {
                    return None;
                }
                let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                    application,
                ))) = &program.nodes[anchor.node.value() as usize].kind
                else {
                    return None;
                };
                Some((anchor.node, adapter, ordinal, *application))
            })
            .collect::<Vec<_>>();
        for (i, (left, owner, ordinal, a)) in candidates.iter().enumerate() {
            for (right, other_owner, other_ordinal, b) in &candidates[i + 1..] {
                if owner == other_owner || ordinal != other_ordinal {
                    continue;
                }
                if !same_type_with_budget(
                    &program.nodes[a.function().value() as usize].ty,
                    &program.nodes[b.function().value() as usize].ty,
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap()
                {
                    continue;
                }
                program.nodes[left.value() as usize].kind =
                    EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                        super::super::function::ApplicationNode::new(b.function(), a.argument()),
                    )));
                program.nodes[right.value() as usize].kind =
                    EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                        super::super::function::ApplicationNode::new(a.function(), b.argument()),
                    )));
                return;
            }
        }
        panic!("equal-typed live passive prerequisite prefixes");
    }
    let index = program
        .method_evidence_anchors
        .iter()
        .position(|anchor| {
            let Some(expected) = catalog.expectations().get(anchor.expectation) else {
                return false;
            };
            let MethodEvidenceExpectedRole::AdapterEdge { adapter, ordinal } = expected.role else {
                return false;
            };
            matches!(
                catalog.adapters()[adapter].prerequisites[ordinal].producer,
                MethodEvidenceExpectedProducer::Authenticated(_)
            )
        })
        .expect("polymorphic prerequisite edge");
    let MethodEvidenceAnchorRole::AdapterEdge {
        producer_selection_node: current_selection,
        ..
    } = program.method_evidence_anchors[index].role
    else {
        unreachable!()
    };
    let replacement_selection = program
        .method_evidence_anchors
        .iter()
        .find_map(|anchor| match anchor.role {
            MethodEvidenceAnchorRole::Adapter { selection_node, .. }
                if selection_node != current_selection =>
            {
                Some(selection_node)
            }
            _ => None,
        })
        .unwrap();
    let anchor = &mut program.method_evidence_anchors[index];
    let MethodEvidenceAnchorRole::AdapterEdge {
        producer_node,
        producer_selection_node,
        ordinal,
        ..
    } = &mut anchor.role
    else {
        unreachable!()
    };
    match mutation {
        0 => *producer_node = program.root,
        1 => {
            assert_ne!(*producer_selection_node, replacement_selection);
            *producer_selection_node = replacement_selection;
        }
        2 => *ordinal += 1,
        3 => {
            anchor.application = crate::interface::InterfaceApplication::new(
                anchor.application.interface(),
                Box::new([Type::Bool]),
            )
        }
        _ => unreachable!(),
    }
}

#[cfg(test)]
pub(crate) fn reuse_dictionary_producer_as_call_for_test(
    program: &mut UnvalidatedEffectProgram,
    root: NodeId,
    mutation: usize,
) {
    use super::super::{
        binding::BindingNode,
        data::{CoreMatchArm, CorePattern, CorePatternKind, MatchNode, TupleNode},
        dialect::StoredNode,
        function::{ApplicationNode, FunctionNode},
        literal::{BooleanNode, UnitNode},
        type_ops::TypeApplicationNode,
        variable::{TypedBinder, VariableNode},
    };
    let mut dictionary_arguments = Vec::new();
    let mut cursor = root;
    while let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(edge))) =
        &program.nodes[cursor.value() as usize].kind
    {
        dictionary_arguments.push(edge.argument());
        cursor = edge.function();
    }
    dictionary_arguments.reverse();
    let first = dictionary_arguments[0];
    let second = dictionary_arguments[1];
    let (call_index, actual) = program
        .nodes
        .iter()
        .enumerate()
        .find_map(|(i, stored)| match &stored.kind {
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(a)))
                if a.function() == root =>
            {
                Some((i, *a))
            }
            _ => None,
        })
        .unwrap();
    let original = NodeId::new(program.arena, call_index as u32);
    let dialect = program.nodes[call_index].dialect;
    let ty = program.nodes[call_index].ty.clone();
    let producer_type = program.nodes[second.value() as usize].ty.clone();
    let origin = program.nodes[call_index].origin.clone().unwrap();
    let arena = program.arena;
    let mut emit = |ty: Type, kind: EffectExprKind| {
        let id = NodeId::new(arena, program.nodes.len() as u32);
        program.nodes.push(StoredNode {
            dialect,
            ty,
            effects: crate::types::EffectRow::empty(),
            origin: Some(origin.clone()),
            kind,
        });
        id
    };
    let pure = |computation| EffectExprKind::Pure(PureExprKind::Computation(computation));
    let alias = TypedBinder::new(
        arena,
        BinderId::generated(100_001),
        producer_type.clone(),
        origin.clone(),
    );
    if mutation == 8 {
        let bound = emit(
            ty,
            pure(PureComputation::Bind(BindingNode::new(
                alias, second, original,
            ))),
        );
        let stored = program.nodes.iter_mut().find(|stored| matches!(&stored.kind, EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(m))) if m.scrutinee() == original)).unwrap();
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(matching))) =
            &stored.kind
        else {
            unreachable!()
        };
        stored.kind = pure(PureComputation::Match(MatchNode::new(
            bound,
            matching.arms().to_vec(),
        )));
        return;
    }
    let (function, argument) = match mutation {
        0 => (second, actual.argument()),
        1 | 3 => (
            emit(
                producer_type.clone(),
                EffectExprKind::Pure(PureExprKind::Variable(VariableNode::new(alias.id()))),
            ),
            actual.argument(),
        ),
        2 => {
            let tuple_type = Type::Tuple(Box::new([ty.clone(), Type::Bool]));
            let function_type = Type::Function(Box::new(tuple_type.clone()), Box::new(ty.clone()));
            let specialized = emit(
                function_type,
                pure(PureComputation::TypeApplication(TypeApplicationNode::new(
                    first,
                    vec![Type::Bool],
                ))),
            );
            let boolean = emit(
                Type::Bool,
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Boolean(BooleanNode::new(
                    true,
                )))),
            );
            let tuple = emit(
                tuple_type,
                pure(PureComputation::Tuple(TupleNode::new(vec![
                    actual.argument(),
                    boolean,
                ]))),
            );
            (specialized, tuple)
        }
        5 => {
            let parameter = TypedBinder::new(
                arena,
                BinderId::generated(100_002),
                producer_type.clone(),
                origin.clone(),
            );
            let body = emit(
                producer_type.clone(),
                EffectExprKind::Pure(PureExprKind::Variable(VariableNode::new(parameter.id()))),
            );
            let identity = emit(
                Type::Function(
                    Box::new(producer_type.clone()),
                    Box::new(producer_type.clone()),
                ),
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(FunctionNode::new(
                    parameter, body,
                )))),
            );
            let laundered = emit(
                producer_type.clone(),
                pure(PureComputation::Apply(ApplicationNode::new(
                    identity, second,
                ))),
            );
            (laundered, actual.argument())
        }
        6 => {
            let body = emit(
                ty.clone(),
                pure(PureComputation::Apply(ApplicationNode::new(
                    second,
                    actual.argument(),
                ))),
            );
            let parameter = TypedBinder::new(
                arena,
                BinderId::generated(100_003),
                Type::Unit,
                origin.clone(),
            );
            let closure = emit(
                Type::Function(Box::new(Type::Unit), Box::new(ty.clone())),
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(FunctionNode::new(
                    parameter, body,
                )))),
            );
            let unit = emit(
                Type::Unit,
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Unit(UnitNode))),
            );
            (closure, unit)
        }
        4 => {
            let boolean = emit(
                Type::Bool,
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Boolean(BooleanNode::new(
                    true,
                )))),
            );
            let arms = [true, false]
                .into_iter()
                .map(|value| {
                    CoreMatchArm::new(
                        CorePattern::new(
                            Type::Bool,
                            origin.clone(),
                            CorePatternKind::Boolean(value),
                        ),
                        second,
                        origin.clone(),
                    )
                })
                .collect();
            (
                emit(
                    producer_type.clone(),
                    pure(PureComputation::Match(MatchNode::new(boolean, arms))),
                ),
                actual.argument(),
            )
        }
        7 => {
            let tuple_type = Type::Tuple(Box::new([producer_type.clone(), Type::Unit]));
            let parameter = TypedBinder::new(
                arena,
                BinderId::generated(100_004),
                tuple_type.clone(),
                origin.clone(),
            );
            let body = emit(
                tuple_type.clone(),
                EffectExprKind::Pure(PureExprKind::Variable(VariableNode::new(parameter.id()))),
            );
            let identity = emit(
                Type::Function(Box::new(tuple_type.clone()), Box::new(tuple_type.clone())),
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(FunctionNode::new(
                    parameter, body,
                )))),
            );
            let unit = emit(
                Type::Unit,
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Unit(UnitNode))),
            );
            let tuple = emit(
                tuple_type.clone(),
                pure(PureComputation::Tuple(TupleNode::new(vec![second, unit]))),
            );
            let laundered = emit(
                tuple_type.clone(),
                pure(PureComputation::Apply(ApplicationNode::new(
                    identity, tuple,
                ))),
            );
            let result = emit(
                producer_type.clone(),
                EffectExprKind::Pure(PureExprKind::Variable(VariableNode::new(alias.id()))),
            );
            let pattern = CorePattern::new(
                tuple_type,
                origin.clone(),
                CorePatternKind::Tuple(
                    vec![
                        CorePattern::new(
                            producer_type.clone(),
                            origin.clone(),
                            CorePatternKind::Binder(alias.clone()),
                        ),
                        CorePattern::new(Type::Unit, origin.clone(), CorePatternKind::Unit),
                    ]
                    .into_boxed_slice(),
                ),
            );
            let projected = emit(
                producer_type.clone(),
                pure(PureComputation::Match(MatchNode::new(
                    laundered,
                    vec![CoreMatchArm::new(pattern, result, origin.clone())],
                ))),
            );
            (projected, actual.argument())
        }
        _ => unreachable!(),
    };
    let called = emit(
        ty.clone(),
        pure(PureComputation::Apply(ApplicationNode::new(
            function, argument,
        ))),
    );
    let called = match mutation {
        1 => emit(
            ty.clone(),
            pure(PureComputation::Bind(BindingNode::new(
                alias, second, called,
            ))),
        ),
        3 => {
            let tuple_type = Type::Tuple(Box::new([producer_type.clone(), Type::Unit]));
            let unit = emit(
                Type::Unit,
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Unit(UnitNode))),
            );
            let tuple = emit(
                tuple_type.clone(),
                pure(PureComputation::Tuple(TupleNode::new(vec![second, unit]))),
            );
            let pattern = CorePattern::new(
                tuple_type,
                origin.clone(),
                CorePatternKind::Tuple(
                    vec![
                        CorePattern::new(
                            producer_type,
                            origin.clone(),
                            CorePatternKind::Binder(alias),
                        ),
                        CorePattern::new(Type::Unit, origin.clone(), CorePatternKind::Unit),
                    ]
                    .into_boxed_slice(),
                ),
            );
            emit(
                ty.clone(),
                pure(PureComputation::Match(MatchNode::new(
                    tuple,
                    vec![CoreMatchArm::new(pattern, called, origin.clone())],
                ))),
            )
        }
        _ => called,
    };
    let ignored = TypedBinder::new(
        arena,
        BinderId::generated(100_000),
        ty.clone(),
        origin.clone(),
    );
    let bound = emit(
        ty,
        pure(PureComputation::Bind(BindingNode::new(
            ignored, original, called,
        ))),
    );
    let stored = program.nodes.iter_mut().find(|stored| matches!(&stored.kind, EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(m))) if m.scrutinee() == original)).unwrap();
    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(matching))) =
        &stored.kind
    else {
        unreachable!()
    };
    stored.kind = pure(PureComputation::Match(MatchNode::new(
        bound,
        matching.arms().to_vec(),
    )));
}

#[cfg(test)]
pub(crate) fn redirect_local_source_call_for_test(
    program: &mut UnvalidatedEffectProgram,
    original_root: NodeId,
    replacement_root: NodeId,
) {
    use super::super::{
        binding::BindingNode,
        dialect::StoredNode,
        function::{ApplicationNode, FunctionNode},
        variable::TypedBinder,
    };
    let (index, application) = program
        .nodes
        .iter()
        .enumerate()
        .find_map(|(index, node)| match &node.kind {
            EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(call)))
                if call.function() == original_root =>
            {
                Some((index, *call))
            }
            _ => None,
        })
        .unwrap();
    let original = NodeId::new(program.arena, index as u32);
    let dialect = program.nodes[index].dialect;
    let ty = program.nodes[index].ty.clone();
    let origin = program.nodes[index].origin.clone().unwrap();
    let called = NodeId::new(program.arena, program.nodes.len() as u32);
    program.nodes.push(StoredNode {
        dialect,
        ty: ty.clone(),
        effects: crate::types::EffectRow::empty(),
        origin: Some(origin.clone()),
        kind: EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
            ApplicationNode::new(replacement_root, application.argument()),
        ))),
    });
    let bound = NodeId::new(program.arena, program.nodes.len() as u32);
    program.nodes.push(StoredNode {
        dialect,
        ty: ty.clone(),
        effects: crate::types::EffectRow::empty(),
        origin: Some(origin.clone()),
        kind: EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(
            BindingNode::new(
                TypedBinder::new(program.arena, BinderId::generated(300_001), ty, origin),
                original,
                called,
            ),
        ))),
    });
    let function = program.nodes.iter_mut().find(|node| matches!(&node.kind, EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) if function.body() == original)).unwrap();
    let EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(target))) = &function.kind
    else {
        unreachable!()
    };
    function.kind = EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(
        FunctionNode::new(target.parameter().clone(), bound),
    )));
}

#[cfg(test)]
pub(crate) fn put_state_access_in_local_callable_for_test(
    program: &mut UnvalidatedEffectProgram,
    unused: bool,
) {
    use super::super::{
        binding::BindingNode, dialect::StoredNode, function::FunctionNode, literal::UnitNode,
        variable::TypedBinder,
    };
    let access = program
        .nodes
        .iter()
        .position(|node| {
            matches!(
                node.kind,
                EffectExprKind::Operation(EffectOperation::ProviderStateAccess(_))
            )
        })
        .unwrap();
    let target = program
        .nodes
        .iter()
        .position(|node| {
            matches!(
                &node.kind,
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function)))
                    if function.parameter().ty() == &Type::String
            )
        })
        .expect("the constrained statement fixture has a packed String forwarder");
    let dialect = program.nodes[target].dialect;
    let origin = program.nodes[target].origin.clone().unwrap();
    let EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(function))) =
        &program.nodes[target].kind
    else {
        unreachable!()
    };
    let parameter = function.parameter().clone();
    let body = function.body();
    let body_type = program.nodes[body.value() as usize].ty.clone();
    let access_type = program.nodes[access].ty.clone();
    let arena = program.arena;
    let mut emit = |ty, kind| {
        let id = NodeId::new(arena, program.nodes.len() as u32);
        program.nodes.push(StoredNode {
            dialect,
            ty,
            effects: crate::types::EffectRow::empty(),
            origin: Some(origin.clone()),
            kind,
        });
        id
    };
    let pure = |computation| EffectExprKind::Pure(PureExprKind::Computation(computation));
    let (initializer, continuation, binder_type) = if unused {
        let unit = emit(
            Type::Unit,
            EffectExprKind::Pure(PureExprKind::Value(PureValue::Unit(UnitNode))),
        );
        let action = emit(
            Type::Unit,
            pure(PureComputation::Bind(BindingNode::new(
                TypedBinder::new(
                    arena,
                    BinderId::generated(300_002),
                    access_type,
                    origin.clone(),
                ),
                NodeId::new(arena, access as u32),
                unit,
            ))),
        );
        let ty = Type::Function(Box::new(Type::Unit), Box::new(Type::Unit));
        let closure = emit(
            ty.clone(),
            EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(FunctionNode::new(
                TypedBinder::new(
                    arena,
                    BinderId::generated(300_003),
                    Type::Unit,
                    origin.clone(),
                ),
                action,
            )))),
        );
        (closure, body, ty)
    } else {
        (NodeId::new(arena, access as u32), body, access_type)
    };
    let bound = emit(
        body_type,
        pure(PureComputation::Bind(BindingNode::new(
            TypedBinder::new(
                arena,
                BinderId::generated(300_004),
                binder_type,
                origin.clone(),
            ),
            initializer,
            continuation,
        ))),
    );
    program.nodes[target].kind = EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(
        FunctionNode::new(parameter, bound),
    )));
}

#[cfg(test)]
pub(crate) fn source_wrapper_origin_prefixes_for_test(
    program: &UnvalidatedEffectProgram,
    global: ProviderGlobalFact<'_>,
    arguments: &[Type],
) -> ([usize; 4], [usize; 4]) {
    let mut builder = super::super::CoreBuilder::<super::super::effect::EffectOperationFamily>::with_registry_for_family(std::sync::Arc::clone(&program.registry));
    builder.type_work = TypeWorkBudget::unbounded();
    let mut work = TypeWorkBudget::unbounded();
    let (_, actual) = emit_source_occurrence(
        &mut builder,
        global,
        arguments,
        &[],
        global.origin(),
        program.root,
        &mut work,
    )
    .unwrap();
    let emission = work.used();
    let function = actual.function_view().unwrap();
    let mut clone = TypeWorkBudget::unbounded();
    drop(IterativeTypeOwner::new(
        clone_type_with_budget(function.domain(), &mut clone).unwrap(),
    ));
    let domain = clone.used();
    let mut clone = TypeWorkBudget::unbounded();
    drop(IterativeTypeOwner::new(
        clone_type_with_budget(function.value(), &mut clone).unwrap(),
    ));
    let result = clone.used();
    let mut clone = TypeWorkBudget::unbounded();
    drop(clone_external_origin(global.origin(), &mut clone).unwrap());
    let origin = clone.used();
    // Caller ledger only: builder admissions use their separate ledger.
    let legacy = [
        emission + domain,
        emission + 2 * domain + origin,
        emission + 2 * domain + 2 * origin + result,
        emission + 2 * domain + 3 * origin + result,
    ];
    let guarded = [
        emission,
        emission + domain + origin,
        emission + 2 * domain + 2 * origin,
        emission + 2 * domain + 3 * origin + result,
    ];
    (legacy, guarded)
}

#[cfg(test)]
pub(crate) fn source_wrapper_for_test(
    program: &UnvalidatedEffectProgram,
    global: ProviderGlobalFact<'_>,
    arguments: &[Type],
    imported: &ImportedFacts,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let mut builder = super::super::CoreBuilder::<super::super::effect::EffectOperationFamily>::with_registry_for_family(std::sync::Arc::clone(&program.registry));
    builder.type_work = TypeWorkBudget::unbounded();
    source_capture_relation_builder(
        program,
        global,
        arguments,
        &[],
        &[],
        &[],
        ProviderExternalFacts {
            imported,
            defining: None,
        },
        &mut builder,
        work,
    )
    .map(drop)
}

/// Immutable defining facts owned by a conditional handler template. These
/// records retain checked imports, not resolved expressions or source bodies.
pub(crate) struct RetainedHandlerExternals {
    catalog: std::sync::Arc<super::super::dialect::MethodEvidenceCatalog>,
    evidence_anchors: Vec<RetainedHandlerEvidenceAnchor>,
    dictionary_nodes: Vec<(NodeId, RetainedHandlerDictionaryNode)>,
    types: HashMap<BinderId, IterativeTypeOwner>,
    globals: Vec<RetainedHandlerGlobal>,
    implementations: Vec<crate::resolved::ImportedImplementationFact>,
    defining_implementations: Vec<crate::resolved::CheckedImplementationFact>,
    occurrences: Vec<RetainedHandlerOccurrence>,
    methods: Vec<RetainedHandlerMethod>,
    // These private records are produced only after reconstructing the full
    // original family scope and its immutable method catalogue.
    family: Option<super::ProviderFamilyIdentity>,
    dictionary_formals: HashMap<BinderId, IterativeTypeOwner>,
    dictionary_edges: HashMap<NodeId, (BinderId, NodeId)>,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum RetainedHandlerDictionaryNode {
    Variable(BinderId),
    Application(NodeId, NodeId),
}
fn retained_dictionary_node(
    program: &UnvalidatedEffectProgram,
    id: NodeId,
) -> Result<RetainedHandlerDictionaryNode, ValidationError> {
    match &node(program, id)?.kind {
        EffectExprKind::Pure(PureExprKind::Variable(variable)) => {
            Ok(RetainedHandlerDictionaryNode::Variable(variable.binder()))
        }
        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(application))) => {
            Ok(RetainedHandlerDictionaryNode::Application(
                application.function(),
                application.argument(),
            ))
        }
        _ => Err(invalid(id)),
    }
}

/// Original checked occurrence/producer routing, without an expression body.
struct RetainedHandlerEvidenceAnchor {
    fact: super::super::dialect::MethodEvidenceAnchor,
    application_edge: Option<(NodeId, NodeId)>,
}

impl RetainedHandlerExternals {
    pub(crate) fn visit_semantic_type_variables(
        &self,
        uses: &mut crate::core::validate::semantic_type_variables::UnusedVariables<'_>,
    ) -> Result<(), ()> {
        uses.catalog(&self.catalog)?;
        uses.charge(
            self.evidence_anchors.len()
                + self.types.len()
                + self.dictionary_formals.len()
                + self.implementations.len()
                + self.defining_implementations.len()
                + self.methods.len()
                + self.occurrences.len(),
        )?;
        for anchor in &self.evidence_anchors {
            uses.application(&anchor.fact.application)?;
        }
        for ty in self.types.values().chain(self.dictionary_formals.values()) {
            uses.ty(ty)?;
        }
        for implementation in &self.implementations {
            implementation.fact.visit_semantic_type_variables(uses)?;
        }
        for implementation in &self.defining_implementations {
            implementation.visit_semantic_type_variables(uses)?;
        }
        for method in &self.methods {
            method.slot.visit_semantic_type_variables(uses)?;
        }
        for occurrence in &self.occurrences {
            uses.ty(&occurrence.callable_type)?;
            uses.charge(
                occurrence.checked_evidence.len()
                    + occurrence.slots.len()
                    + occurrence.arguments.0.len()
                    + occurrence.rows.len(),
            )?;
            for (application, selection) in &occurrence.checked_evidence {
                uses.application(application)?;
                uses.selection(selection)?;
            }
            for slot in &occurrence.slots {
                slot.visit_semantic_type_variables(uses)?;
            }
            for argument in &occurrence.arguments.0 {
                uses.ty(argument)?;
            }
            for row in &occurrence.rows {
                uses.row(row)?;
            }
        }
        if let Some(family) = self.family {
            uses.id(family.parameter)?;
        }
        Ok(())
    }
    pub(in crate::core) fn original_evidence_slots(
        &self,
    ) -> impl Iterator<Item = &crate::interface::EvidenceSlot> {
        self.occurrences
            .iter()
            .flat_map(|occurrence| occurrence.slots.iter())
            .chain(self.methods.iter().map(|method| &method.slot))
    }
    pub(in crate::core) fn original_catalog(
        &self,
    ) -> &std::sync::Arc<super::super::dialect::MethodEvidenceCatalog> {
        &self.catalog
    }
    /// Retention can recognize only the exact original Abstract plan already
    /// authenticated against the borrowed family scope. A specialized plan or
    /// a newly selected plan must use the separate final admission path.
    fn original_family_selection(
        &self,
        slot: usize,
        selection: &crate::interface::EvidenceSelection,
        application: &crate::interface::InterfaceApplication,
        at: NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        let Some(crate::interface::EvidenceNode::Abstract { requirement, .. }) =
            selection.node(selection.root())
        else {
            return Ok(false);
        };
        let family = self.family.ok_or_else(|| invalid(at))?;
        charge(work, self.catalog.occurrence_count())?;
        let original = self.catalog.occurrence(slot).ok_or_else(|| invalid(at))?;
        if original.scope
            != Some(super::super::dialect::MethodEvidenceOwner::ResourceFamily(
                family.definition,
            ))
            || requirement.owner()
                != crate::interface::RequirementOwner::ResourceFamily(family.definition)
            || !selection.shares_plan_with(&original.selection)
            || selection.root() != original.selection.root()
            || application.interface() != original.checked_application.interface()
            || application.arguments().len() != original.checked_application.arguments().len()
        {
            return Err(invalid(at));
        }
        charge(work, application.arguments().len())?;
        for (expected, actual) in original
            .checked_application
            .arguments()
            .iter()
            .zip(application.arguments())
        {
            require_same_argument(expected, actual, at, work)?;
        }
        Ok(true)
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "the original immutable catalogue and published method coordinates are independently compared"
    )]
    fn authenticate_method_coordinates(
        &self,
        retained: &RetainedHandlerMethod,
        method: crate::interface::MethodId,
        application: &crate::interface::InterfaceApplication,
        arguments: &[Type],
        value_type: &Type,
        selection: &crate::interface::EvidenceSelection,
        at: NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        charge(work, self.catalog.occurrence_count())?;
        let original = self
            .catalog
            .occurrence(retained.slot.storage_id())
            .ok_or_else(|| invalid(at))?;
        if method != retained.method
            || original.checked_method != Some(method)
            || !selection.same_original_owner(&original.selection)
            || application.interface() != original.checked_application.interface()
            || application.arguments().len() != original.checked_application.arguments().len()
            || arguments.len() != original.method_arguments.len()
            || original.scope
                != self.family.map(|family| {
                    super::super::dialect::MethodEvidenceOwner::ResourceFamily(family.definition)
                })
        {
            return Err(invalid(at));
        }
        charge(
            work,
            application
                .arguments()
                .len()
                .checked_add(arguments.len())
                .ok_or_else(resource)?,
        )?;
        for (expected, actual) in original
            .checked_application
            .arguments()
            .iter()
            .zip(application.arguments())
        {
            require_same_argument(expected, actual, at, work)?;
        }
        for (expected, actual) in original.method_arguments.iter().zip(arguments) {
            require_same(expected, actual, at, work)?;
        }
        require_same(
            original
                .checked_value_type
                .as_ref()
                .ok_or_else(|| invalid(at))?,
            value_type,
            at,
            work,
        )?;
        self.original_family_selection(retained.slot.storage_id(), selection, application, at, work)
    }

    pub(crate) fn authenticate_publication(
        &self,
        committed: bool,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        charge(work, self.occurrences.len())?;
        for occurrence in &self.occurrences {
            charge(work, occurrence.slots.len())?;
            if occurrence.slots.len() != occurrence.checked_evidence.len() {
                return Err(invalid(occurrence.node));
            }
            for (slot, (expected, selected)) in
                occurrence.slots.iter().zip(&occurrence.checked_evidence)
            {
                if !committed {
                    if slot.selection().is_some() {
                        return Err(invalid(occurrence.node));
                    }
                    continue;
                }
                let (actual, selection) = slot.filled().ok_or_else(|| invalid(occurrence.node))?;
                if actual.interface() != expected.interface()
                    || actual.arguments().len() != expected.arguments().len()
                    || !selection.same_original_owner(selected)
                {
                    return Err(invalid(occurrence.node));
                }
                self.original_family_selection(
                    slot.storage_id(),
                    selection,
                    actual,
                    occurrence.node,
                    work,
                )?;
                charge(work, expected.arguments().len())?;
                for (expected, actual) in expected.arguments().iter().zip(actual.arguments()) {
                    require_same_argument(expected, actual, occurrence.node, work)?;
                }
            }
        }
        charge(work, self.methods.len())?;
        for method in &self.methods {
            let at = method.node;
            if !committed {
                if method.slot.selection().is_some() {
                    return Err(invalid(at));
                }
                continue;
            }
            let (id, application, arguments, value_type, selection) =
                method.slot.filled_method().ok_or_else(|| invalid(at))?;
            self.authenticate_method_coordinates(
                method,
                id,
                application,
                arguments,
                value_type,
                selection,
                at,
                work,
            )?;
        }
        Ok(())
    }

    /// Revalidates the frozen original selections against their exact pending
    /// publication. This borrows preparation evidence and creates no authority.
    pub(crate) fn authenticate_pending(
        &self,
        publication: &crate::evidence::PendingEvidencePublication,
        facts: ProviderExternalFacts<'_>,
        canonical: &crate::resolved::ResolvedRegistry,
        module: ModuleId,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        charge(work, self.occurrences.len())?;
        for occurrence in &self.occurrences {
            charge(work, occurrence.slots.len())?;
            if occurrence.slots.len() != occurrence.checked_evidence.len() {
                return Err(invalid(occurrence.node));
            }
            for (slot, (expected, selected)) in
                occurrence.slots.iter().zip(&occurrence.checked_evidence)
            {
                if slot.selection().is_some() {
                    return Err(invalid(occurrence.node));
                }
                let pending = publication
                    .occurrence(slot.storage_id(), None, work)
                    .map_err(|failure| match failure {
                        crate::evidence::SelectionFailure::TypeResource => resource(),
                        _ => invalid(occurrence.node),
                    })?;
                if pending.method.is_some()
                    || pending.value_type.is_some()
                    || !pending.method_arguments.is_empty()
                    || !pending.selection.same_original_owner(selected)
                    || pending.application.interface() != expected.interface()
                    || pending.application.arguments().len() != expected.arguments().len()
                {
                    return Err(invalid(occurrence.node));
                }
                for (expected, actual) in expected
                    .arguments()
                    .iter()
                    .zip(pending.application.arguments())
                {
                    require_same_argument(expected, actual, occurrence.node, work)?;
                }
                if self.original_family_selection(
                    slot.storage_id(),
                    pending.selection,
                    pending.application,
                    occurrence.node,
                    work,
                )? {
                    continue;
                }
                let mut constraints =
                    crate::interface::InterfaceConstraintBudget::with_limit(work.remaining());
                let result = crate::evidence_validation::validate_provider_closed_selection(
                    facts,
                    canonical,
                    module,
                    pending.selection,
                    pending.application,
                    &mut constraints,
                    work,
                    occurrence.origin.as_origin().primary_span(),
                );
                charge(work, constraints.used())?;
                result.map_err(|failure| match failure.reason() {
                    crate::evidence_validation::EvidenceValidationReason::ConstraintResourceExhausted
                    | crate::evidence_validation::EvidenceValidationReason::TypeResourceExhausted => resource(),
                    _ => invalid(occurrence.node),
                })?;
            }
        }
        charge(work, self.methods.len())?;
        for method in &self.methods {
            if method.slot.selection().is_some() {
                return Err(invalid(method.node));
            }
            let pending = publication
                .occurrence(method.slot.storage_id(), Some(method.method), work)
                .map_err(|failure| match failure {
                    crate::evidence::SelectionFailure::TypeResource => resource(),
                    _ => invalid(method.node),
                })?;
            if self.authenticate_method_coordinates(
                method,
                pending.method.ok_or_else(|| invalid(method.node))?,
                pending.application,
                pending.method_arguments,
                pending.value_type.ok_or_else(|| invalid(method.node))?,
                pending.selection,
                method.node,
                work,
            )? {
                continue;
            }
            let mut constraints =
                crate::interface::InterfaceConstraintBudget::with_limit(work.remaining());
            let result = crate::evidence_validation::validate_provider_closed_selection(
                facts,
                canonical,
                module,
                pending.selection,
                pending.application,
                &mut constraints,
                work,
                method.origin.as_origin().primary_span(),
            );
            charge(work, constraints.used())?;
            result.map_err(|failure| match failure.reason() {
                crate::evidence_validation::EvidenceValidationReason::ConstraintResourceExhausted
                | crate::evidence_validation::EvidenceValidationReason::TypeResourceExhausted => resource(),
                _ => invalid(method.node),
            })?;
        }
        Ok(())
    }

    pub(crate) fn defining_origins(&self) -> impl Iterator<Item = &crate::source::Origin> {
        self.globals
            .iter()
            .map(|global| global.origin.as_origin())
            .chain(
                self.occurrences
                    .iter()
                    .map(|occurrence| occurrence.origin.as_origin()),
            )
            .chain(self.methods.iter().map(|method| method.origin.as_origin()))
            .chain(self.implementations.iter().flat_map(|implementation| {
                std::iter::once(&implementation.fact.origin).chain(
                    implementation
                        .fact
                        .methods
                        .iter()
                        .map(|method| &method.origin),
                )
            }))
            .chain(
                self.defining_implementations
                    .iter()
                    .flat_map(|implementation| {
                        std::iter::once(&implementation.origin)
                            .chain(implementation.methods.iter().map(|method| &method.origin))
                    }),
            )
    }

    /// Authenticates the exact original occurrence owners carried by the code.
    /// The shared one-shot slots may still be pending in the defining transaction;
    /// only that transaction's final commit exposes the owner through exports.
    pub(crate) fn authenticate_owners<'a>(
        &self,
        program: &UnvalidatedEffectProgram,
        occurrences: impl IntoIterator<Item = (NodeId, &'a crate::resolved::ResolvedOccurrence)>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        // Retention already authenticated this immutable catalogue. Exact
        // allocation identity proves equality; actual graph and authority
        // reconstruction below still run for every owning occurrence.
        charge(work, 1)?;
        if !std::sync::Arc::ptr_eq(&self.catalog, &program.method_evidence)
            && !super::super::dialect::same_imported_method_evidence_catalog(
                &self.catalog,
                &program.method_evidence,
                work,
            )
            .map_err(|()| resource())?
        {
            return Err(invalid(program.root));
        }
        charge(work, self.evidence_anchors.len())?;
        if self.evidence_anchors.len() != program.method_evidence_anchors.len() {
            return Err(invalid(program.root));
        }
        for (retained, actual) in self
            .evidence_anchors
            .iter()
            .zip(&program.method_evidence_anchors)
        {
            let expected = &retained.fact;
            if expected.node != actual.node
                || expected.owner != actual.owner
                || expected.requirement != actual.requirement
                || expected.method != actual.method
                || expected.role != actual.role
                || expected.occurrence != actual.occurrence
                || expected.expectation != actual.expectation
                || expected.application.interface() != actual.application.interface()
                || expected.application.arguments().len() != actual.application.arguments().len()
            {
                return Err(invalid(actual.node));
            }
            charge(work, expected.application.arguments().len())?;
            for (left, right) in expected
                .application
                .arguments()
                .iter()
                .zip(actual.application.arguments())
            {
                if !crate::types::same_kinded_argument_with_budget(left, right, work)
                    .map_err(|()| resource())?
                {
                    return Err(invalid(actual.node));
                }
            }
            charge(work, 1)?;
            let edge = match &node(program, actual.node)?.kind {
                EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                    application,
                ))) => Some((application.function(), application.argument())),
                _ => None,
            };
            if edge != retained.application_edge {
                return Err(invalid(actual.node));
            }
        }
        charge(work, self.dictionary_nodes.len())?;
        for (id, expected) in &self.dictionary_nodes {
            if retained_dictionary_node(program, *id)? != *expected {
                return Err(invalid(*id));
            }
            if let RetainedHandlerDictionaryNode::Variable(binder) = expected {
                require_same(
                    self.types
                        .get(binder)
                        .or_else(|| self.dictionary_formals.get(binder))
                        .ok_or_else(|| invalid(*id))?,
                    &node(program, *id)?.ty,
                    *id,
                    work,
                )?;
            }
        }
        charge(work, self.dictionary_edges.len())?;
        for (id, (_, previous)) in &self.dictionary_edges {
            if !matches!(&node(program, *id)?.kind,
                EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(application)))
                    if application.function() == *previous)
            {
                return Err(invalid(*id));
            }
        }
        charge(work, self.occurrences.len())?;
        let mut seen = HashSet::new();
        seen.try_reserve(self.occurrences.len())
            .map_err(|_| resource())?;
        let mut count = 0usize;
        for (id, source) in occurrences {
            charge(work, 1)?;
            if !seen.insert(id) {
                return Err(invalid(id));
            }
            charge(work, self.occurrences.len())?;
            let retained = self
                .occurrences
                .iter()
                .find(|entry| entry.node == id)
                .ok_or_else(|| invalid(id))?;
            count = count.checked_add(1).ok_or_else(resource)?;
            charge(
                work,
                retained
                    .spelling
                    .len()
                    .checked_add(source.spelling.len())
                    .ok_or_else(resource)?,
            )?;
            if retained.term != source.term
                || retained.spelling != source.spelling
                || retained.import_span != source.import_span
                || retained.slots.len() != source.evidence.len()
                || !crate::resolved::same_origin_with_budget(
                    retained.origin.0.as_ref().ok_or_else(|| invalid(id))?,
                    &source.origin,
                    work,
                )
                .map_err(|()| resource())?
            {
                return Err(invalid(id));
            }
            let mut head = id;
            for step in 0..=program.nodes.len() {
                charge(work, 1)?;
                if step == program.nodes.len() {
                    return Err(invalid(head));
                }
                match &node(program, head)?.kind {
                    EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                        application,
                    ))) => head = application.function(),
                    _ => break,
                }
            }
            let variable = if retained.arguments.0.is_empty() && retained.rows.is_empty() {
                head
            } else {
                let EffectExprKind::Pure(PureExprKind::Computation(
                    PureComputation::TypeApplication(application),
                )) = &node(program, head)?.kind
                else {
                    return Err(invalid(head));
                };
                compare_actual_arguments(
                    application.arguments(),
                    application.row_arguments(),
                    &retained.arguments.0,
                    &retained.rows,
                    head,
                    work,
                )?;
                application.function()
            };
            if !matches!(&node(program, variable)?.kind,
                EffectExprKind::Pure(PureExprKind::Variable(actual)) if actual.binder() == retained.binder)
            {
                return Err(invalid(variable));
            }
            require_same(
                self.types
                    .get(&retained.binder)
                    .ok_or_else(|| invalid(variable))?,
                &node(program, variable)?.ty,
                variable,
                work,
            )?;
            require_same(&retained.callable_type, &node(program, id)?.ty, id, work)?;
            charge(work, retained.slots.len())?;
            for (canonical, actual) in retained.slots.iter().zip(&source.evidence) {
                if canonical.storage_id() != actual.storage_id() {
                    return Err(invalid(id));
                }
            }
        }
        if count != self.occurrences.len() {
            return Err(invalid(program.root));
        }
        Ok(())
    }
}

// Source type/capture relations are retained in their authenticated occurrence
// records. The global inventory contributes only original source origins here.
struct RetainedHandlerGlobal {
    origin: RetainedHandlerOrigin,
}

struct RetainedHandlerMethod {
    node: NodeId,
    method: crate::interface::MethodId,
    slot: crate::interface::EvidenceSlot,
    origin: RetainedHandlerOrigin,
}

struct RetainedHandlerOccurrence {
    checked_evidence: Vec<(
        crate::interface::InterfaceApplication,
        crate::interface::EvidenceSelection,
    )>,
    slots: Vec<crate::interface::EvidenceSlot>,
    node: NodeId,
    callable_type: IterativeTypeOwner,
    binder: BinderId,
    arguments: IterativeArguments,
    rows: Vec<crate::types::EffectRow>,
    spelling: String,
    origin: RetainedHandlerOrigin,
    import_span: Option<crate::source::Span>,
    term: crate::resolved::ResolvedTermName,
}

#[derive(Debug)]
pub(crate) struct RetainedHandlerOrigin(Option<crate::source::Origin>);
impl RetainedHandlerOrigin {
    pub(crate) fn as_origin(&self) -> &crate::source::Origin {
        self.0
            .as_ref()
            .expect("a retained origin remains owned until drop")
    }
    pub(crate) fn copy(
        origin: &crate::source::Origin,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        Ok(Self(Some(clone_external_origin(origin, work)?)))
    }
}
impl Drop for RetainedHandlerOrigin {
    fn drop(&mut self) {
        if let Some(origin) = self.0.take() {
            crate::source::discard_origin_iteratively(origin);
        }
    }
}

fn retain_handler_string(
    value: &str,
    work: &mut TypeWorkBudget,
) -> Result<String, ValidationError> {
    charge(work, value.len())?;
    let mut result = String::new();
    result
        .try_reserve_exact(value.len())
        .map_err(|_| resource())?;
    result.push_str(value);
    Ok(result)
}

fn retain_handler_requirement(
    value: &crate::interface::CheckedRequirement,
    work: &mut TypeWorkBudget,
) -> Result<crate::interface::CheckedRequirement, ValidationError> {
    charge(work, 1)?;
    Ok(crate::interface::CheckedRequirement {
        id: value.id,
        application: value
            .application()
            .clone_with_budget(work)
            .map_err(|()| resource())?,
        origin: clone_external_origin(&value.origin, work)?,
        span: value.span,
    })
}

fn retain_handler_scheme(
    value: &crate::interface::ConstrainedScheme,
    work: &mut TypeWorkBudget,
) -> Result<crate::interface::ConstrainedScheme, ValidationError> {
    let type_parameters = clone_kinded_type_parameters_with_budget(&value.type_parameters, work)
        .map_err(|()| resource())?;
    charge(work, value.requirements.len())?;
    let mut requirements = Vec::new();
    requirements
        .try_reserve_exact(value.requirements.len())
        .map_err(|_| resource())?;
    for requirement in &value.requirements {
        requirements.push(retain_handler_requirement(requirement, work)?);
    }
    Ok(crate::interface::ConstrainedScheme {
        type_parameters: type_parameters.into_boxed_slice(),
        requirements: requirements.into_boxed_slice(),
        value_type: clone_type_with_budget(value.value_type(), work).map_err(|()| resource())?,
    })
}

fn retain_handler_authorization(
    value: &crate::resolved::ImplementationAuthorization,
    work: &mut TypeWorkBudget,
) -> Result<crate::resolved::ImplementationAuthorization, ValidationError> {
    let mut constraints = crate::interface::InterfaceConstraintBudget::with_limit(work.remaining());
    let result = value.clone_with_budget(&mut constraints);
    charge(work, constraints.used())?;
    result.map_err(|()| resource())
}

impl AuthenticatedProviderExternals<'_> {
    pub(in crate::core) fn retain_handler(
        self,
        entry: &super::HandlerFragmentEntry<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<RetainedHandlerExternals, ValidationError> {
        if !std::ptr::eq(self.program, &entry.draft.program)
            || self
                .entry
                .is_none_or(|original| !std::ptr::eq(original, entry))
        {
            return Err(invalid(entry.draft.program.root));
        }
        let mut originals = HashMap::new();
        charge(work, self.source_occurrences.len())?;
        originals
            .try_reserve(self.source_occurrences.len())
            .map_err(|_| resource())?;
        for id in self.source_occurrences.keys() {
            let origin = node(self.program, *id)?
                .origin
                .as_ref()
                .ok_or_else(|| invalid(*id))?;
            let mut primary = origin;
            let span = loop {
                charge(work, 1)?;
                match primary {
                    crate::source::Origin::Source(span) => break *span,
                    crate::source::Origin::Generated { cause, .. } => primary = cause,
                    crate::source::Origin::Related { primary: cause, .. } => primary = cause,
                }
            };
            originals.insert(*id, *entry.imports.get(&span).ok_or_else(|| invalid(*id))?);
        }
        self.retain_defining_externals(&originals, work)
    }

    pub(crate) fn retain_lifecycle(
        self,
        program: &UnvalidatedEffectProgram,
        originals: &HashMap<NodeId, &crate::resolved::ResolvedOccurrence>,
        work: &mut TypeWorkBudget,
    ) -> Result<RetainedHandlerExternals, ValidationError> {
        if !std::ptr::eq(self.program, program) || self.entry.is_some() {
            return Err(invalid(program.root));
        }
        self.retain_defining_externals(originals, work)
    }

    fn retain_defining_externals(
        self,
        originals: &HashMap<NodeId, &crate::resolved::ResolvedOccurrence>,
        work: &mut TypeWorkBudget,
    ) -> Result<RetainedHandlerExternals, ValidationError> {
        if originals.len() != self.source_occurrences.len() {
            return Err(invalid(self.program.root));
        }
        let mut globals = Vec::new();
        for global in self.facts().globals() {
            charge(work, 1)?;
            globals.try_reserve(1).map_err(|_| resource())?;
            globals.push(RetainedHandlerGlobal {
                origin: RetainedHandlerOrigin::copy(global.origin(), work)?,
            });
        }
        let mut implementations = Vec::new();
        for imported in self.imported.implementations() {
            charge(work, 2)?;
            implementations.try_reserve(1).map_err(|_| resource())?;
            let publication = std::sync::Arc::clone(
                imported
                    .publication
                    .as_ref()
                    .ok_or_else(|| invalid(self.program.root))?,
            );
            let fact = &imported.fact;
            let mut head_parameters = RetainedHandlerParameters(Vec::new());
            charge(work, fact.head_parameters.len())?;
            head_parameters
                .0
                .try_reserve_exact(fact.head_parameters.len())
                .map_err(|_| resource())?;
            for parameter in &fact.head_parameters {
                head_parameters
                    .0
                    .push(crate::resolved::ResolvedTypeVariable {
                        id: parameter.id,
                        spelling: retain_handler_string(&parameter.spelling, work)?,
                        kind: crate::types::clone_kind_with_budget(&parameter.kind, work)
                            .map_err(|()| resource())?,
                        origin: clone_external_origin(&parameter.origin, work)?,
                    });
            }
            let mut prerequisites = Vec::new();
            charge(work, fact.prerequisites.len())?;
            prerequisites
                .try_reserve_exact(fact.prerequisites.len())
                .map_err(|_| resource())?;
            for prerequisite in &fact.prerequisites {
                prerequisites.push(retain_handler_requirement(prerequisite, work)?);
            }
            let mut methods = Vec::new();
            charge(work, fact.methods.len())?;
            methods
                .try_reserve_exact(fact.methods.len())
                .map_err(|_| resource())?;
            for method in &fact.methods {
                methods.push(crate::resolved::CheckedImplementationMethodFact {
                    capture: method
                        .capture
                        .clone_with_budget(work)
                        .map_err(|()| resource())?,
                    id: method.id,
                    method: method.method,
                    binder: method.binder,
                    scheme: retain_handler_scheme(&method.scheme, work)?,
                    head_type_parameter_count: method.head_type_parameter_count,
                    origin: clone_external_origin(&method.origin, work)?,
                    span: method.span,
                });
            }
            let application = fact
                .application()
                .clone_with_budget(work)
                .map_err(|()| resource())?;
            let origin = clone_external_origin(&fact.origin, work)?;
            let retained = crate::resolved::CheckedImplementationFact {
                id: fact.id,
                application,
                head_parameters: std::mem::take(&mut head_parameters.0).into_boxed_slice(),
                prerequisites: prerequisites.into_boxed_slice(),
                methods: methods.into_boxed_slice(),
                origin,
                span: fact.span,
            };
            implementations.push(crate::resolved::ImportedImplementationFact {
                publication: Some(publication),
                fact: retained,
                authorization: retain_handler_authorization(&imported.authorization, work)?,
                public_authorization: imported
                    .public_authorization
                    .as_ref()
                    .map(|route| retain_handler_authorization(route, work))
                    .transpose()?,
            });
        }
        let mut defining_implementations = Vec::new();
        if let Some(defining) = self.defining {
            charge(work, defining.implementations.len())?;
            defining_implementations
                .try_reserve_exact(defining.implementations.len())
                .map_err(|_| resource())?;
            let mut constraints =
                crate::interface::InterfaceConstraintBudget::with_limit(work.remaining());
            let result: Result<(), ValidationError> = (|| {
                for fact in &defining.implementations {
                    defining_implementations.push(
                        crate::resolved::clone_checked_implementation_fact(
                            fact,
                            work,
                            &mut constraints,
                        )
                        .map_err(|failure| match failure {
                            crate::resolved::ResolvedBuildFailure::TypeResource
                            | crate::resolved::ResolvedBuildFailure::ConstraintResource => {
                                resource()
                            }
                            _ => invalid(self.program.root),
                        })?,
                    );
                }
                Ok(())
            })();
            charge(work, constraints.used())?;
            result?;
        }
        let family = self.family;
        if self.entry.and_then(|entry| entry.family_identity()) != family {
            return Err(invalid(self.program.root));
        }
        let mut dictionary_formals = HashMap::new();
        let mut methods = Vec::new();
        if let Some(entry) = self
            .entry
            .filter(|entry| entry.family_definition().is_some())
        {
            charge(work, entry.dictionary_parameters().len())?;
            dictionary_formals
                .try_reserve(entry.dictionary_parameters().len())
                .map_err(|_| resource())?;
            for formal in entry.dictionary_parameters() {
                if dictionary_formals
                    .insert(
                        formal.id(),
                        IterativeTypeOwner::new(
                            clone_type_with_budget(formal.ty(), work).map_err(|()| resource())?,
                        ),
                    )
                    .is_some()
                {
                    return Err(invalid(self.program.root));
                }
            }
            for source in entry.source_methods() {
                charge(work, 1)?;
                let crate::resolved::ResolvedTermName::Method(method) = source.term else {
                    return Err(invalid(self.program.root));
                };
                let [slot] = source.evidence.as_ref() else {
                    return Err(invalid(self.program.root));
                };
                charge(work, self.program.method_evidence.occurrence_count())?;
                let original = self
                    .program
                    .method_evidence
                    .occurrence(slot.storage_id())
                    .ok_or_else(|| invalid(self.program.root))?;
                if original.checked_method != Some(method)
                    || original.checked_value_type.is_none()
                    || original.scope
                        != family.map(|identity| {
                            super::super::dialect::MethodEvidenceOwner::ResourceFamily(
                                identity.definition,
                            )
                        })
                {
                    return Err(invalid(self.program.root));
                }
                methods.try_reserve(1).map_err(|_| resource())?;
                methods.push(RetainedHandlerMethod {
                    node: self.program.root,
                    method,
                    slot: slot
                        .retain_unpublished()
                        .ok_or_else(|| invalid(self.program.root))?,
                    origin: RetainedHandlerOrigin::copy(&source.origin, work)?,
                });
            }
        }
        let mut occurrences = Vec::new();
        charge(work, self.source_occurrences.len())?;
        occurrences
            .try_reserve_exact(self.source_occurrences.len())
            .map_err(|_| resource())?;
        for (id, occurrence) in self.source_occurrences {
            charge(work, 1)?;
            let source = originals.get(&id).ok_or_else(|| invalid(id))?;
            charge(work, source.evidence.len())?;
            let mut slots = Vec::new();
            slots
                .try_reserve_exact(source.evidence.len())
                .map_err(|_| resource())?;
            for slot in &source.evidence {
                slots.push(slot.retain_unpublished().ok_or_else(|| invalid(id))?);
            }
            occurrences.push(RetainedHandlerOccurrence {
                checked_evidence: occurrence.checked_evidence,
                slots,
                node: id,
                callable_type: IterativeTypeOwner::new(
                    clone_type_with_budget(&node(self.program, id)?.ty, work)
                        .map_err(|()| resource())?,
                ),
                binder: occurrence.global.binder(),
                arguments: occurrence.arguments,
                rows: occurrence.rows,
                spelling: retain_handler_string(&source.spelling, work)?,
                origin: RetainedHandlerOrigin::copy(&source.origin, work)?,
                import_span: source.import_span,
                term: source.term,
            });
        }
        charge(work, self.program.method_evidence_anchors.len())?;
        let mut evidence_anchors = Vec::new();
        evidence_anchors
            .try_reserve_exact(self.program.method_evidence_anchors.len())
            .map_err(|_| resource())?;
        for anchor in &self.program.method_evidence_anchors {
            charge(work, 1)?;
            let application_edge = match &node(self.program, anchor.node)?.kind {
                EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Apply(
                    application,
                ))) => Some((application.function(), application.argument())),
                _ => None,
            };
            evidence_anchors.push(RetainedHandlerEvidenceAnchor {
                application_edge,
                fact: super::super::dialect::MethodEvidenceAnchor {
                    node: anchor.node,
                    owner: anchor.owner,
                    requirement: anchor.requirement,
                    method: anchor.method,
                    role: anchor.role,
                    occurrence: anchor.occurrence,
                    expectation: anchor.expectation,
                    application: anchor
                        .application
                        .clone_with_budget(work)
                        .map_err(|()| resource())?,
                },
            });
        }
        let dictionary_count = self
            .dictionary_variables
            .len()
            .checked_add(self.dictionary_installers.len())
            .ok_or_else(resource)?;
        charge(work, dictionary_count)?;
        let mut dictionary_nodes = Vec::new();
        dictionary_nodes
            .try_reserve_exact(dictionary_count)
            .map_err(|_| resource())?;
        for id in self
            .dictionary_variables
            .iter()
            .chain(&self.dictionary_installers)
        {
            dictionary_nodes.push((*id, retained_dictionary_node(self.program, *id)?));
        }
        charge(work, 1)?;
        Ok(RetainedHandlerExternals {
            catalog: std::sync::Arc::clone(&self.program.method_evidence),
            evidence_anchors,
            dictionary_nodes,
            types: self.types,
            globals,
            implementations,
            defining_implementations,
            occurrences,
            methods,
            family,
            dictionary_formals,
            dictionary_edges: self.dictionary_edges,
        })
    }
}

struct RetainedHandlerParameters(Vec<crate::resolved::ResolvedTypeVariable>);
impl Drop for RetainedHandlerParameters {
    fn drop(&mut self) {
        for parameter in self.0.drain(..) {
            crate::source::discard_origin_iteratively(parameter.origin);
        }
    }
}

#[cfg(test)]
mod storage_tests {
    use super::ExternalTypes;
    use crate::types::{Type, TypeVariableId, reset_type_discard_observation, type_discard_visits};

    #[test]
    fn external_type_replacement_and_drop_dispose_exact_owned_trees() {
        const DEPTH: usize = 32_768;
        let mut deep = Type::Unit;
        for _ in 0..DEPTH {
            deep = Type::Application(Box::new(deep), Box::new(Type::Unit));
        }
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let mut types = ExternalTypes(std::collections::HashMap::new());
                types.0.try_reserve(1).unwrap();
                let parameter = TypeVariableId::Generated(0);
                types.insert_discarding_replaced(parameter, deep);
                reset_type_discard_observation();
                types.insert_discarding_replaced(parameter, Type::Int);
                assert_eq!(type_discard_visits(), 2 * DEPTH + 1);
                assert_eq!(types.0.len(), 1);
                assert!(matches!(types.0.get(&parameter), Some(Type::Int)));
                drop(types);
                assert_eq!(type_discard_visits(), 2 * DEPTH + 2);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
