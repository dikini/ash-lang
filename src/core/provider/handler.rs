//! Conditional admission of actual provider clause fragments.
//!
//! The canonical local module supplies declaration authority. This entry has
//! no handled client body, executable handler certificate or public descriptor.

use super::super::{
    NodeId, TypedBinder, UnvalidatedEffectProgram,
    effect::{EffectClause, HandlerId},
};
#[cfg(test)]
use super::OperationId;
use super::{
    BinderId, CorePattern, CorePatternKind, DraftStateAssociation, EffectExprKind, EffectOperation,
    EffectOperationFamily, HashMap, HashSet, PureComputation, PureExprKind, Type, TypeWorkBudget,
    ValidationError, ValidationReason, charge, invalid, node, resource, same_type_with_budget,
};
use crate::{
    resolved::{
        ProviderTemplateId, ResolvedExpr, ResolvedExprKind, ResolvedLocalDeclaration,
        ResolvedModule, ResolvedPatternKind, ResolvedResourceDefinition,
    },
    types::{EffectRow, Kind, TypeVariableId},
};

/// Claimed source-to-Core entry facts, independently checked before admission.
#[derive(Debug)]
pub(crate) struct HandlerFragmentDraft {
    pub defining_facts: Option<std::sync::Arc<crate::resolved::ProviderDefiningFacts>>,
    pub program: UnvalidatedEffectProgram,
    pub template: ProviderTemplateId,
    pub handler: HandlerId,
    pub state: TypedBinder,
    pub dictionary_parameters: Box<[TypedBinder]>,
    pub family_requirements: Box<[crate::interface::CheckedRequirement]>,
    pub hidden: [(TypeVariableId, Kind); 2],
    pub clauses: Box<[EffectClause]>,
    pub direct_demands: EffectRow,
    pub pending_rows: super::HandlerPendingRows,
}

/// Borrowed row/capture inputs shared by independently admitted handler kinds.
/// This view carries coordinates only; its producer must authenticate the
/// defining source before any reconstructed recipe can grant an allowance.
#[derive(Clone, Copy)]
pub(in crate::core) struct HandlerGraphDraft<'a> {
    pub(in crate::core) program: &'a UnvalidatedEffectProgram,
    pub(in crate::core) template: ProviderTemplateId,
    pub(in crate::core) handler: HandlerId,
    pub(in crate::core) state: &'a TypedBinder,
    pub(in crate::core) hidden: &'a [(TypeVariableId, Kind); 2],
    pub(in crate::core) clauses: &'a [EffectClause],
    pub(in crate::core) direct_demands: &'a EffectRow,
    pub(in crate::core) pending_rows: &'a super::HandlerPendingRows,
}

#[derive(Clone, Copy)]
pub(in crate::core) struct HandlerGraphView<'a> {
    pub(in crate::core) draft: HandlerGraphDraft<'a>,
    pub(in crate::core) canonical: &'a crate::resolved::ResolvedRegistry,
    pub(in crate::core) row_recipe: Option<&'a super::HandlerRowRecipeDraft>,
    pub(in crate::core) roots: &'a [NodeId],
    // A product original retains its independently checked parameter wrappers.
    // The complete root is checked before projecting its exact clause forest.
    pub(in crate::core) wrapper_root: Option<NodeId>,
    pub(in crate::core) pattern_binders: &'a [BinderId],
    pub(in crate::core) provided: &'a crate::types::EffectInstance,
}
impl HandlerGraphView<'_> {
    pub(in crate::core) fn roots(&self) -> &[NodeId] {
        self.roots
    }
    pub(in crate::core) fn provided(&self) -> &crate::types::EffectInstance {
        self.provided
    }
}

impl HandlerGraphView<'_> {
    pub(in crate::core) fn handler_graph(&self) -> HandlerGraphView<'_> {
        *self
    }
}

/// Canonical entry roots, not a certificate that row realization is complete.
/// Construction is private; every allowance stays within this exact draft.
pub(in crate::core) struct HandlerFragmentEntry<'a> {
    pub(in crate::core) draft: &'a HandlerFragmentDraft,
    pub(in crate::core) module: &'a ResolvedModule,
    pub(in crate::core) definition: &'a ResolvedResourceDefinition,
    family: Option<&'a crate::resolved::ResolvedResourceFamilyTemplate>,
    pub(in crate::core) canonical: std::sync::Arc<crate::resolved::ResolvedRegistry>,
    pub(in crate::core) row_recipe: Option<&'a super::HandlerRowRecipeDraft>,
    pub(in crate::core) fragment_locals: Vec<crate::types::NominalTypeId>,
    roots: Vec<NodeId>,
    root_clauses: HashMap<NodeId, usize>,
    type_parameters: HashSet<TypeVariableId>,
    pub(in crate::core) imports:
        HashMap<crate::source::Span, &'a crate::resolved::ResolvedOccurrence>,
}

impl HandlerFragmentEntry<'_> {
    pub(in crate::core) fn handler_graph(&self) -> HandlerGraphView<'_> {
        HandlerGraphView {
            draft: HandlerGraphDraft {
                program: &self.draft.program,
                template: self.draft.template,
                handler: self.draft.handler,
                state: &self.draft.state,
                hidden: &self.draft.hidden,
                clauses: &self.draft.clauses,
                direct_demands: &self.draft.direct_demands,
                pending_rows: &self.draft.pending_rows,
            },
            canonical: &self.canonical,
            row_recipe: self.row_recipe,
            roots: self.roots(),
            wrapper_root: None,
            pattern_binders: &[],
            provided: self.provided(),
        }
    }
}

impl<'a> HandlerFragmentEntry<'a> {
    pub(in crate::core) fn reconstruct(
        draft: &'a HandlerFragmentDraft,
        module: &'a ResolvedModule,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        let program = &draft.program;
        charge(work, module.resources().len())?;
        let definition = module
            .resources()
            .iter()
            .find(|definition| definition.id == draft.template.definition())
            .ok_or_else(|| invalid(program.root))?;
        // The template slot only locates the source block. All allowances are
        // reconstructed from that original block and its canonical payload ID.
        let family = if draft.template == ProviderTemplateId::new(definition.id, 2) {
            None
        } else if draft.template == ProviderTemplateId::new(definition.id, 3) {
            Some(
                definition
                    .family_template
                    .as_ref()
                    .ok_or_else(|| invalid(program.root))?,
            )
        } else {
            return Err(invalid(program.root));
        };
        if family.is_none()
            && (!draft.dictionary_parameters.is_empty() || !draft.family_requirements.is_empty())
        {
            return Err(invalid(program.root));
        }
        let handlers_binder = family.map_or(&definition.handlers_binder, |family| {
            &family.handlers_binder
        });
        let handlers = family.map_or(definition.handlers.as_ref(), |family| {
            family.handlers.as_ref()
        });
        let provided = family.map_or(&definition.provided, |family| &family.provided);
        if definition.id.module() != module.module()
            || draft.state.id() != handlers_binder.id
            || !crate::resolved::same_origin_with_budget(
                draft.state.origin(),
                &handlers_binder.origin,
                work,
            )
            .map_err(|()| resource())?
            || !same_type_with_budget(draft.state.ty(), &definition.state.ty, work)
                .map_err(|()| resource())?
            || draft.hidden[0].1 != Kind::Type
            || draft.hidden[1].1 != Kind::EffectRow
            || draft.hidden[0].0 == draft.hidden[1].0
            || !draft
                .hidden
                .iter()
                .all(|(id, _)| matches!(id, TypeVariableId::Generated(_)))
            || draft
                .hidden
                .iter()
                .any(|(id, _)| *id == definition.answer.id)
            || draft.clauses.len() != handlers.len()
            || draft.clauses.is_empty()
            || program.root != draft.clauses[0].body()
        {
            return Err(invalid(program.root));
        }
        let canonical = std::sync::Arc::new(
            module
                .registry()
                .provider_template_view(module.imported_facts(), work)
                .map_err(|error| match error {
                    crate::resolved::ResolvedBuildFailure::InvalidState
                    | crate::resolved::ResolvedBuildFailure::Kind(_) => invalid(program.root),
                    crate::resolved::ResolvedBuildFailure::TypeResource
                    | crate::resolved::ResolvedBuildFailure::ConstraintResource => resource(),
                })?,
        );
        charge(
            work,
            canonical
                .type_variables()
                .count()
                .checked_mul(draft.hidden.len())
                .ok_or_else(resource)?,
        )?;
        if draft
            .hidden
            .iter()
            .any(|(identity, _)| canonical.type_variable(*identity).is_some())
        {
            return Err(invalid(program.root));
        }
        charge(
            work,
            definition
                .parameters
                .len()
                .checked_mul(draft.hidden.len())
                .ok_or_else(resource)?,
        )?;
        let declaration = canonical
            .effect(provided.instance.effect())
            .ok_or_else(|| invalid(program.root))?;
        if super::super::validate::registered_foreign_effect_with_charge(
            &canonical,
            declaration.id,
            |cells| work.charge(cells),
        )
        .map_err(|()| resource())?
            || declaration.operations.len() != draft.clauses.len()
            || declaration.parameters.len() != provided.instance.arguments().len()
        {
            return Err(invalid(program.root));
        }
        let state_id = definition
            .state
            .ty
            .outer_nominal()
            .ok_or_else(|| invalid(program.root))?;
        let state = super::super::validate::registered_foreign_state_with_charge(
            &canonical,
            state_id,
            |cells| work.charge(cells),
        )
        .map_err(|()| resource())?
        .ok_or_else(|| invalid(program.root))?;
        let arguments = type_arguments(&definition.state.ty, work)?;
        if arguments.len() != state.parameter_count
            || definition.parameters.is_empty()
            || !matches!(arguments.get(state.owned_identity_position), Some(Type::Variable(id)) if *id == definition.parameters[0].id)
        {
            return Err(invalid(program.root));
        }
        let mut operations = HashSet::new();
        let mut resumes = HashSet::new();
        let mut roots = Vec::new();
        let mut root_clauses = HashMap::new();
        charge(
            work,
            draft.clauses.len().checked_mul(4).ok_or_else(resource)?,
        )?;
        operations
            .try_reserve(draft.clauses.len())
            .map_err(|_| resource())?;
        resumes
            .try_reserve(draft.clauses.len())
            .map_err(|_| resource())?;
        root_clauses
            .try_reserve(draft.clauses.len())
            .map_err(|_| resource())?;
        roots
            .try_reserve_exact(draft.clauses.len())
            .map_err(|_| resource())?;
        for (index, (clause, source)) in draft.clauses.iter().zip(handlers).enumerate() {
            charge(work, 1)?;
            if clause.operation() != source.operation
                || clause.operation().owner() != declaration.id
                || declaration
                    .operations
                    .get(
                        usize::try_from(clause.operation().operation())
                            .map_err(|_| invalid(clause.body()))?,
                    )
                    .is_none_or(|operation| operation.id != clause.operation())
                || clause.resume() != source.resume
                || !operations.insert(clause.operation())
                || !resumes.insert(clause.resume())
                || root_clauses.insert(clause.body(), index).is_some()
                || !crate::resolved::same_origin_with_budget(
                    clause.origin(),
                    &crate::source::Origin::Source(source.span),
                    work,
                )
                .map_err(|()| resource())?
            {
                return Err(invalid(clause.body()));
            }
            node(program, clause.body())?;
            check_pattern_source_relation(
                program,
                &canonical,
                source,
                clause.pattern(),
                clause.body(),
                work,
            )?;
            roots.push(clause.body());
        }
        for stored in &program.nodes {
            charge(work, 1)?;
            use super::super::dialect::CoreOperationFamily;
            let count = EffectOperationFamily::child_count(&stored.kind);
            charge(work, count)?;
            for index in 0..count {
                let child = EffectOperationFamily::child_at(&stored.kind, index)
                    .ok_or_else(|| invalid(program.root))?;
                if root_clauses.contains_key(&child) {
                    return Err(invalid(child));
                }
            }
            if let EffectExprKind::Operation(EffectOperation::Handler(handler)) = &stored.kind
                && handler.id() == draft.handler
            {
                return Err(invalid(program.root));
            }
        }
        let mut type_parameters = HashSet::new();
        let parameter_count = definition
            .parameters
            .len()
            .checked_add(usize::from(family.is_some()))
            .ok_or_else(resource)?
            .checked_add(draft.hidden.len())
            .ok_or_else(resource)?;
        charge(work, parameter_count)?;
        type_parameters
            .try_reserve(parameter_count)
            .map_err(|_| resource())?;
        for formal in definition
            .parameters
            .iter()
            .chain(family.map(|family| &family.parameter))
        {
            let declared = canonical
                .type_variable(formal.id)
                .ok_or_else(|| invalid(program.root))?;
            if !crate::types::same_kind_with_budget(&formal.kind, &declared.kind, work)
                .map_err(|()| resource())?
                || !type_parameters.insert(formal.id)
            {
                return Err(invalid(program.root));
            }
        }
        // H0's provisional graph has an answer role but no residual row
        // positions. Retaining rho's kind does not authorize its use in any
        // graph annotation; such positions need an authenticated equation.
        if !type_parameters.insert(draft.hidden[0].0) {
            return Err(invalid(program.root));
        }
        let (imports, fragment_locals) = source_imports(
            handlers.iter().map(|clause| &clause.body),
            Some(crate::resolved::ProviderExternalFacts {
                imported: module.imported_facts(),
                defining: draft.defining_facts.as_deref(),
            }),
            family.is_some(),
            work,
        )?;
        Ok(Self {
            draft,
            module,
            definition,
            family,
            canonical,
            row_recipe: None,
            fragment_locals,
            roots,
            root_clauses,
            type_parameters,
            imports,
        })
    }

    pub(in crate::core) fn family_definition(&self) -> Option<&'a ResolvedResourceDefinition> {
        self.family.map(|_| self.definition)
    }
    pub(in crate::core) fn family_requirements(&self) -> &[crate::interface::CheckedRequirement] {
        &self.draft.family_requirements
    }
    pub(in crate::core) fn dictionary_parameters(&self) -> &[TypedBinder] {
        &self.draft.dictionary_parameters
    }
    pub(in crate::core) fn source_methods(
        &self,
    ) -> impl Iterator<Item = &'a crate::resolved::ResolvedOccurrence> {
        self.imports.values().copied().filter(|occurrence| {
            matches!(
                occurrence.term,
                crate::resolved::ResolvedTermName::Method(_)
            )
        })
    }
    pub(in crate::core) fn family_identity(&self) -> Option<super::ProviderFamilyIdentity> {
        self.family.map(|family| super::ProviderFamilyIdentity {
            definition: self.definition.id,
            parameter: family.parameter.id,
        })
    }

    pub(in crate::core) fn parameters(
        &self,
    ) -> impl Iterator<Item = &crate::resolved::ResolvedTypeVariable> {
        self.definition
            .parameters
            .iter()
            .chain(self.family.map(|family| &family.parameter))
    }

    pub(in crate::core) fn provided(&self) -> &crate::types::EffectInstance {
        &self
            .family
            .map_or(&self.definition.provided, |family| &family.provided)
            .instance
    }

    pub(in crate::core) fn interpreted(&self) -> &crate::types::EffectInstance {
        &self
            .family
            .map_or(&self.definition.interpreted, |family| &family.interpreted)
            .instance
    }

    pub(in crate::core) fn roots(&self) -> &[NodeId] {
        &self.roots
    }
    pub(in crate::core) fn clause_at(&self, root: NodeId) -> Option<&'a EffectClause> {
        self.root_clauses
            .get(&root)
            .and_then(|index| self.draft.clauses.get(*index))
    }
    pub(in crate::core) fn permits_type(&self, identity: TypeVariableId) -> bool {
        self.type_parameters.contains(&identity)
    }
}

/// Reconstruct the defining source VALUE inventory, including unused callable
/// bodies. Traversal supplies correspondence only, never native privilege.
pub(super) fn source_fragment_locals(
    source: &ResolvedExpr,
    work: &mut TypeWorkBudget,
) -> Result<Vec<crate::types::NominalTypeId>, ValidationError> {
    source_imports(std::iter::once(source), None, false, work).map(|(_, locals)| locals)
}

#[allow(clippy::type_complexity)]
fn source_imports<'a>(
    sources: impl ExactSizeIterator<Item = &'a ResolvedExpr>,
    facts: Option<crate::resolved::ProviderExternalFacts<'_>>,
    include_methods: bool,
    work: &mut TypeWorkBudget,
) -> Result<
    (
        HashMap<crate::source::Span, &'a crate::resolved::ResolvedOccurrence>,
        Vec<crate::types::NominalTypeId>,
    ),
    ValidationError,
> {
    enum Task<'a> {
        Expression(&'a ResolvedExpr),
        Block(&'a crate::resolved::ResolvedBlock),
        Declaration(&'a ResolvedLocalDeclaration),
    }
    let mut pending = Vec::new();
    let mut found = HashMap::new();
    let mut fragment_locals = Vec::new();
    charge(work, sources.len())?;
    pending
        .try_reserve_exact(sources.len())
        .map_err(|_| resource())?;
    pending.extend(sources.map(Task::Expression));
    while let Some(task) = pending.pop() {
        charge(work, 4)?;
        pending.try_reserve(3).map_err(|_| resource())?;
        match task {
            Task::Block(block) => {
                charge(work, block.declarations.len())?;
                pending
                    .try_reserve(
                        block
                            .declarations
                            .len()
                            .checked_add(1)
                            .ok_or_else(resource)?,
                    )
                    .map_err(|_| resource())?;
                pending.push(Task::Expression(&block.result));
                pending.extend(block.declarations.iter().map(Task::Declaration));
            }
            Task::Declaration(ResolvedLocalDeclaration::Binding(binding)) => {
                pending.push(Task::Expression(&binding.initializer))
            }
            Task::Declaration(ResolvedLocalDeclaration::Recursive(group)) => {
                charge(work, group.members.len())?;
                pending
                    .try_reserve(group.members.len())
                    .map_err(|_| resource())?;
                pending.extend(
                    group
                        .members
                        .iter()
                        .map(|member| Task::Expression(&member.initializer)),
                );
            }
            Task::Declaration(ResolvedLocalDeclaration::Evidence(evidence)) => {
                charge(work, evidence.method_groups.len())?;
                for group in &evidence.method_groups {
                    charge(work, group.equations.len())?;
                    pending
                        .try_reserve(group.equations.len())
                        .map_err(|_| resource())?;
                    pending.extend(
                        group
                            .equations
                            .iter()
                            .map(|equation| Task::Expression(&equation.body)),
                    );
                }
            }
            Task::Declaration(ResolvedLocalDeclaration::Newtype(id)) => {
                charge(work, 1)?;
                fragment_locals.try_reserve(1).map_err(|_| resource())?;
                fragment_locals.push(*id);
            }
            Task::Expression(expression) => match &expression.kind {
                ResolvedExprKind::Occurrence(occurrence) => {
                    if occurrence.global_binder().is_some_and(|binder| {
                        facts.is_some_and(|facts| facts.global(binder).is_some())
                    }) || (include_methods
                        && matches!(
                            occurrence.term,
                            crate::resolved::ResolvedTermName::Method(_)
                        ))
                    {
                        charge(work, 1)?;
                        found.try_reserve(1).map_err(|_| resource())?;
                        if found
                            .insert(occurrence.origin.primary_span(), occurrence)
                            .is_some()
                        {
                            return Err(ValidationError::new(
                                ValidationReason::ResourceEscape,
                                None,
                            ));
                        }
                    }
                }
                ResolvedExprKind::Block(block) => pending.push(Task::Block(block)),
                ResolvedExprKind::Function(function) => pending.push(Task::Block(&function.body)),
                ResolvedExprKind::Apply(application) => {
                    pending.push(Task::Expression(&application.function));
                    pending.push(Task::Expression(&application.argument));
                }
                ResolvedExprKind::Add(binary)
                | ResolvedExprKind::Multiply(binary)
                | ResolvedExprKind::Equal(binary) => {
                    pending.push(Task::Expression(&binary.left));
                    pending.push(Task::Expression(&binary.right));
                }
                ResolvedExprKind::Tuple(elements) => {
                    charge(work, elements.len())?;
                    pending
                        .try_reserve(elements.len())
                        .map_err(|_| resource())?;
                    pending.extend(elements.iter().map(Task::Expression));
                }
                ResolvedExprKind::Match(matched) => {
                    charge(work, matched.arms.len())?;
                    pending
                        .try_reserve(matched.arms.len().checked_add(1).ok_or_else(resource)?)
                        .map_err(|_| resource())?;
                    pending.push(Task::Expression(&matched.scrutinee));
                    pending.extend(matched.arms.iter().map(|arm| Task::Expression(&arm.body)));
                }
                ResolvedExprKind::Perform(request) => {
                    pending.push(Task::Expression(&request.operand))
                }
                ResolvedExprKind::Resume(resume) => pending.push(Task::Expression(&resume.value)),
                ResolvedExprKind::Handle(handler) => {
                    charge(work, handler.clauses.len())?;
                    pending
                        .try_reserve(handler.clauses.len().checked_add(1).ok_or_else(resource)?)
                        .map_err(|_| resource())?;
                    pending.push(Task::Expression(&handler.body));
                    pending.extend(
                        handler
                            .clauses
                            .iter()
                            .map(|clause| Task::Expression(&clause.body)),
                    );
                }
                ResolvedExprKind::Cleanup(cleanup) => {
                    pending.push(Task::Expression(&cleanup.body));
                    pending.push(Task::Expression(&cleanup.action));
                }
                ResolvedExprKind::Resource(resource) => {
                    pending.push(Task::Expression(&resource.initializer));
                    pending.push(Task::Expression(&resource.body));
                }
                ResolvedExprKind::CopyWindow(window) => {
                    pending.push(Task::Expression(&window.state));
                    pending.push(Task::Expression(&window.body));
                }
                ResolvedExprKind::ProviderResource(resource) => {
                    pending.push(Task::Expression(&resource.initializer));
                    pending.push(Task::Expression(&resource.body));
                }
                ResolvedExprKind::String(_)
                | ResolvedExprKind::Integer(_)
                | ResolvedExprKind::Boolean(_)
                | ResolvedExprKind::Unit
                | ResolvedExprKind::Constructor(_)
                | ResolvedExprKind::Discard(_) => {}
            },
        }
    }
    Ok((found, fragment_locals))
}

pub(in crate::core) struct HandlerAssociations<'a> {
    definitions: &'a [ResolvedResourceDefinition],
    parameters: Vec<Box<[TypeVariableId]>>,
}
impl<'a> HandlerAssociations<'a> {
    pub(in crate::core) fn reconstruct(
        module: &'a ResolvedModule,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        let definitions = module.resources();
        charge(work, definitions.len())?;
        let mut parameters = Vec::new();
        parameters
            .try_reserve_exact(definitions.len())
            .map_err(|_| resource())?;
        for definition in definitions {
            charge(work, definition.parameters.len())?;
            let mut row = Vec::new();
            row.try_reserve_exact(definition.parameters.len())
                .map_err(|_| resource())?;
            row.extend(definition.parameters.iter().map(|parameter| parameter.id));
            parameters.push(row.into_boxed_slice());
        }
        Ok(Self {
            definitions,
            parameters,
        })
    }
    pub(in crate::core) fn borrowed(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<Vec<DraftStateAssociation<'_>>, ValidationError> {
        charge(work, self.definitions.len())?;
        let mut borrowed = Vec::new();
        borrowed
            .try_reserve_exact(self.definitions.len())
            .map_err(|_| resource())?;
        for (definition, parameters) in self.definitions.iter().zip(&self.parameters) {
            borrowed.push(DraftStateAssociation {
                definition: definition.id,
                family: definition.family,
                parameters,
                state: &definition.state.ty,
            });
        }
        Ok(borrowed)
    }
}

pub(super) fn type_arguments<'a>(
    ty: &'a Type,
    work: &mut TypeWorkBudget,
) -> Result<Vec<&'a Type>, ValidationError> {
    let mut arguments = Vec::new();
    let mut head = ty;
    while let Type::Application(function, argument) = head {
        charge(work, 1)?;
        arguments.try_reserve(1).map_err(|_| resource())?;
        arguments.push(argument.as_ref());
        head = function;
    }
    arguments.reverse();
    Ok(arguments)
}

/// Match source binders and constructor identities to the actual lowered
/// pattern. Newtype replacements require their real unwrap/match nodes.
fn check_pattern_source_relation(
    program: &UnvalidatedEffectProgram,
    canonical: &crate::resolved::ResolvedRegistry,
    source: &crate::resolved::ResolvedHandlerClause,
    pattern: &CorePattern,
    body: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let source_body = &source.body;
    let expected_span = source.span;
    let source = &source.pattern;
    let mut pending = Vec::new();
    let mut lowerings = HashMap::new();
    let mut lowered_body = body;
    charge(work, 1)?;
    pending.try_reserve(1).map_err(|_| resource())?;
    pending.push((source, pattern));
    loop {
        while let Some((source, actual)) = pending.pop() {
            charge(work, 1)?;
            if !crate::resolved::same_origin_with_budget(
                &actual.origin,
                &crate::source::Origin::Source(source.span),
                work,
            )
            .map_err(|()| resource())?
            {
                return Err(invalid(body));
            }
            match (&source.kind, &actual.kind) {
                (ResolvedPatternKind::Binder(source), CorePatternKind::Binder(actual))
                    if source.id == actual.id() =>
                {
                    let crate::source::Origin::Generated {
                        cause,
                        reason: crate::source::GeneratedReason::BindingLowering,
                    } = actual.origin()
                    else {
                        return Err(invalid(body));
                    };
                    if !crate::resolved::same_origin_with_budget(&source.origin, cause, work)
                        .map_err(|()| resource())?
                    {
                        return Err(invalid(body));
                    }
                }
                (ResolvedPatternKind::Wildcard, CorePatternKind::Wildcard)
                | (ResolvedPatternKind::Unit, CorePatternKind::Unit) => {}
                (ResolvedPatternKind::Boolean(left), CorePatternKind::Boolean(right))
                    if left == right => {}
                (ResolvedPatternKind::Tuple(left), CorePatternKind::Tuple(right))
                    if left.len() == right.len() =>
                {
                    charge(work, left.len())?;
                    pending.try_reserve(left.len()).map_err(|_| resource())?;
                    pending.extend(left.iter().zip(right));
                }
                (
                    ResolvedPatternKind::Constructor {
                        constructor: source_constructor,
                        payload: source_payload,
                        ..
                    },
                    CorePatternKind::Constructor {
                        constructor,
                        payload,
                    },
                ) if source_constructor == constructor => {
                    match (source_payload.as_deref(), payload.as_deref()) {
                        (Some(left), Some(right)) => {
                            charge(work, 1)?;
                            pending.try_reserve(1).map_err(|_| resource())?;
                            pending.push((left, right));
                        }
                        (None, None) => {}
                        _ => return Err(invalid(body)),
                    }
                }
                (
                    ResolvedPatternKind::Constructor {
                        constructor,
                        payload: Some(payload),
                        ..
                    },
                    CorePatternKind::Binder(binder),
                ) => {
                    let declaration = canonical
                        .constructor(*constructor)
                        .ok_or_else(|| invalid(body))?;
                    let nominal = canonical
                        .nominal(declaration.owner)
                        .ok_or_else(|| invalid(body))?;
                    if nominal.declaration_kind
                        != crate::resolved::ResolvedNominalDeclarationKind::Newtype
                        || !matches!(binder.id(), BinderId::Generated(_))
                        || !crate::resolved::same_origin_with_budget(
                            binder.origin(),
                            &actual.origin,
                            work,
                        )
                        .map_err(|()| resource())?
                    {
                        return Err(invalid(body));
                    }
                    charge(work, 1)?;
                    lowerings.try_reserve(1).map_err(|_| resource())?;
                    if lowerings
                        .insert(
                            binder.id(),
                            (declaration.owner, payload.as_ref(), source.span),
                        )
                        .is_some()
                    {
                        return Err(invalid(body));
                    }
                }
                _ => return Err(invalid(body)),
            }
        }
        if lowerings.is_empty() {
            break;
        }
        let stored = node(program, lowered_body)?;
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(matched))) =
            &stored.kind
        else {
            return Err(invalid(lowered_body));
        };
        let [arm] = matched.arms() else {
            return Err(invalid(lowered_body));
        };
        let conversion = node(program, matched.scrutinee())?;
        let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::NewtypeConversion(
            convert,
        ))) = &conversion.kind
        else {
            return Err(invalid(lowered_body));
        };
        let variable_node = node(program, convert.child())?;
        let EffectExprKind::Pure(PureExprKind::Variable(variable)) = &variable_node.kind else {
            return Err(invalid(lowered_body));
        };
        let (owner, source, span) = lowerings
            .remove(&variable.binder())
            .ok_or_else(|| invalid(lowered_body))?;
        if convert.owner() != owner
            || convert.direction() != super::super::NewtypeConversionDirection::Unwrap
        {
            return Err(invalid(lowered_body));
        }
        for actual in [
            stored.origin.as_ref(),
            conversion.origin.as_ref(),
            variable_node.origin.as_ref(),
            Some(arm.origin()),
        ] {
            let actual = actual.ok_or_else(|| invalid(lowered_body))?;
            if !crate::resolved::same_origin_with_budget(
                actual,
                &crate::source::Origin::Source(span),
                work,
            )
            .map_err(|()| resource())?
            {
                return Err(invalid(lowered_body));
            }
        }
        charge(work, 1)?;
        pending.try_reserve(1).map_err(|_| resource())?;
        pending.push((source, arm.pattern()));
        lowered_body = arm.body();
    }
    check_source_body_root(program, source_body, lowered_body, expected_span, work)
}

/// A block's root is its first retained declaration, not its braced span.
/// Authenticate the ordinary lowering's complete provenance and source binder.
fn check_source_body_root(
    program: &UnvalidatedEffectProgram,
    mut source: &ResolvedExpr,
    body: NodeId,
    expected_span: crate::source::Span,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    loop {
        charge(work, 1)?;
        let stored = node(program, body)?;
        let origin = stored.origin.as_ref().ok_or_else(|| invalid(body))?;
        let ResolvedExprKind::Block(block) = &source.kind else {
            // Match is checked by its branch loop. Other admitted clause
            // results go through FinishCheck / record_type_check, which wraps
            // their synthesized source origin with the exact clause context.
            let primary = if matches!(source.kind, ResolvedExprKind::Match(_)) {
                origin
            } else {
                let crate::source::Origin::Generated {
                    cause,
                    reason: crate::source::GeneratedReason::TypeChecking,
                } = origin
                else {
                    return Err(invalid(body));
                };
                let crate::source::Origin::Related { primary, related } = cause.as_ref() else {
                    return Err(invalid(body));
                };
                charge(work, 1)?;
                if related.as_slice() != [expected_span] {
                    return Err(invalid(body));
                }
                primary.as_ref()
            };
            return if crate::resolved::same_origin_with_budget(
                primary,
                &crate::source::Origin::Source(source.span),
                work,
            )
            .map_err(|()| resource())?
            {
                Ok(())
            } else {
                Err(invalid(body))
            };
        };
        let Some(first) = block.declarations.first() else {
            source = &block.result;
            continue;
        };
        match first {
            ResolvedLocalDeclaration::Binding(binding) => {
                let crate::source::Origin::Generated {
                    cause,
                    reason: crate::source::GeneratedReason::BindingLowering,
                } = origin
                else {
                    return Err(invalid(body));
                };
                let crate::source::Origin::Related { primary, related } = cause.as_ref() else {
                    return Err(invalid(body));
                };
                let expected_count = 1 + usize::from(binding.annotation.is_some());
                charge(work, expected_count)?;
                if !matches!(primary.as_ref(), crate::source::Origin::Source(span) if *span == binding.span)
                    || related.len() != expected_count
                    || related[0] != binding.initializer.span
                    || binding
                        .annotation
                        .as_ref()
                        .is_some_and(|annotation| related[1] != annotation.span)
                {
                    return Err(invalid(body));
                }
                match (&binding.pattern.kind, &stored.kind) {
                    (
                        ResolvedPatternKind::Binder(source),
                        EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(
                            actual,
                        ))),
                    ) if source.id == actual.binder().id() => return Ok(()),
                    // Non-binder local patterns need their own actual match /
                    // newtype lowering relation before this fragment can pass.
                    _ => return Err(invalid(body)),
                }
            }
            ResolvedLocalDeclaration::Recursive(group) => {
                let crate::source::Origin::Generated {
                    cause,
                    reason: crate::source::GeneratedReason::RecursiveBindingLowering,
                } = origin
                else {
                    return Err(invalid(body));
                };
                let crate::source::Origin::Related { primary, related } = cause.as_ref() else {
                    return Err(invalid(body));
                };
                let EffectExprKind::Pure(PureExprKind::Computation(
                    PureComputation::RecursiveBind(actual),
                )) = &stored.kind
                else {
                    return Err(invalid(body));
                };
                charge(
                    work,
                    group.members.len().checked_mul(3).ok_or_else(resource)?,
                )?;
                if !matches!(primary.as_ref(), crate::source::Origin::Source(span) if *span == group.span)
                    || related.len() != group.members.len().checked_mul(3).ok_or_else(resource)?
                    || actual.members().len() != group.members.len()
                {
                    return Err(invalid(body));
                }
                for ((source, actual), spans) in group
                    .members
                    .iter()
                    .zip(actual.members())
                    .zip(related.chunks_exact(3))
                {
                    if source.binder.id != actual.binder().id()
                        || spans != [source.span, source.annotation.span, source.initializer.span]
                    {
                        return Err(invalid(body));
                    }
                }
                return Ok(());
            }
            // Lexical evidence and nominal wrappers need separate exact
            // correspondence; their names or spans grant no entry authority.
            ResolvedLocalDeclaration::Evidence(_) | ResolvedLocalDeclaration::Newtype(_) => {
                return Err(invalid(body));
            }
        }
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(crate) enum HandlerMutation {
    OperationOwner,
    Coverage,
    DuplicateRoot,
    SwapRoots,
    PatternDomain,
    PatternOrigin,
    BinderReason,
    BinderCause,
    BodyReason,
    BodyCause,
    HiddenKind,
    HiddenCollision,
    HiddenFormal,
    StateType,
    ResumeOwner,
    ResumeHandler,
    ResumeAvailable,
    ResumeResult,
    ResumeRowErasure,
    DirectDemandErasure,
    HiddenRowPosition,
    NestedForeignHandler,
}

#[cfg(test)]
pub(crate) fn mutate_handler_for_test(
    draft: &mut HandlerFragmentDraft,
    definition: &ResolvedResourceDefinition,
    mutation: HandlerMutation,
) {
    use super::super::effect::ResumeUse;
    use crate::source::{GeneratedReason, Origin};
    let root = draft.clauses[0].body();
    match mutation {
        HandlerMutation::OperationOwner => {
            draft.clauses[0].operation = OperationId::new(
                crate::types::EffectId::new(definition.id.module(), u32::MAX),
                0,
            )
        }
        HandlerMutation::Coverage => draft.clauses = Box::new([]),
        HandlerMutation::DuplicateRoot | HandlerMutation::SwapRoots => {
            assert!(draft.clauses.len() > 1);
            let first = draft.clauses[0].clone();
            let second = draft.clauses[1].clone();
            draft.clauses[1].arm = super::super::CoreMatchArm::new(
                second.pattern().clone(),
                first.body(),
                second.origin().clone(),
            );
            if matches!(mutation, HandlerMutation::SwapRoots) {
                draft.clauses[0].arm = super::super::CoreMatchArm::new(
                    first.pattern().clone(),
                    second.body(),
                    first.origin().clone(),
                );
                draft.program.root = second.body();
            }
        }
        HandlerMutation::PatternDomain => draft.clauses[0].arm.pattern_mut().ty = Type::Unit,
        HandlerMutation::PatternOrigin => {
            let pattern = draft.clauses[0].arm.pattern_mut();
            pattern.origin = Origin::Generated {
                cause: Box::new(pattern.origin.clone()),
                reason: GeneratedReason::TypeChecking,
            };
        }
        HandlerMutation::BinderReason | HandlerMutation::BinderCause => {
            let CorePatternKind::Binder(binder) = &mut draft.clauses[0].arm.pattern_mut().kind
            else {
                panic!("direct binder fixture");
            };
            let Origin::Generated { cause, reason } = binder.origin() else {
                panic!("lowered binder");
            };
            let origin = Origin::Generated {
                cause: if matches!(mutation, HandlerMutation::BinderCause) {
                    Box::new(Origin::Source(definition.state.span))
                } else {
                    cause.clone()
                },
                reason: if matches!(mutation, HandlerMutation::BinderReason) {
                    GeneratedReason::FunctionLowering
                } else {
                    *reason
                },
            };
            *binder = TypedBinder::new(binder.arena(), binder.id(), binder.ty().clone(), origin);
        }
        HandlerMutation::BodyReason | HandlerMutation::BodyCause => {
            let origin = draft.program.nodes[root.value() as usize]
                .origin
                .as_mut()
                .unwrap();
            let Origin::Generated { cause, reason } = origin else {
                panic!("checked or binding root");
            };
            if matches!(mutation, HandlerMutation::BodyReason) {
                *reason = GeneratedReason::FunctionLowering;
            } else {
                let Origin::Related { related, .. } = cause.as_mut() else {
                    panic!("causal context");
                };
                related[0] = definition.state.span;
            }
        }
        HandlerMutation::HiddenKind => draft.hidden[0].1 = Kind::EffectRow,
        HandlerMutation::HiddenCollision => draft.hidden[1].0 = draft.hidden[0].0,
        HandlerMutation::HiddenFormal => draft.hidden[0].0 = definition.parameters[0].id,
        HandlerMutation::StateType => draft.state.replace_type(Type::Unit),
        HandlerMutation::DirectDemandErasure => draft.direct_demands = EffectRow::empty(),
        HandlerMutation::HiddenRowPosition => {
            draft.program.nodes[root.value() as usize].effects = EffectRow::with_tail(
                Box::new([]),
                crate::types::EffectRowVariable::rigid(draft.hidden[1].0),
                Box::new([]),
            );
        }
        HandlerMutation::NestedForeignHandler => {
            // Preserve the actual ordinary source graph and its provenance,
            // but coherently replace its interpretation target with Native.
            let native = definition.interpreted.instance.clone();
            let reports = draft
                .program
                .registry
                .effect(native.effect())
                .unwrap()
                .operations
                .iter()
                .filter_map(|operation| {
                    operation
                        .annotation
                        .ty
                        .function_view()
                        .and_then(|signature| signature.value().outer_nominal())
                })
                .filter(|id| {
                    draft.program.registry.nominal(*id).is_some_and(|nominal| {
                        matches!(nominal.spelling.as_str(), "Acquire" | "Finish")
                    })
                })
                .collect::<Vec<_>>();
            // Only the small, source-built report types in this adversarial
            // fixture are rewritten; the canonical registry is unchanged.
            fn report_type(
                ty: &Type,
                reports: &[crate::types::NominalTypeId],
                state: &Type,
            ) -> Type {
                match ty {
                    Type::Application(function, argument) => {
                        let replacement = if matches!(function.as_ref(), Type::Nominal(id) if reports.contains(id))
                            && matches!(argument.as_ref(), Type::Unit)
                        {
                            state.clone()
                        } else {
                            report_type(argument, reports, state)
                        };
                        Type::Application(
                            Box::new(report_type(function, reports, state)),
                            Box::new(replacement),
                        )
                    }
                    Type::Function(domain, result) => Type::Function(
                        Box::new(report_type(domain, reports, state)),
                        Box::new(report_type(result, reports, state)),
                    ),
                    _ => ty.clone(),
                }
            }
            let native_request = draft
                .program
                .nodes
                .iter()
                .find_map(|stored| match &stored.kind {
                    EffectExprKind::Operation(EffectOperation::Request(request))
                        if request.effect() == &native =>
                    {
                        Some(stored.ty.clone())
                    }
                    _ => None,
                })
                .expect("actual native diagnostic request");
            let nested = draft
                .program
                .nodes
                .iter()
                .find_map(|stored| match &stored.kind {
                    EffectExprKind::Operation(EffectOperation::Handler(handler)) => {
                        Some((handler.id(), handler.effect().clone()))
                    }
                    _ => None,
                })
                .expect("actual nested source handler");
            let mut replaced_request = None;
            for (index, stored) in draft.program.nodes.iter_mut().enumerate() {
                let report = stored
                    .ty
                    .function_view()
                    .map_or(&stored.ty, |signature| signature.value())
                    .outer_nominal()
                    .is_some_and(|id| reports.contains(&id));
                if let EffectExprKind::Pure(PureExprKind::Computation(
                    PureComputation::TypeApplication(application),
                )) = &mut stored.kind
                    && report
                    && application.arguments().first() == Some(&Type::Unit)
                {
                    let mut arguments = application.arguments().to_vec();
                    arguments[0] = draft.state.ty().clone();
                    *application = super::super::type_ops::TypeApplicationNode::new(
                        application.function(),
                        arguments,
                    );
                }
                stored.ty = report_type(&stored.ty, &reports, draft.state.ty());
                if let EffectExprKind::Operation(EffectOperation::Request(request)) =
                    &mut stored.kind
                    && request.effect() == &nested.1
                {
                    request.effect = native.clone();
                    request.operation = OperationId::new(native.effect(), 1);
                    replaced_request = Some((index, request.operand()));
                    stored.ty = native_request.clone();
                }
                if stored.effects.known().contains(&nested.1) {
                    stored.effects = EffectRow::closed(vec![native.clone()].into_boxed_slice());
                }
                if let EffectExprKind::Operation(EffectOperation::Resume(resume)) = &stored.kind
                    && resume.handler() == nested.0
                {
                    stored.effects = EffectRow::empty();
                }
                if let EffectExprKind::Operation(EffectOperation::Handler(handler)) =
                    &mut stored.kind
                {
                    handler.effect = native.clone();
                    for (index, clause) in handler.clauses.iter_mut().enumerate() {
                        clause.operation = OperationId::new(native.effect(), index as u32);
                        if index != 0 {
                            let pattern = clause.arm.pattern_mut();
                            pattern.ty = draft.state.ty().clone();
                            let CorePatternKind::Binder(binder) = &mut pattern.kind else {
                                panic!("actual nested binder");
                            };
                            binder.replace_type(draft.state.ty().clone());
                        }
                    }
                    stored.effects = EffectRow::empty();
                }
            }
            let (request_index, operand) = replaced_request.expect("ordinary H request");
            let operand_node = &mut draft.program.nodes[operand.value() as usize];
            operand_node.kind = EffectExprKind::Pure(PureExprKind::Variable(
                super::super::variable::VariableNode::new(draft.state.id()),
            ));
            operand_node.ty = draft.state.ty().clone();
            for stored in &mut draft.program.nodes {
                if let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(
                    binding,
                ))) = &mut stored.kind
                    && binding.initializer().value() as usize == request_index
                {
                    binding.binder_mut().replace_type(native_request.clone());
                }
            }
            draft.direct_demands = EffectRow::empty();
        }
        HandlerMutation::ResumeOwner
        | HandlerMutation::ResumeHandler
        | HandlerMutation::ResumeAvailable
        | HandlerMutation::ResumeResult
        | HandlerMutation::ResumeRowErasure => {
            let stored = draft.program.nodes.iter_mut().find(|stored| matches!(&stored.kind, EffectExprKind::Operation(EffectOperation::Resume(resume)) if resume.handler() == draft.handler)).unwrap();
            let EffectExprKind::Operation(EffectOperation::Resume(resume)) = &mut stored.kind
            else {
                unreachable!();
            };
            match mutation {
                HandlerMutation::ResumeOwner => {
                    resume.owner = crate::resolved::ResumeId::new(u32::MAX)
                }
                HandlerMutation::ResumeHandler => resume.handler = HandlerId::new(u32::MAX),
                HandlerMutation::ResumeAvailable => resume.use_state = ResumeUse::Available,
                HandlerMutation::ResumeResult => stored.ty = Type::Unit,
                HandlerMutation::ResumeRowErasure => stored.effects = EffectRow::empty(),
                _ => unreachable!(),
            }
        }
    }
}

/// Body-free native state association retained after the defining source entry
/// has authenticated its family, formal order and exact foreign state type.
pub(in crate::core) struct RetainedHandlerStateAssociation {
    definition: crate::resolved::ResourceDefinitionId,
    family: crate::types::NominalTypeId,
    parameters: Box<[TypeVariableId]>,
    state: crate::types::IterativeTypeOwner,
}
impl RetainedHandlerStateAssociation {
    pub(in crate::core) fn borrowed(&self) -> DraftStateAssociation<'_> {
        DraftStateAssociation {
            definition: self.definition,
            family: self.family,
            parameters: &self.parameters,
            state: &self.state,
        }
    }
}
impl HandlerAssociations<'_> {
    pub(in crate::core) fn retain(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<Vec<RetainedHandlerStateAssociation>, ValidationError> {
        charge(work, self.definitions.len())?;
        let mut result = Vec::new();
        result
            .try_reserve_exact(self.definitions.len())
            .map_err(|_| resource())?;
        for (definition, parameters) in self.definitions.iter().zip(&self.parameters) {
            charge(work, parameters.len())?;
            let mut retained = Vec::new();
            retained
                .try_reserve_exact(parameters.len())
                .map_err(|_| resource())?;
            retained.extend_from_slice(parameters);
            result.push(RetainedHandlerStateAssociation {
                definition: definition.id,
                family: definition.family,
                parameters: retained.into_boxed_slice(),
                state: crate::types::IterativeTypeOwner::new(
                    crate::types::clone_type_with_budget(&definition.state.ty, work)
                        .map_err(|()| resource())?,
                ),
            });
        }
        Ok(result)
    }
}
