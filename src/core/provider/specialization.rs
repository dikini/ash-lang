//! Original-template admission for scoped provider execution.
//!
//! Compiler preparation borrows original checked templates. Executable proof
//! retains only reconstructed final projections and original body-free evidence;
//! source graphs, conditional recipes and compiler claims cannot grant authority.

use crate::{
    core::{BuildError, NodeId, UnvalidatedEffectProgram, ValidationError},
    types::TypeWorkBudget,
};

use super::ProviderScopeNode;

/// One copied occurrence's disjoint identity spaces. Every pair is checked
/// before projection, including duplicate source/target identities.
pub(crate) struct ProviderFreshening<'a> {
    pub(crate) binders: &'a [(crate::resolved::BinderId, crate::resolved::BinderId)],
    pub(crate) types: &'a [(
        crate::types::TypeVariableId,
        crate::types::TypeVariableId,
        crate::types::Kind,
    )],
    pub(crate) handlers: &'a [(crate::core::HandlerId, crate::core::HandlerId)],
    pub(crate) resumes: &'a [(crate::resolved::ResumeId, crate::resolved::ResumeId)],
    pub(crate) nominals: &'a [(crate::types::NominalTypeId, crate::types::NominalTypeId)],
    pub(crate) lexicals: &'a [(
        crate::interface::LexicalEvidenceId,
        crate::interface::LexicalEvidenceId,
    )],
}

pub(crate) struct ProviderTemplateSubstitution<'a> {
    pub(crate) types:
        &'a std::collections::HashMap<crate::types::TypeVariableId, crate::types::Type>,
    pub(crate) rows:
        &'a std::collections::HashMap<crate::types::TypeVariableId, crate::types::EffectRow>,
    pub(crate) pending:
        &'a std::collections::HashMap<crate::types::InferenceVariableId, crate::types::EffectRow>,
}

#[derive(Clone, Copy)]
pub(crate) enum ProviderOriginalTemplate<'a> {
    Lifecycle(&'a LifecycleOriginal, &'a UnvalidatedEffectProgram),
    Handler(&'a crate::core::validate::CheckedHandlerTemplate),
}
#[derive(Clone, Copy)]
pub(crate) struct ProviderOccurrenceRelocation {
    pub(crate) original: usize,
    pub(crate) copied: usize,
}
pub(crate) struct ProviderCopiedTemplate<'a> {
    pub(crate) original: ProviderOriginalTemplate<'a>,
    pub(crate) original_slots: &'a [crate::interface::EvidenceSlot],
    pub(crate) nodes: &'a [(NodeId, NodeId)],
    pub(crate) freshening: ProviderFreshening<'a>,
    pub(crate) substitution: ProviderTemplateSubstitution<'a>,
    pub(crate) occurrences: &'a [ProviderOccurrenceRelocation],
    pub(crate) catalog: &'a [super::copy::ProviderCatalogRelocation],
    pub(crate) node_rows: &'a std::collections::HashMap<NodeId, crate::types::EffectRow>,
}
#[derive(Debug)]
pub(crate) struct ProviderScopeAdmission {
    pub(crate) definition: std::sync::Arc<crate::resolved::ResourceTypeFact>,
    pub(crate) native: std::sync::Arc<crate::foreign::ForeignModuleFact>,
    pub(crate) arguments: Box<[crate::types::KindedArgument]>,
    pub(crate) identity: crate::types::TypeVariableId,
    pub(crate) retained: Box<[crate::types::TypeVariableId]>,
    pub(crate) native_effect: crate::types::EffectInstance,
    pub(crate) protocol: super::ProviderScopeProtocol,
}
impl Drop for ProviderScopeAdmission {
    fn drop(&mut self) {
        for argument in std::mem::take(&mut self.arguments).into_vec() {
            crate::types::discard_kinded_argument_iteratively(argument);
        }
    }
}
pub(crate) struct ProviderSpecializationEntries<'a> {
    pub(crate) acquire: &'a super::ProviderLifecycleEntry,
    pub(crate) finish: &'a super::ProviderLifecycleEntry,
    pub(crate) state: &'a crate::core::TypedBinder,
    pub(crate) handler: crate::core::HandlerId,
    pub(crate) clauses: &'a [crate::core::EffectClause],
    pub(crate) body: NodeId,
}

fn renamed<T: Copy + Eq>(
    identity: T,
    pairs: &[(T, T)],
    work: &mut TypeWorkBudget,
) -> Result<T, ValidationError> {
    super::charge(work, pairs.len())?;
    Ok(pairs
        .iter()
        .find(|(original, _)| *original == identity)
        .map_or(identity, |(_, copied)| *copied))
}

impl ProviderFreshening<'_> {
    fn authenticate(&self, work: &mut TypeWorkBudget) -> Result<(), ValidationError> {
        fn pairs<T: Eq>(
            pairs: &[(T, T)],
            work: &mut TypeWorkBudget,
        ) -> Result<(), ValidationError> {
            for (ordinal, (source, target)) in pairs.iter().enumerate() {
                super::charge(
                    work,
                    ordinal
                        .checked_mul(2)
                        .and_then(|n| n.checked_add(1))
                        .ok_or_else(super::resource)?,
                )?;
                if source == target
                    || pairs[..ordinal]
                        .iter()
                        .any(|(old, fresh)| old == source || fresh == target)
                {
                    return Err(ValidationError::new(
                        crate::core::ValidationReason::Scope,
                        None,
                    ));
                }
            }
            Ok(())
        }
        pairs(self.binders, work)?;
        pairs(self.handlers, work)?;
        pairs(self.resumes, work)?;
        pairs(self.nominals, work)?;
        pairs(self.lexicals, work)?;
        for (ordinal, (source, target, _)) in self.types.iter().enumerate() {
            super::charge(
                work,
                ordinal
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(1))
                    .ok_or_else(super::resource)?,
            )?;
            if source == target
                || self.types[..ordinal]
                    .iter()
                    .any(|(old, fresh, _)| old == source || fresh == target)
            {
                return Err(ValidationError::new(
                    crate::core::ValidationReason::TypeOperation,
                    None,
                ));
            }
        }
        Ok(())
    }
    fn atom(
        &self,
        atom: &super::projection::Atom,
        work: &mut TypeWorkBudget,
    ) -> Result<super::projection::Atom, ValidationError> {
        use super::projection::Atom;
        super::charge(work, 1)?;
        Ok(match atom {
            Atom::Tag(tag) => Atom::Tag(*tag),
            Atom::Count(count) => Atom::Count(*count),
            Atom::Boolean(value) => Atom::Boolean(*value),
            Atom::Literal(value) => {
                super::charge(work, value.len())?;
                let mut copy = String::new();
                copy.try_reserve_exact(value.len())
                    .map_err(|_| super::resource())?;
                copy.push_str(value);
                Atom::Literal(copy)
            }
            Atom::Binder(id) => Atom::Binder(renamed(*id, self.binders, work)?),
            Atom::Variable(id) => {
                super::charge(work, self.types.len())?;
                Atom::Variable(
                    self.types
                        .iter()
                        .find(|(old, _, _)| old == id)
                        .map_or(*id, |(_, fresh, _)| *fresh),
                )
            }
            Atom::Nominal(id) => Atom::Nominal(renamed(*id, self.nominals, work)?),
            Atom::Constructor(id) => Atom::Constructor(crate::types::ConstructorId::new(
                renamed(id.owner(), self.nominals, work)?,
                id.constructor(),
            )),
            Atom::Handler(id) => Atom::Handler(renamed(*id, self.handlers, work)?),
            Atom::Resume(id) => Atom::Resume(renamed(*id, self.resumes, work)?),
            Atom::Effect(id) => Atom::Effect(*id),
            Atom::Operation(id) => Atom::Operation(*id),
            Atom::Method(id) => Atom::Method(*id),
            Atom::Definition(id) => Atom::Definition(*id),
            Atom::Primitive(value) => Atom::Primitive(*value),
            Atom::Direction(value) => Atom::Direction(*value),
            Atom::ResumeUse(value) => Atom::ResumeUse(*value),
            Atom::Span(value) => Atom::Span(*value),
            Atom::Acquisition(_) => {
                return Err(ValidationError::new(
                    crate::core::ValidationReason::ResourceEscape,
                    None,
                ));
            }
        })
    }
}

impl ProviderTemplateSubstitution<'_> {
    fn metadata(
        &self,
        metadata: &super::projection::Metadata,
        renaming: &crate::types::TemplateIdentityRenaming<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<super::projection::Metadata, ValidationError> {
        use super::projection::Metadata;
        let invalid = || ValidationError::new(crate::core::ValidationReason::EffectRow, None);
        Ok(match metadata {
            Metadata::Type(ty) => Metadata::Type(crate::types::IterativeTypeOwner::new(
                crate::types::substitute_type_for_template_with(
                    ty,
                    self.types,
                    self.rows,
                    self.pending,
                    renaming,
                    |cells| work.charge(cells),
                    || (),
                )
                .map_err(|()| super::resource())?
                .map_err(|_| invalid())?,
            )),
            Metadata::Row(row) => Metadata::Row(
                crate::types::substitute_row_for_template_with(
                    row,
                    self.types,
                    self.rows,
                    self.pending,
                    renaming,
                    |cells| work.charge(cells),
                    || (),
                )
                .map_err(|()| super::resource())?
                .map_err(|_| invalid())?,
            ),
            Metadata::Argument(argument) => {
                Metadata::Argument(crate::types::IterativeArgumentOwner::new(
                    crate::types::substitute_argument_for_template_with(
                        argument,
                        self.types,
                        self.rows,
                        self.pending,
                        renaming,
                        |cells| work.charge(cells),
                        || (),
                    )
                    .map_err(|()| super::resource())?
                    .map_err(|_| invalid())?,
                ))
            }
            Metadata::Kind(kind) => Metadata::Kind(
                crate::types::clone_kind_with_budget(kind, work).map_err(|()| super::resource())?,
            ),
        })
    }
}

fn specialize_projection(
    original: &super::projection::NodeProjection,
    copied: &std::collections::HashMap<NodeId, NodeId>,
    fresh: &ProviderFreshening<'_>,
    substitution: &ProviderTemplateSubstitution<'_>,
    renaming: &crate::types::TemplateIdentityRenaming<'_>,
    work: &mut TypeWorkBudget,
) -> Result<super::projection::NodeProjection, ValidationError> {
    let mapped = |node: NodeId| {
        copied
            .get(&node)
            .copied()
            .ok_or_else(|| super::invalid(node))
    };
    super::charge(
        work,
        original
            .children
            .len()
            .checked_add(original.atoms.len())
            .and_then(|n| n.checked_add(original.metadata.len()))
            .and_then(|n| n.checked_add(original.origins.len()))
            .and_then(|n| n.checked_add(1))
            .ok_or_else(super::resource)?,
    )?;
    let mut result = super::projection::NodeProjection {
        node: mapped(original.node)?,
        children: Vec::new(),
        atoms: Vec::new(),
        metadata: Vec::new(),
        origins: Vec::new(),
    };
    result
        .children
        .try_reserve_exact(original.children.len())
        .map_err(|_| super::resource())?;
    result
        .atoms
        .try_reserve_exact(original.atoms.len())
        .map_err(|_| super::resource())?;
    result
        .metadata
        .try_reserve_exact(original.metadata.len())
        .map_err(|_| super::resource())?;
    result
        .origins
        .try_reserve_exact(original.origins.len())
        .map_err(|_| super::resource())?;
    for child in &original.children {
        result.children.push(mapped(*child)?);
    }
    for atom in &original.atoms {
        result.atoms.push(fresh.atom(atom, work)?);
    }
    for metadata in &original.metadata {
        result
            .metadata
            .push(substitution.metadata(metadata, renaming, work)?);
    }
    for origin in &original.origins {
        result.origins.push(super::RetainedHandlerOrigin::copy(
            origin.as_origin(),
            work,
        )?);
    }
    Ok(result)
}

/// Solved rows for compiler preparation. Construction reconstructs D, epsilon,
/// Omega and the normalized residual; a caller cannot supply a row solution.
#[derive(Debug)]
pub(crate) struct ResolvedProviderHandlerRows {
    direct: crate::types::EffectRow,
    epsilon: crate::types::EffectRow,
    output: crate::types::EffectRow,
    residual: crate::types::EffectRow,
    pending: std::collections::HashMap<crate::types::InferenceVariableId, crate::types::EffectRow>,
    node_rows: std::collections::HashMap<NodeId, crate::types::EffectRow>,
    handler_outputs: std::collections::HashMap<crate::core::HandlerId, crate::types::EffectRow>,
}
impl ResolvedProviderHandlerRows {
    pub(crate) fn node_rows(&self) -> &std::collections::HashMap<NodeId, crate::types::EffectRow> {
        &self.node_rows
    }
    pub(crate) fn handler_outputs(
        &self,
    ) -> &std::collections::HashMap<crate::core::HandlerId, crate::types::EffectRow> {
        &self.handler_outputs
    }
    pub(crate) fn direct(&self) -> &crate::types::EffectRow {
        &self.direct
    }
    pub(crate) fn epsilon(&self) -> &crate::types::EffectRow {
        &self.epsilon
    }
    pub(crate) fn output(&self) -> &crate::types::EffectRow {
        &self.output
    }
    pub(crate) fn residual(&self) -> &crate::types::EffectRow {
        &self.residual
    }
    pub(crate) fn pending(
        &self,
    ) -> &std::collections::HashMap<crate::types::InferenceVariableId, crate::types::EffectRow>
    {
        &self.pending
    }
}

pub(in crate::core) fn prepare_handler_rows(
    checked: &crate::core::validate::CheckedHandlerTemplate,
    types: &std::collections::HashMap<crate::types::TypeVariableId, crate::types::Type>,
    rows: &std::collections::HashMap<crate::types::TypeVariableId, crate::types::EffectRow>,
    body_answer: &crate::types::Type,
    body_effects: &crate::types::EffectRow,
    provided: &crate::types::EffectInstance,
    work: &mut TypeWorkBudget,
) -> Result<ResolvedProviderHandlerRows, ValidationError> {
    use crate::types::{
        EffectRowError, clone_effect_row_with_budget, same_effect_rows_with_budget,
    };
    let hidden = checked.original_hidden();
    if types.contains_key(&hidden[0].0) || rows.contains_key(&hidden[1].0) {
        return Err(super::invalid(checked.original_program().root));
    }
    // An empty actual capture input domain is admissible only when the original
    // checked recipe has no discard ports. Advanced capture realization must
    // provide independently reconstructed inputs through this same vocabulary.
    if !checked.original_recipe().discards().is_empty() {
        return Err(ValidationError::new(
            crate::core::ValidationReason::ResourceEscape,
            None,
        ));
    }
    let (direct, pending_rows) = checked.original_recipe().realize_direct(
        types,
        rows,
        &std::collections::HashMap::new(),
        work,
    )?;
    let epsilon = match body_effects
        .remove_exact_with_budget(provided, work)
        .map_err(|()| super::resource())?
    {
        Ok(row) => row,
        Err(EffectRowError::Missing) => {
            clone_effect_row_with_budget(body_effects, work).map_err(|()| super::resource())?
        }
        Err(_) => {
            return Err(ValidationError::new(
                crate::core::ValidationReason::EffectRow,
                None,
            ));
        }
    };
    let output = direct
        .union_with_budget(&epsilon, work)
        .map_err(|()| super::resource())?
        .map_err(|_| ValidationError::new(crate::core::ValidationReason::EffectRow, None))?;
    let mut residual =
        clone_effect_row_with_budget(&output, work).map_err(|()| super::resource())?;
    for known in direct.known() {
        residual = residual
            .remove_exact_with_budget(known, work)
            .map_err(|()| super::resource())?
            .map_err(|_| ValidationError::new(crate::core::ValidationReason::EffectRow, None))?;
    }
    let known = crate::types::rebuild_effect_row_with_budget(
        direct.known().iter(),
        None,
        std::iter::empty(),
        crate::types::clone_type_with_budget,
        work,
    )
    .map_err(|()| super::resource())?;
    let recomposed = known
        .union_with_budget(&residual, work)
        .map_err(|()| super::resource())?
        .map_err(|_| ValidationError::new(crate::core::ValidationReason::EffectRow, None))?;
    if !same_effect_rows_with_budget(&recomposed, &output, work).map_err(|()| super::resource())? {
        return Err(super::invalid(checked.original_program().root));
    }
    let records = checked.original_pending_rows();
    if pending_rows.len() != records.len() {
        return Err(super::invalid(checked.original_program().root));
    }
    super::charge(work, records.len())?;
    let mut pending = std::collections::HashMap::new();
    pending
        .try_reserve(records.len())
        .map_err(|_| super::resource())?;
    for (record, row) in records.iter().zip(pending_rows) {
        if let Some(previous) = pending.insert(record.identity, row) {
            drop(previous);
            return Err(super::invalid(checked.original_program().root));
        }
    }
    let mut complete = OriginalSubstitutions {
        types: std::collections::HashMap::new(),
        rows: std::collections::HashMap::new(),
    };
    super::charge(
        work,
        types
            .len()
            .checked_add(rows.len())
            .and_then(|n| n.checked_add(2))
            .ok_or_else(super::resource)?,
    )?;
    complete
        .types
        .try_reserve(types.len() + 1)
        .map_err(|_| super::resource())?;
    complete
        .rows
        .try_reserve(rows.len() + 1)
        .map_err(|_| super::resource())?;
    for (id, ty) in types {
        complete.insert_type(
            *id,
            crate::types::clone_type_with_budget(ty, work).map_err(|()| super::resource())?,
        );
    }
    for (id, row) in rows {
        complete.insert_row(
            *id,
            clone_effect_row_with_budget(row, work).map_err(|()| super::resource())?,
        );
    }
    complete.insert_type(
        hidden[0].0,
        crate::types::clone_type_with_budget(body_answer, work).map_err(|()| super::resource())?,
    );
    complete.insert_row(
        hidden[1].0,
        clone_effect_row_with_budget(&residual, work).map_err(|()| super::resource())?,
    );
    let realized = checked.original_recipe().realize_nodes(
        checked.original_program(),
        &complete.types,
        &complete.rows,
        &pending,
        &std::collections::HashMap::new(),
        &output,
        work,
    )?;
    Ok(ResolvedProviderHandlerRows {
        direct,
        epsilon,
        output,
        residual,
        pending,
        node_rows: realized.nodes,
        handler_outputs: realized.handlers,
    })
}

/// Original checked lifecycle authority. This preparation-only token is bound
/// to the exact original arena, catalog, entry, and frozen typed node forest.
/// It is deliberately absent from executable specialization proof storage.
#[derive(Debug)]
pub(crate) struct LifecycleOriginal {
    arena: crate::core::dialect::ArenaId,
    catalog: std::sync::Arc<crate::core::dialect::MethodEvidenceCatalog>,
    template: crate::resolved::ProviderTemplateId,
    phase: super::LifecyclePhase,
    body: NodeId,
    parameter: crate::resolved::BinderId,
    family: crate::types::NominalTypeId,
    parameter_projection: super::projection::NodeProjection,
    formals: Box<
        [(
            crate::types::TypeVariableId,
            crate::types::TypeVariableId,
            crate::types::Kind,
        )],
    >,
    hidden: [(crate::types::TypeVariableId, crate::types::Kind); 2],
    nodes: Vec<super::projection::NodeProjection>,
}

impl LifecycleOriginal {
    pub(crate) fn body(&self) -> NodeId {
        self.body
    }
    pub(crate) fn parameter(&self) -> crate::resolved::BinderId {
        self.parameter
    }
    pub(crate) fn parameter_binder<'a>(
        &self,
        program: &'a UnvalidatedEffectProgram,
        work: &mut TypeWorkBudget,
    ) -> Result<&'a crate::core::TypedBinder, ValidationError> {
        if program.arena != self.arena {
            return Err(super::invalid(self.body));
        }
        super::charge(work, 2)?;
        let crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Computation(
            crate::core::PureComputation::TypeAbstraction(abstraction),
        )) = &super::node(program, program.root)?.kind
        else {
            return Err(super::invalid(program.root));
        };
        let crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Value(
            crate::core::PureValue::Function(function),
        )) = &super::node(program, abstraction.body())?.kind
        else {
            return Err(super::invalid(program.root));
        };
        let binder = function.parameter();
        let root = super::node(program, program.root)?;
        let function_node = super::node(program, abstraction.body())?;
        let body = super::node(program, self.body)?;
        if function.body() != self.body
            || binder.id() != self.parameter
            || !root.effects.is_empty()
            || !function_node.effects.is_empty()
            || abstraction.parameters().len()
                != self
                    .formals
                    .len()
                    .checked_add(2)
                    .ok_or_else(super::resource)?
            || !self.parameter_projection.same(
                &super::projection::project_binder(self.body, binder, work)?,
                work,
            )?
        {
            return Err(super::invalid(self.body));
        }
        super::charge(work, abstraction.parameters().len())?;
        for ((_, generated, kind), (actual, actual_kind)) in
            self.formals.iter().zip(abstraction.parameters())
        {
            if generated != actual
                || !crate::types::same_kind_with_budget(kind, actual_kind, work)
                    .map_err(|()| super::resource())?
            {
                return Err(super::invalid(program.root));
            }
        }
        for ((expected, kind), (actual, actual_kind)) in self
            .hidden
            .iter()
            .zip(&abstraction.parameters()[self.formals.len()..])
        {
            if expected != actual
                || !crate::types::same_kind_with_budget(kind, actual_kind, work)
                    .map_err(|()| super::resource())?
            {
                return Err(super::invalid(program.root));
            }
        }
        let crate::types::Type::Forall(parameters, function_type) = &root.ty else {
            return Err(super::invalid(program.root));
        };
        if !crate::types::same_kinded_type_parameters_with_budget(
            parameters,
            abstraction.parameters(),
            work,
        )
        .map_err(|()| super::resource())?
            || !crate::types::same_type_with_budget(function_type, &function_node.ty, work)
                .map_err(|()| super::resource())?
        {
            return Err(super::invalid(program.root));
        }
        let signature = function_node
            .ty
            .function_view()
            .ok_or_else(|| super::invalid(abstraction.body()))?;
        if !crate::types::same_type_with_budget(signature.domain(), binder.ty(), work)
            .map_err(|()| super::resource())?
            || !crate::types::same_type_with_budget(signature.value(), &body.ty, work)
                .map_err(|()| super::resource())?
        {
            return Err(super::invalid(abstraction.body()));
        }
        match signature.effects() {
            None if body.effects.is_empty() => {}
            Some(row)
                if crate::types::same_effect_rows_with_budget(row, &body.effects, work)
                    .map_err(|()| super::resource())? => {}
            _ => return Err(super::invalid(abstraction.body())),
        }
        Ok(binder)
    }
    pub(crate) fn template(&self) -> crate::resolved::ProviderTemplateId {
        self.template
    }
    pub(crate) fn phase(&self) -> super::LifecyclePhase {
        self.phase
    }
    pub(crate) fn formals(
        &self,
    ) -> &[(
        crate::types::TypeVariableId,
        crate::types::TypeVariableId,
        crate::types::Kind,
    )] {
        &self.formals
    }
    pub(crate) fn hidden(&self) -> &[(crate::types::TypeVariableId, crate::types::Kind); 2] {
        &self.hidden
    }

    /// A source program cannot be substituted underneath admitted authority,
    /// including in malformed internal fixtures that preserve its arena ID.
    pub(crate) fn authenticate_source(
        &self,
        program: &UnvalidatedEffectProgram,
        budget: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        if self.arena != program.arena
            || !std::sync::Arc::ptr_eq(&self.catalog, &program.method_evidence)
        {
            return Err(super::invalid(self.body));
        }
        self.parameter_binder(program, budget)?;
        for expected in &self.nodes {
            let actual = super::projection::project(
                expected.node,
                super::node(program, expected.node)?,
                budget,
            )?;
            if !expected.same(&actual, budget)? {
                return Err(super::invalid(expected.node));
            }
        }
        Ok(())
    }
}

struct OriginalSubstitutions {
    types: std::collections::HashMap<crate::types::TypeVariableId, crate::types::Type>,
    rows: std::collections::HashMap<crate::types::TypeVariableId, crate::types::EffectRow>,
}
impl OriginalSubstitutions {
    fn insert_type(&mut self, id: crate::types::TypeVariableId, ty: crate::types::Type) -> bool {
        if let Some(previous) = self.types.insert(id, ty) {
            crate::types::discard_type_iteratively(previous);
            false
        } else {
            true
        }
    }
    fn insert_row(
        &mut self,
        id: crate::types::TypeVariableId,
        row: crate::types::EffectRow,
    ) -> bool {
        if let Some(previous) = self.rows.insert(id, row) {
            drop(previous);
            false
        } else {
            true
        }
    }
}
impl Drop for OriginalSubstitutions {
    fn drop(&mut self) {
        for (_, ty) in self.types.drain() {
            crate::types::discard_type_iteratively(ty);
        }
        self.rows.clear();
    }
}

/// Minted only after independently checking entry, original external authority,
/// exact native arguments, state lineage, and the actual lifecycle flow.
pub(crate) fn admit_lifecycle_original(
    program: &UnvalidatedEffectProgram,
    context: &super::LifecycleEntryContext<'_>,
    externals: &super::AuthenticatedProviderExternals<'_>,
    associations: &[super::DraftStateAssociation<'_>],
    budget: &mut TypeWorkBudget,
) -> Result<LifecycleOriginal, ValidationError> {
    use crate::types::{IterativeArgumentOwner, IterativeTypeOwner, Kind, KindedArgument, Type};
    if !externals.authenticates_program(program) {
        return Err(super::invalid(context.body));
    }
    super::check_lifecycle_entry(program, context, budget)?;
    let mut substitutions = OriginalSubstitutions {
        types: std::collections::HashMap::new(),
        rows: std::collections::HashMap::new(),
    };
    super::charge(budget, context.formal_parameters.len())?;
    let rows = context
        .formal_parameters
        .iter()
        .filter(|(_, _, kind)| matches!(kind, Kind::EffectRow))
        .count();
    substitutions
        .types
        .try_reserve(context.formal_parameters.len() - rows)
        .map_err(|_| super::resource())?;
    substitutions
        .rows
        .try_reserve(rows)
        .map_err(|_| super::resource())?;
    for (source, fresh, kind) in context.formal_parameters {
        match kind {
            Kind::EffectRow => {
                super::charge(budget, 1)?;
                let row = crate::types::EffectRow::open(
                    crate::types::EffectRowVariable::rigid(*fresh),
                    Box::new([]),
                );
                if !substitutions.insert_row(*source, row) {
                    return Err(super::invalid(context.body));
                }
            }
            _ => {
                super::charge(budget, 1)?;
                if !substitutions.insert_type(*source, Type::Variable(*fresh)) {
                    return Err(super::invalid(context.body));
                }
            }
        }
    }
    let interpreted = context.definition.interpreted();
    super::charge(
        budget,
        interpreted
            .arguments()
            .len()
            .checked_mul(2)
            .ok_or_else(super::resource)?,
    )?;
    let mut guarded = Vec::new();
    guarded
        .try_reserve_exact(interpreted.arguments().len())
        .map_err(|_| super::resource())?;
    for argument in interpreted.arguments() {
        // Native argument coordinates are still Type-only. All source owner
        // slots were authenticated above; none are silently dropped here.
        if !matches!(argument, KindedArgument::TypeArg(_)) {
            return Err(super::invalid(context.body));
        }
        let actual = crate::types::substitute_kinded_argument_with(
            argument,
            &substitutions.types,
            &substitutions.rows,
            |cells| budget.charge(cells),
        )
        .map_err(|()| super::resource())?
        .map_err(|_| super::invalid(context.body))?;
        guarded.push(IterativeArgumentOwner::new(actual));
    }
    let mut arguments = Vec::new();
    arguments
        .try_reserve_exact(guarded.len())
        .map_err(|_| super::resource())?;
    arguments.extend(guarded.into_iter().map(IterativeArgumentOwner::into_inner));
    let native = crate::types::EffectInstance::new_kinded(
        interpreted.effect(),
        arguments.into_boxed_slice(),
    );
    let state = crate::types::substitute_type_and_row_variables_with(
        context.definition.state(),
        &substitutions.types,
        &substitutions.rows,
        |cells| budget.charge(cells),
        || (),
    )
    .map_err(|()| super::resource())?
    .map_err(|_| super::invalid(context.body))?;
    let state = IterativeTypeOwner::new(state);
    super::check_lifecycle_flow_with_externals(
        program,
        &super::LifecycleFlowContext {
            phase: context.phase,
            body: context.body,
            parameter: context.parameter,
            native: &native,
            state: &state,
        },
        externals,
        associations,
        budget,
    )?;
    let order = crate::core::transform::provider_entry_forest_order(
        program,
        &[context.body],
        &std::collections::HashSet::new(),
        budget,
    )
    .map_err(|_| super::resource())?;
    super::charge(
        budget,
        order.len().checked_add(1).ok_or_else(super::resource)?,
    )?;
    let mut nodes = Vec::new();
    nodes
        .try_reserve_exact(order.len())
        .map_err(|_| super::resource())?;
    for id in order {
        nodes.push(super::projection::project(
            id,
            super::node(program, id)?,
            budget,
        )?);
    }
    super::charge(budget, context.formal_parameters.len())?;
    let mut formals = Vec::new();
    formals
        .try_reserve_exact(context.formal_parameters.len())
        .map_err(|_| super::resource())?;
    for (source, generated, kind) in context.formal_parameters {
        formals.push((
            *source,
            *generated,
            crate::types::clone_kind_with_budget(kind, budget).map_err(|()| super::resource())?,
        ));
    }
    let crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Computation(
        crate::core::PureComputation::TypeAbstraction(abstraction),
    )) = &super::node(program, program.root)?.kind
    else {
        return Err(super::invalid(program.root));
    };
    let crate::core::EffectExprKind::Pure(crate::core::PureExprKind::Value(
        crate::core::PureValue::Function(function),
    )) = &super::node(program, abstraction.body())?.kind
    else {
        return Err(super::invalid(program.root));
    };
    let parameter_projection =
        super::projection::project_binder(context.body, function.parameter(), budget)?;
    Ok(LifecycleOriginal {
        arena: program.arena,
        catalog: std::sync::Arc::clone(&program.method_evidence),
        template: context.template,
        phase: context.phase,
        body: context.body,
        parameter: context.parameter,
        family: context.definition.family(),
        parameter_projection,
        formals: formals.into_boxed_slice(),
        hidden: [
            (context.hidden_answer, Kind::Type),
            (
                match context.hidden_row {
                    crate::types::EffectRowVariable::Rigid(identity) => identity,
                    _ => return Err(super::invalid(context.body)),
                },
                Kind::EffectRow,
            ),
        ],
        nodes,
    })
}

/// Final, recipe-free relation to independently checked original occurrences.
/// The private allocation can only be minted by the copying reconstruction.
#[derive(Clone, Debug)]
pub(crate) struct OriginalProviderSpecialization(std::sync::Arc<SpecializationProof>);
impl PartialEq for OriginalProviderSpecialization {
    fn eq(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for OriginalProviderSpecialization {}
#[derive(Debug)]
struct SpecializationProof {
    arena: crate::core::dialect::ArenaId,
    catalog: std::sync::Arc<crate::core::dialect::MethodEvidenceCatalog>,
    definition: crate::resolved::ResourceDefinitionId,
    acquire: NodeId,
    finish: NodeId,
    body: NodeId,
    handler: crate::core::HandlerId,
    nodes: Vec<super::projection::NodeProjection>,
    parameters: [super::projection::NodeProjection; 3],
    clauses: Vec<super::projection::NodeProjection>,
    occurrences: Vec<SpecializedOccurrence>,
    anchors: Vec<SpecializedAnchor>,
    state_accesses: Vec<NodeId>,
}
struct SpecializedOccurrence {
    slot: usize,
    original: OriginalOccurrence,
    selection: crate::interface::EvidenceSelection,
    application: crate::interface::InterfaceApplication,
    arguments: Vec<crate::types::IterativeTypeOwner>,
    value_type: Option<crate::types::IterativeTypeOwner>,
    method: Option<crate::interface::MethodId>,
    scope: Option<crate::core::dialect::MethodEvidenceOwner>,
    scope_binder: Option<crate::resolved::BinderId>,
    target: Option<crate::core::dialect::MethodEvidenceOwner>,
    requirement: Option<crate::interface::RequirementId>,
}
#[derive(Debug)]
struct SpecializedAnchor {
    node: NodeId,
    owner: Option<crate::core::dialect::MethodEvidenceOwner>,
    requirement: Option<crate::interface::RequirementId>,
    method: crate::interface::MethodId,
    application: crate::interface::InterfaceApplication,
    role: crate::core::dialect::MethodEvidenceAnchorRole,
    occurrence: Option<usize>,
}
struct OriginalOccurrence {
    allocation: crate::interface::EvidenceSlot,
    application: crate::interface::InterfaceApplication,
    selection: crate::interface::EvidenceSelection,
    method: Option<crate::interface::MethodId>,
    arguments: Vec<crate::types::IterativeTypeOwner>,
    value: Option<crate::types::IterativeTypeOwner>,
}
impl OriginalOccurrence {
    fn copy(&self, work: &mut TypeWorkBudget) -> Result<Self, ValidationError> {
        super::charge(
            work,
            self.arguments
                .len()
                .checked_add(2)
                .ok_or_else(super::resource)?,
        )?;
        let mut arguments = Vec::new();
        arguments
            .try_reserve_exact(self.arguments.len())
            .map_err(|_| super::resource())?;
        for argument in &self.arguments {
            arguments.push(crate::types::IterativeTypeOwner::new(
                crate::types::clone_type_with_budget(argument, work)
                    .map_err(|()| super::resource())?,
            ));
        }
        Ok(Self {
            allocation: self
                .allocation
                .retain_unpublished()
                .unwrap_or_else(|| self.allocation.clone()),
            application: self
                .application
                .clone_with_budget(work)
                .map_err(|()| super::resource())?,
            selection: self.selection.clone(),
            method: self.method,
            arguments,
            value: self
                .value
                .as_ref()
                .map(|ty| {
                    crate::types::clone_type_with_budget(ty, work)
                        .map(crate::types::IterativeTypeOwner::new)
                        .map_err(|()| super::resource())
                })
                .transpose()?,
        })
    }
    fn authenticate_publication(&self, work: &mut TypeWorkBudget) -> Result<(), ValidationError> {
        let (application, arguments, value, selection) = match self.method {
            None => {
                let (application, selection) = self.allocation.filled().ok_or_else(|| {
                    ValidationError::new(crate::core::ValidationReason::Registry, None)
                })?;
                (application, &[][..], None, selection)
            }
            Some(method) => {
                let (actual, application, arguments, value, selection) =
                    self.allocation.filled_method().ok_or_else(|| {
                        ValidationError::new(crate::core::ValidationReason::Registry, None)
                    })?;
                if method != actual {
                    return Err(ValidationError::new(
                        crate::core::ValidationReason::Registry,
                        None,
                    ));
                }
                (application, arguments, Some(value), selection)
            }
        };
        if !same_application(&self.application, application, work)?
            || !same_selection(&self.selection, selection, work)?
            || self.arguments.len() != arguments.len()
        {
            return Err(ValidationError::new(
                crate::core::ValidationReason::Registry,
                None,
            ));
        }
        for (expected, actual) in self.arguments.iter().zip(arguments) {
            if !crate::types::same_type_with_budget(expected, actual, work)
                .map_err(|()| super::resource())?
            {
                return Err(ValidationError::new(
                    crate::core::ValidationReason::Registry,
                    None,
                ));
            }
        }
        match (&self.value, value) {
            (None, None) => {}
            (Some(expected), Some(actual))
                if crate::types::same_type_with_budget(expected, actual, work)
                    .map_err(|()| super::resource())? => {}
            _ => {
                return Err(ValidationError::new(
                    crate::core::ValidationReason::Registry,
                    None,
                ));
            }
        }
        Ok(())
    }
}
impl std::fmt::Debug for SpecializedOccurrence {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("SpecializedOccurrence")
            .field("slot", &self.slot)
            .field("application", &self.application)
            .field("method", &self.method)
            .finish_non_exhaustive()
    }
}
fn same_application(
    left: &crate::interface::InterfaceApplication,
    right: &crate::interface::InterfaceApplication,
    work: &mut TypeWorkBudget,
) -> Result<bool, ValidationError> {
    super::charge(
        work,
        left.arguments()
            .len()
            .checked_add(1)
            .ok_or_else(super::resource)?,
    )?;
    if left.interface() != right.interface() || left.arguments().len() != right.arguments().len() {
        return Ok(false);
    }
    for (a, b) in left.arguments().iter().zip(right.arguments()) {
        if !crate::types::same_kinded_argument_with_budget(a, b, work)
            .map_err(|()| super::resource())?
        {
            return Ok(false);
        }
    }
    Ok(true)
}
fn specialized_application(
    original: &crate::interface::InterfaceApplication,
    copy: &ProviderCopiedTemplate<'_>,
    renaming: &crate::types::TemplateIdentityRenaming<'_>,
    work: &mut TypeWorkBudget,
) -> Result<crate::interface::InterfaceApplication, ValidationError> {
    super::charge(
        work,
        original
            .arguments()
            .len()
            .checked_mul(2)
            .ok_or_else(super::resource)?,
    )?;
    let mut arguments = Vec::new();
    arguments
        .try_reserve_exact(original.arguments().len())
        .map_err(|_| super::resource())?;
    for argument in original.arguments() {
        let actual = crate::types::substitute_argument_for_template_with(
            argument,
            copy.substitution.types,
            copy.substitution.rows,
            copy.substitution.pending,
            renaming,
            |n| work.charge(n),
            || (),
        )
        .map_err(|()| super::resource())?
        .map_err(|_| ValidationError::new(crate::core::ValidationReason::EffectRow, None))?;
        arguments.push(crate::types::IterativeArgumentOwner::new(actual));
    }
    let mut actuals = Vec::new();
    actuals
        .try_reserve_exact(arguments.len())
        .map_err(|_| super::resource())?;
    actuals.extend(
        arguments
            .into_iter()
            .map(crate::types::IterativeArgumentOwner::into_inner),
    );
    Ok(crate::interface::InterfaceApplication::new_kinded(
        original.interface(),
        actuals.into_boxed_slice(),
    ))
}
fn owner(
    owner: Option<crate::core::dialect::MethodEvidenceOwner>,
    fresh: &ProviderFreshening<'_>,
    work: &mut TypeWorkBudget,
) -> Result<Option<crate::core::dialect::MethodEvidenceOwner>, ValidationError> {
    use crate::core::dialect::MethodEvidenceOwner;
    Ok(match owner {
        Some(MethodEvidenceOwner::Global(id)) => Some(MethodEvidenceOwner::Global(renamed(
            id,
            fresh.binders,
            work,
        )?)),
        other => other,
    })
}
fn role(
    original: crate::core::dialect::MethodEvidenceAnchorRole,
    fresh: &ProviderFreshening<'_>,
    nodes: &std::collections::HashMap<NodeId, NodeId>,
    work: &mut TypeWorkBudget,
) -> Result<crate::core::dialect::MethodEvidenceAnchorRole, ValidationError> {
    use crate::core::dialect::MethodEvidenceAnchorRole as R;
    let binder = |id, work: &mut TypeWorkBudget| renamed(id, fresh.binders, work);
    let lexical = |id, work: &mut TypeWorkBudget| renamed(id, fresh.lexicals, work);
    Ok(match original {
        R::LexicalOwner { source, binder: id } => R::LexicalOwner {
            source: lexical(source, work)?,
            binder: binder(id, work)?,
        },
        R::LexicalUse {
            source,
            binder: id,
            selection_node,
        } => R::LexicalUse {
            source: lexical(source, work)?,
            binder: binder(id, work)?,
            selection_node,
        },
        R::ImplementationOwner {
            implementation,
            binder: id,
        } => R::ImplementationOwner {
            implementation,
            binder: binder(id, work)?,
        },
        R::Domain { binder: id } => R::Domain {
            binder: binder(id, work)?,
        },
        R::Instantiation { binder: id } => R::Instantiation {
            binder: id.map(|id| binder(id, work)).transpose()?,
        },
        R::Application { producer } => R::Application {
            producer: renamed_producer(producer, fresh, work)?,
        },
        R::AdapterEdge {
            adapter,
            adapter_selection_node,
            ordinal,
            producer_node,
            producer_selection_node,
            producer_binder,
            producer,
        } => R::AdapterEdge {
            adapter,
            adapter_selection_node,
            ordinal,
            producer_node: *nodes
                .get(&producer_node)
                .ok_or_else(|| super::invalid(producer_node))?,
            producer_selection_node,
            producer_binder: producer_binder.map(|id| binder(id, work)).transpose()?,
            producer: renamed_producer(producer, fresh, work)?,
        },
        other => other,
    })
}
fn renamed_producer(
    producer: crate::core::dialect::MethodEvidenceProducer,
    fresh: &ProviderFreshening<'_>,
    work: &mut TypeWorkBudget,
) -> Result<crate::core::dialect::MethodEvidenceProducer, ValidationError> {
    use crate::core::dialect::MethodEvidenceProducer as P;
    Ok(match producer {
        P::Lexical { source } => P::Lexical {
            source: renamed(source, fresh.lexicals, work)?,
        },
        other => other,
    })
}
fn relocate_claimed_role_nodes(
    role: crate::core::dialect::MethodEvidenceAnchorRole,
    nodes: &std::collections::HashMap<NodeId, NodeId>,
    work: &mut TypeWorkBudget,
) -> Result<crate::core::dialect::MethodEvidenceAnchorRole, ValidationError> {
    use crate::core::dialect::MethodEvidenceAnchorRole as R;
    Ok(match role {
        R::AdapterEdge {
            adapter,
            adapter_selection_node,
            ordinal,
            producer_node,
            producer_selection_node,
            producer_binder,
            producer,
        } => {
            super::charge(work, 1)?;
            R::AdapterEdge {
                adapter,
                adapter_selection_node,
                ordinal,
                producer_node: mapped(nodes, producer_node)?,
                producer_selection_node,
                producer_binder,
                producer,
            }
        }
        other => other,
    })
}
fn mapped(
    nodes: &std::collections::HashMap<NodeId, NodeId>,
    node: NodeId,
) -> Result<NodeId, ValidationError> {
    nodes
        .get(&node)
        .copied()
        .ok_or_else(|| super::invalid(node))
}
fn target_node<'a>(
    arena: crate::core::dialect::ArenaId,
    nodes: &'a [crate::core::dialect::StoredNode<crate::core::EffectOperationFamily>],
    node: NodeId,
) -> Result<&'a crate::core::dialect::StoredNode<crate::core::EffectOperationFamily>, ValidationError>
{
    if node.arena() != arena {
        return Err(super::invalid(node));
    }
    nodes
        .get(node.index().map_err(|_| super::invalid(node))?)
        .ok_or_else(|| super::invalid(node))
}

impl crate::core::CoreBuilder<crate::core::EffectOperationFamily> {
    /// Reconstructs every copied typed occurrence from original independently
    /// admitted templates. Compiler claims are consumed, never retained as proof.
    pub(crate) fn admit_provider_scope(
        &self,
        mut admission: ProviderScopeAdmission,
        entries: ProviderSpecializationEntries<'_>,
        copies: &[ProviderCopiedTemplate<'_>],
        work: &mut TypeWorkBudget,
    ) -> Result<std::sync::Arc<super::AdmittedProviderScope>, ValidationError> {
        use super::projection::{project, project_binder, project_clause};
        use crate::types::{
            KindedArgument, TemplateIdentityRenaming, Type, same_effect_rows_with_budget,
            same_type_with_budget,
        };
        let (arena, target, catalog) = self
            .provider_projection_parts()
            .map_err(|_| super::invalid(entries.body))?;
        if copies.len() != 3
            || admission.arguments.len() != admission.definition.parameters.len()
            || !matches!(admission.arguments.first(),Some(KindedArgument::TypeArg(Type::Variable(id))) if *id==admission.identity)
        {
            return Err(super::invalid(entries.body));
        }
        let body = target_node(arena, target, entries.body)?;
        super::charge(
            work,
            admission
                .arguments
                .len()
                .checked_add(copies.len())
                .ok_or_else(super::resource)?,
        )?;
        let row_count = admission
            .arguments
            .iter()
            .filter(|argument| matches!(argument, KindedArgument::RowArg(_)))
            .count();
        let type_count = admission.arguments.len() - row_count;
        let handler_copy = copies
            .iter()
            .find_map(|copy| match copy.original {
                ProviderOriginalTemplate::Handler(original) => Some((original, copy)),
                _ => None,
            })
            .ok_or_else(|| super::invalid(entries.body))?;
        let residual_claim = handler_copy
            .1
            .substitution
            .rows
            .get(&handler_copy.0.original_hidden()[1].0)
            .ok_or_else(|| super::invalid(entries.body))?;
        authenticate_disjoint_freshening(copies, work)?;
        authenticate_caller_disjointness(copies, &body.ty, &body.effects, work)?;
        let mut all_nodes = std::collections::HashSet::new();
        let total = copies
            .iter()
            .try_fold(0usize, |n, c| n.checked_add(c.nodes.len()))
            .ok_or_else(super::resource)?;
        super::charge(
            work,
            total
                .checked_mul(2)
                .and_then(|n| n.checked_add(7))
                .ok_or_else(super::resource)?,
        )?;
        all_nodes
            .try_reserve(total)
            .map_err(|_| super::resource())?;
        let mut proof = SpecializationProof {
            arena,
            catalog: std::sync::Arc::clone(catalog),
            definition: admission.definition.id,
            acquire: entries.acquire.body,
            finish: entries.finish.body,
            body: entries.body,
            handler: entries.handler,
            nodes: Vec::new(),
            parameters: [
                project_binder(entries.acquire.body, &entries.acquire.parameter, work)?,
                project_binder(entries.finish.body, &entries.finish.parameter, work)?,
                project_binder(entries.body, entries.state, work)?,
            ],
            clauses: Vec::new(),
            occurrences: Vec::new(),
            anchors: Vec::new(),
            state_accesses: Vec::new(),
        };
        proof
            .nodes
            .try_reserve_exact(total)
            .map_err(|_| super::resource())?;
        proof
            .clauses
            .try_reserve_exact(entries.clauses.len())
            .map_err(|_| super::resource())?;
        let mut phases = [false; 3];
        for copy in copies {
            copy.freshening.authenticate(work)?;
            if copy.substitution.types.len()
                != type_count.checked_add(1).ok_or_else(super::resource)?
                || copy.substitution.rows.len()
                    != row_count.checked_add(1).ok_or_else(super::resource)?
            {
                return Err(super::invalid(entries.body));
            }
            super::charge(
                work,
                copy.nodes
                    .len()
                    .checked_mul(2)
                    .and_then(|n| n.checked_add(copy.freshening.types.len()))
                    .and_then(|n| n.checked_add(copy.freshening.nominals.len()))
                    .ok_or_else(super::resource)?,
            )?;
            let mut nodes = std::collections::HashMap::new();
            nodes
                .try_reserve(copy.nodes.len())
                .map_err(|_| super::resource())?;
            for (old, new) in copy.nodes {
                target_node(arena, target, *new)?;
                if nodes.insert(*old, *new).is_some() || !all_nodes.insert(*new) {
                    return Err(super::invalid(*new));
                }
            }
            let mut variables = std::collections::HashMap::new();
            variables
                .try_reserve(copy.freshening.types.len())
                .map_err(|_| super::resource())?;
            for (old, new, _) in copy.freshening.types {
                variables.insert(*old, *new);
            }
            let mut nominals = std::collections::HashMap::new();
            nominals
                .try_reserve(copy.freshening.nominals.len())
                .map_err(|_| super::resource())?;
            for (old, new) in copy.freshening.nominals {
                nominals.insert(*old, *new);
            }
            let renaming = TemplateIdentityRenaming {
                variables: &variables,
                nominals: &nominals,
            };
            let (source, originals, phase) = match copy.original {
                ProviderOriginalTemplate::Lifecycle(original, source) => {
                    original.authenticate_source(source, work)?;
                    let phase = match original.phase {
                        super::LifecyclePhase::Acquire => 0,
                        super::LifecyclePhase::Finish => 1,
                    };
                    let expected = if phase == 0 {
                        entries.acquire
                    } else {
                        entries.finish
                    };
                    if original.template.definition() != admission.definition.id
                        || original.family != admission.definition.family
                        || mapped(&nodes, original.body) != Ok(expected.body)
                        || renamed(original.parameter, copy.freshening.binders, work)?
                            != expected.parameter.id()
                        || original.formals.len() != admission.arguments.len()
                    {
                        return Err(super::invalid(expected.body));
                    }
                    for ((formal, generated, kind), (declared, actual)) in
                        original.formals.iter().zip(
                            admission
                                .definition
                                .parameters
                                .iter()
                                .zip(admission.arguments.iter()),
                        )
                    {
                        if *formal != declared.id
                            || !crate::types::same_kind_with_budget(kind, &declared.kind, work)
                                .map_err(|()| super::resource())?
                        {
                            return Err(super::invalid(expected.body));
                        }
                        authenticate_actual(*generated, actual, &copy.substitution, work)?;
                    }
                    if !copy.node_rows.is_empty()
                        || !copy.substitution.pending.is_empty()
                        || !same_type_with_budget(
                            copy.substitution
                                .types
                                .get(&original.hidden[0].0)
                                .ok_or_else(|| super::invalid(expected.body))?,
                            &body.ty,
                            work,
                        )
                        .map_err(|()| super::resource())?
                        || !same_effect_rows_with_budget(
                            copy.substitution
                                .rows
                                .get(&original.hidden[1].0)
                                .ok_or_else(|| super::invalid(expected.body))?,
                            residual_claim,
                            work,
                        )
                        .map_err(|()| super::resource())?
                    {
                        return Err(super::invalid(expected.body));
                    }
                    let expected_parameter = specialize_projection(
                        &original.parameter_projection,
                        &nodes,
                        &copy.freshening,
                        &copy.substitution,
                        &renaming,
                        work,
                    )?;
                    if !expected_parameter.same(&proof.parameters[phase], work)? {
                        return Err(super::invalid(expected.body));
                    }
                    (source, original.nodes.as_slice(), phase)
                }
                ProviderOriginalTemplate::Handler(original) => {
                    original.authenticate_source(work)?;
                    original.authenticate_definition(&admission.definition, work)?;
                    if original.original_template().definition() != admission.definition.id
                        || renamed(original.original_handler(), copy.freshening.handlers, work)?
                            != entries.handler
                        || original.original_clauses().len() != entries.clauses.len()
                    {
                        return Err(super::invalid(entries.body));
                    }
                    for formal in admission
                        .definition
                        .parameters
                        .iter()
                        .zip(admission.arguments.iter())
                    {
                        authenticate_actual(formal.0.id, formal.1, &copy.substitution, work)?;
                    }
                    let state = project_binder(
                        original.original_program().root,
                        original.original_state(),
                        work,
                    )?;
                    let actual_state = project_binder(
                        mapped(&nodes, original.original_program().root)?,
                        entries.state,
                        work,
                    )?;
                    if !specialize_projection(
                        &state,
                        &nodes,
                        &copy.freshening,
                        &copy.substitution,
                        &renaming,
                        work,
                    )?
                    .same(&actual_state, work)?
                    {
                        return Err(super::invalid(entries.body));
                    }
                    // The normalized solution is reconstructed from the actual
                    // body, original direct proof and complete source actuals.
                    let provided = substitute_instance(
                        &admission.definition.provided.instance,
                        &copy.substitution,
                        &renaming,
                        work,
                    )?;
                    let mut formals = OriginalSubstitutions {
                        types: std::collections::HashMap::new(),
                        rows: std::collections::HashMap::new(),
                    };
                    super::charge(work, admission.arguments.len())?;
                    let row_count = admission
                        .arguments
                        .iter()
                        .filter(|arg| matches!(arg, KindedArgument::RowArg(_)))
                        .count();
                    formals
                        .types
                        .try_reserve(admission.arguments.len() - row_count)
                        .map_err(|_| super::resource())?;
                    formals
                        .rows
                        .try_reserve(row_count)
                        .map_err(|_| super::resource())?;
                    for (formal, actual) in admission
                        .definition
                        .parameters
                        .iter()
                        .zip(admission.arguments.iter())
                    {
                        match actual {
                            KindedArgument::TypeArg(ty) => {
                                if !formals.insert_type(
                                    formal.id,
                                    crate::types::clone_type_with_budget(ty, work)
                                        .map_err(|()| super::resource())?,
                                ) {
                                    return Err(super::invalid(entries.body));
                                }
                            }
                            KindedArgument::RowArg(row) => {
                                if !formals.insert_row(
                                    formal.id,
                                    crate::types::clone_effect_row_with_budget(row, work)
                                        .map_err(|()| super::resource())?,
                                ) {
                                    return Err(super::invalid(entries.body));
                                }
                            }
                        }
                    }
                    let rows = original.prepare_rows(
                        &formals.types,
                        &formals.rows,
                        &body.ty,
                        &body.effects,
                        &provided,
                        work,
                    )?;
                    super::charge(work, rows.node_rows.len())?;
                    if copy.node_rows.len() != rows.node_rows.len() {
                        return Err(super::invalid(entries.body));
                    }
                    for (id, row) in &rows.node_rows {
                        if !same_effect_rows_with_budget(
                            row,
                            copy.node_rows.get(id).ok_or_else(|| super::invalid(*id))?,
                            work,
                        )
                        .map_err(|()| super::resource())?
                        {
                            return Err(super::invalid(*id));
                        }
                    }
                    let hidden = original.original_hidden();
                    if !same_type_with_budget(
                        copy.substitution
                            .types
                            .get(&hidden[0].0)
                            .ok_or_else(|| super::invalid(entries.body))?,
                        &body.ty,
                        work,
                    )
                    .map_err(|()| super::resource())?
                        || !same_effect_rows_with_budget(
                            copy.substitution
                                .rows
                                .get(&hidden[1].0)
                                .ok_or_else(|| super::invalid(entries.body))?,
                            rows.residual(),
                            work,
                        )
                        .map_err(|()| super::resource())?
                        || copy.substitution.pending.len() != rows.pending.len()
                    {
                        return Err(super::invalid(entries.body));
                    }
                    for (id, row) in &rows.pending {
                        if !same_effect_rows_with_budget(
                            row,
                            copy.substitution
                                .pending
                                .get(id)
                                .ok_or_else(|| super::invalid(entries.body))?,
                            work,
                        )
                        .map_err(|()| super::resource())?
                        {
                            return Err(super::invalid(entries.body));
                        }
                    }
                    for (frozen, actual) in original
                        .original_clause_projections()
                        .iter()
                        .zip(entries.clauses)
                    {
                        let expected = specialize_projection(
                            frozen,
                            &nodes,
                            &copy.freshening,
                            &copy.substitution,
                            &renaming,
                            work,
                        )?;
                        let actual = project_clause(actual, work)?;
                        if !expected.same(&actual, work)? {
                            return Err(super::invalid(actual.node));
                        }
                        proof.clauses.push(expected);
                    }
                    (original.original_program(), original.original_nodes(), 2)
                }
            };
            let mut declarations = LocalDeclarations::default();
            for (old, _) in copy.nodes {
                declarations.node(super::node(source, *old)?, work)?;
            }
            match copy.original {
                ProviderOriginalTemplate::Lifecycle(original, _) => {
                    retain_identity(&mut declarations.binders, original.parameter, work)?
                }
                ProviderOriginalTemplate::Handler(original) => {
                    retain_identity(
                        &mut declarations.binders,
                        original.original_state().id(),
                        work,
                    )?;
                    retain_identity(
                        &mut declarations.handlers,
                        original.original_handler(),
                        work,
                    )?;
                    for clause in original.original_clauses() {
                        retain_identity(&mut declarations.resumes, clause.resume(), work)?;
                        declarations.pattern(clause.pattern(), work)?;
                    }
                }
            }
            for frozen in originals {
                for metadata in &frozen.metadata {
                    declarations.foralls(metadata, &copy.substitution, work)?;
                }
            }
            declarations.authenticate(&copy.freshening, work)?;
            let mut lexicals = std::collections::HashSet::new();
            for owner in source.method_evidence.lexical_owners() {
                retain_identity(&mut lexicals, owner.source, work)?;
            }
            super::charge(work, copy.freshening.lexicals.len())?;
            if lexicals.len() != copy.freshening.lexicals.len()
                || copy
                    .freshening
                    .lexicals
                    .iter()
                    .any(|(old, _)| !lexicals.contains(old))
            {
                return Err(super::invalid(entries.body));
            }
            if phases[phase] {
                return Err(super::invalid(entries.body));
            }
            phases[phase] = true;
            if originals.len() != nodes.len() {
                return Err(super::invalid(entries.body));
            }
            for frozen in originals {
                let mut expected = specialize_projection(
                    frozen,
                    &nodes,
                    &copy.freshening,
                    &copy.substitution,
                    &renaming,
                    work,
                )?;
                if let Some(row) = copy.node_rows.get(&frozen.node) {
                    let actual = crate::types::substitute_row_for_template_with(
                        row,
                        &std::collections::HashMap::new(),
                        &std::collections::HashMap::new(),
                        &std::collections::HashMap::new(),
                        &renaming,
                        |cells| work.charge(cells),
                        || (),
                    )
                    .map_err(|()| super::resource())?
                    .map_err(|_| super::invalid(expected.node))?;
                    let Some(super::projection::Metadata::Row(recorded)) =
                        expected.metadata.get_mut(1)
                    else {
                        return Err(super::invalid(expected.node));
                    };
                    *recorded = actual;
                }
                let actual = project(
                    expected.node,
                    target_node(arena, target, expected.node)?,
                    work,
                )?;
                if !expected.same(&actual, work)? {
                    return Err(super::invalid(expected.node));
                }
                if matches!(
                    &target_node(arena, target, expected.node)?.kind,
                    crate::core::EffectExprKind::Operation(
                        crate::core::EffectOperation::ProviderStateAccess(_)
                    )
                ) {
                    super::charge(work, 1)?;
                    proof
                        .state_accesses
                        .try_reserve(1)
                        .map_err(|_| super::resource())?;
                    proof.state_accesses.push(expected.node);
                }
                proof.nodes.push(expected);
            }
            authenticate_catalog(
                copy,
                source,
                catalog,
                self.provider_projection_anchors(),
                &nodes,
                &renaming,
                &mut proof,
                work,
            )?;
        }
        if !phases.into_iter().all(|phase| phase) {
            return Err(super::invalid(entries.body));
        }
        let specialization = OriginalProviderSpecialization(std::sync::Arc::new(proof));
        let descriptor = super::AdmittedProviderScope {
            definition: std::sync::Arc::clone(&admission.definition),
            native: std::sync::Arc::clone(&admission.native),
            arguments: std::mem::take(&mut admission.arguments),
            identity: admission.identity,
            retained: std::mem::take(&mut admission.retained),
            native_effect: crate::types::clone_effect_instance_with_budget(
                &admission.native_effect,
                work,
            )
            .map_err(|()| super::resource())?,
            protocol: admission.protocol,
            specialization,
        };
        Ok(std::sync::Arc::new(descriptor))
    }
}
/// Caller payloads are outside the copied declaration scopes. Alpha targets
/// cannot capture their free or quantified identities after simultaneous sigma.
fn authenticate_caller_disjointness(
    copies: &[ProviderCopiedTemplate<'_>],
    answer: &crate::types::Type,
    effects: &crate::types::EffectRow,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    use crate::types::{EffectRowVariable, NominalTypeId, Type, TypeStructureNode, TypeVariableId};
    struct CallerIdentities {
        variables: std::collections::HashSet<TypeVariableId>,
        nominals: std::collections::HashSet<NominalTypeId>,
    }
    impl CallerIdentities {
        fn component(
            &mut self,
            node: TypeStructureNode<'_>,
            work: &mut TypeWorkBudget,
        ) -> Result<bool, ()> {
            match node {
                TypeStructureNode::Type(Type::Variable(id)) => {
                    retain_identity(&mut self.variables, *id, work).map_err(|_| ())?
                }
                TypeStructureNode::Type(Type::Forall(parameters, _)) => {
                    for (id, _) in parameters {
                        retain_identity(&mut self.variables, *id, work).map_err(|_| ())?;
                    }
                }
                TypeStructureNode::Type(Type::Nominal(id)) => {
                    retain_identity(&mut self.nominals, *id, work).map_err(|_| ())?
                }
                TypeStructureNode::Tail(tail) => {
                    if let EffectRowVariable::Rigid(id) = tail.variable() {
                        retain_identity(&mut self.variables, id, work).map_err(|_| ())?;
                    }
                }
                _ => {}
            }
            Ok(false)
        }
        fn ty(&mut self, ty: &Type, work: &mut TypeWorkBudget) -> Result<(), ValidationError> {
            crate::types::visit_type_structure_with_budget(ty, work, |node, work| {
                self.component(node, work)
            })
            .map_err(|()| super::resource())?;
            Ok(())
        }
        fn row(
            &mut self,
            row: &crate::types::EffectRow,
            work: &mut TypeWorkBudget,
        ) -> Result<(), ValidationError> {
            super::charge(
                work,
                row.known()
                    .len()
                    .checked_add(row.tail().map_or(0, |tail| tail.lacks().len()))
                    .and_then(|n| n.checked_add(1))
                    .ok_or_else(super::resource)?,
            )?;
            if let Some(tail) = row.tail() {
                self.component(TypeStructureNode::Tail(tail), work)
                    .map_err(|()| super::resource())?;
            }
            for instance in row
                .known()
                .iter()
                .chain(row.tail().into_iter().flat_map(|tail| tail.lacks()))
            {
                super::charge(work, instance.arguments().len())?;
                for argument in instance.arguments() {
                    crate::types::visit_argument_structure_with_budget(
                        argument,
                        work,
                        |node, work| self.component(node, work),
                    )
                    .map_err(|()| super::resource())?;
                }
            }
            Ok(())
        }
    }
    let mut caller = CallerIdentities {
        variables: std::collections::HashSet::new(),
        nominals: std::collections::HashSet::new(),
    };
    caller.ty(answer, work)?;
    caller.row(effects, work)?;
    for copy in copies {
        super::charge(
            work,
            copy.substitution
                .types
                .len()
                .checked_add(copy.substitution.rows.len())
                .and_then(|n| n.checked_add(copy.substitution.pending.len()))
                .ok_or_else(super::resource)?,
        )?;
        for ty in copy.substitution.types.values() {
            caller.ty(ty, work)?;
        }
        for row in copy
            .substitution
            .rows
            .values()
            .chain(copy.substitution.pending.values())
        {
            caller.row(row, work)?;
        }
    }
    for copy in copies {
        super::charge(
            work,
            copy.freshening
                .types
                .len()
                .checked_add(copy.freshening.nominals.len())
                .ok_or_else(super::resource)?,
        )?;
        if copy
            .freshening
            .types
            .iter()
            .any(|(_, fresh, _)| caller.variables.contains(fresh))
            || copy
                .freshening
                .nominals
                .iter()
                .any(|(_, fresh)| caller.nominals.contains(fresh))
        {
            return Err(ValidationError::new(
                crate::core::ValidationReason::Scope,
                None,
            ));
        }
    }
    Ok(())
}
/// Local targets must be fresh across the complete copied scope, including
/// every original phase namespace; distinct source phases may share originals.
fn authenticate_disjoint_freshening(
    copies: &[ProviderCopiedTemplate<'_>],
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    fn namespace<T: Copy + Eq + std::hash::Hash>(
        pairs: impl Clone + Iterator<Item = (T, T)>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        let count = pairs.clone().try_fold(0usize, |count, _| {
            super::charge(work, 1)?;
            count.checked_add(1).ok_or_else(super::resource)
        })?;
        super::charge(work, count.checked_mul(3).ok_or_else(super::resource)?)?;
        let mut originals = std::collections::HashSet::new();
        let mut targets = std::collections::HashSet::new();
        originals
            .try_reserve(count)
            .map_err(|_| super::resource())?;
        targets.try_reserve(count).map_err(|_| super::resource())?;
        for (old, _) in pairs.clone() {
            originals.insert(old);
        }
        for (_, fresh) in pairs {
            if originals.contains(&fresh) || !targets.insert(fresh) {
                return Err(ValidationError::new(
                    crate::core::ValidationReason::Scope,
                    None,
                ));
            }
        }
        Ok(())
    }
    namespace(
        copies
            .iter()
            .flat_map(|copy| copy.freshening.binders.iter().copied()),
        work,
    )?;
    namespace(
        copies.iter().flat_map(|copy| {
            copy.freshening
                .types
                .iter()
                .map(|(old, fresh, _)| (*old, *fresh))
        }),
        work,
    )?;
    namespace(
        copies
            .iter()
            .flat_map(|copy| copy.freshening.handlers.iter().copied()),
        work,
    )?;
    namespace(
        copies
            .iter()
            .flat_map(|copy| copy.freshening.resumes.iter().copied()),
        work,
    )?;
    namespace(
        copies
            .iter()
            .flat_map(|copy| copy.freshening.nominals.iter().copied()),
        work,
    )?;
    namespace(
        copies
            .iter()
            .flat_map(|copy| copy.freshening.lexicals.iter().copied()),
        work,
    )
}
fn authenticate_actual(
    id: crate::types::TypeVariableId,
    actual: &crate::types::KindedArgument,
    substitution: &ProviderTemplateSubstitution<'_>,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let same = match actual {
        crate::types::KindedArgument::TypeArg(ty) => crate::types::same_type_with_budget(
            ty,
            substitution.types.get(&id).ok_or_else(super::resource)?,
            work,
        )
        .map_err(|()| super::resource())?,
        crate::types::KindedArgument::RowArg(row) => crate::types::same_effect_rows_with_budget(
            row,
            substitution.rows.get(&id).ok_or_else(super::resource)?,
            work,
        )
        .map_err(|()| super::resource())?,
    };
    if same {
        Ok(())
    } else {
        Err(ValidationError::new(
            crate::core::ValidationReason::TypeOperation,
            None,
        ))
    }
}
fn substitute_instance(
    instance: &crate::types::EffectInstance,
    sigma: &ProviderTemplateSubstitution<'_>,
    renaming: &crate::types::TemplateIdentityRenaming<'_>,
    work: &mut TypeWorkBudget,
) -> Result<crate::types::EffectInstance, ValidationError> {
    super::charge(
        work,
        instance
            .arguments()
            .len()
            .checked_mul(2)
            .ok_or_else(super::resource)?,
    )?;
    let mut guarded = Vec::new();
    guarded
        .try_reserve_exact(instance.arguments().len())
        .map_err(|_| super::resource())?;
    for arg in instance.arguments() {
        guarded.push(crate::types::IterativeArgumentOwner::new(
            crate::types::substitute_argument_for_template_with(
                arg,
                sigma.types,
                sigma.rows,
                sigma.pending,
                renaming,
                |n| work.charge(n),
                || (),
            )
            .map_err(|()| super::resource())?
            .map_err(|_| ValidationError::new(crate::core::ValidationReason::EffectRow, None))?,
        ));
    }
    let mut args = Vec::new();
    args.try_reserve_exact(guarded.len())
        .map_err(|_| super::resource())?;
    args.extend(
        guarded
            .into_iter()
            .map(crate::types::IterativeArgumentOwner::into_inner),
    );
    Ok(crate::types::EffectInstance::new_kinded(
        instance.effect(),
        args.into_boxed_slice(),
    ))
}
fn authenticate_catalog(
    copy: &ProviderCopiedTemplate<'_>,
    source: &UnvalidatedEffectProgram,
    target: &crate::core::dialect::MethodEvidenceCatalog,
    target_anchors: &[crate::core::dialect::MethodEvidenceAnchor],
    nodes: &std::collections::HashMap<NodeId, NodeId>,
    renaming: &crate::types::TemplateIdentityRenaming<'_>,
    proof: &mut SpecializationProof,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    super::charge(
        work,
        copy.occurrences
            .len()
            .checked_mul(2)
            .and_then(|n| n.checked_add(copy.catalog.len()))
            .ok_or_else(super::resource)?,
    )?;
    let mut slots = std::collections::HashMap::new();
    slots
        .try_reserve(copy.occurrences.len())
        .map_err(|_| super::resource())?;
    let mut targets = std::collections::HashSet::new();
    targets
        .try_reserve(copy.occurrences.len())
        .map_err(|_| super::resource())?;
    if copy.occurrences.len() != source.method_evidence.occurrences().len() {
        return Err(super::invalid(source.root));
    }
    for relocation in copy.occurrences {
        if slots
            .insert(relocation.original, relocation.copied)
            .is_some()
            || !targets.insert(relocation.copied)
        {
            return Err(super::invalid(source.root));
        }
        super::charge(work, target.final_occurrence_owners().len())?;
        if !target
            .final_occurrence_owners()
            .iter()
            .any(|owner| owner.storage_id() == relocation.copied)
        {
            return Err(super::invalid(source.root));
        }
        let original = source
            .method_evidence
            .occurrence(relocation.original)
            .ok_or_else(|| super::invalid(source.root))?;
        let actual = target
            .occurrence(relocation.copied)
            .ok_or_else(|| super::invalid(source.root))?;
        let application =
            specialized_application(&original.checked_application, copy, renaming, work)?;
        let mut arguments = Vec::new();
        super::charge(
            work,
            original
                .method_arguments
                .len()
                .checked_add(2)
                .ok_or_else(super::resource)?,
        )?;
        arguments
            .try_reserve_exact(original.method_arguments.len())
            .map_err(|_| super::resource())?;
        for argument in &original.method_arguments {
            let argument = crate::types::substitute_type_for_template_with(
                argument,
                copy.substitution.types,
                copy.substitution.rows,
                copy.substitution.pending,
                renaming,
                |n| work.charge(n),
                || (),
            )
            .map_err(|()| super::resource())?
            .map_err(|_| super::invalid(source.root))?;
            arguments.push(crate::types::IterativeTypeOwner::new(argument));
        }
        let value_type = original
            .checked_value_type
            .as_ref()
            .map(|ty| {
                let ty = crate::types::substitute_type_for_template_with(
                    ty,
                    copy.substitution.types,
                    copy.substitution.rows,
                    copy.substitution.pending,
                    renaming,
                    |n| work.charge(n),
                    || (),
                )
                .map_err(|()| super::resource())?
                .map_err(|_| super::invalid(source.root))?;
                Ok::<_, ValidationError>(crate::types::IterativeTypeOwner::new(ty))
            })
            .transpose()?;
        let mut constraints =
            crate::interface::InterfaceConstraintBudget::with_limit(work.remaining());
        let projected = original.selection.specialize_with(
            work,
            &mut constraints,
            |ty, work| {
                crate::types::substitute_type_for_template_with(
                    ty,
                    copy.substitution.types,
                    copy.substitution.rows,
                    copy.substitution.pending,
                    renaming,
                    |n| work.charge(n),
                    || (),
                )
                .map_err(|()| super::resource())?
                .map_err(|_| super::invalid(source.root))
            },
            |argument, work| {
                crate::types::substitute_argument_for_template_with(
                    argument,
                    copy.substitution.types,
                    copy.substitution.rows,
                    copy.substitution.pending,
                    renaming,
                    |n| work.charge(n),
                    || (),
                )
                .map_err(|()| super::resource())?
                .map_err(|_| super::invalid(source.root))
            },
            |lexical, work| renamed(lexical, copy.freshening.lexicals, work),
            super::resource,
            super::resource,
            || super::invalid(source.root),
        );
        super::charge(work, constraints.used())?;
        let selection = projected?;
        super::charge(
            work,
            copy.original_slots
                .len()
                .checked_add(original.method_arguments.len())
                .and_then(|n| n.checked_add(2))
                .ok_or_else(super::resource)?,
        )?;
        let mut pins = copy
            .original_slots
            .iter()
            .filter(|slot| slot.storage_id() == relocation.original);
        let pin = pins.next().ok_or_else(|| super::invalid(source.root))?;
        if pins.next().is_some() {
            return Err(super::invalid(source.root));
        }
        let allocation = pin.retain_unpublished().unwrap_or_else(|| pin.clone());
        let mut source_arguments = Vec::new();
        source_arguments
            .try_reserve_exact(original.method_arguments.len())
            .map_err(|_| super::resource())?;
        for argument in &original.method_arguments {
            source_arguments.push(crate::types::IterativeTypeOwner::new(
                crate::types::clone_type_with_budget(argument, work)
                    .map_err(|()| super::resource())?,
            ));
        }
        let source_value = original
            .checked_value_type
            .as_ref()
            .map(|ty| {
                crate::types::clone_type_with_budget(ty, work)
                    .map(crate::types::IterativeTypeOwner::new)
                    .map_err(|()| super::resource())
            })
            .transpose()?;
        let source_occurrence = OriginalOccurrence {
            allocation,
            application: original
                .checked_application
                .clone_with_budget(work)
                .map_err(|()| super::resource())?,
            selection: original.selection.clone(),
            method: original.checked_method,
            arguments: source_arguments,
            value: source_value,
        };
        let expected = SpecializedOccurrence {
            slot: relocation.copied,
            original: source_occurrence,
            selection,
            application,
            arguments,
            value_type,
            method: original.checked_method,
            scope: owner(original.scope, &copy.freshening, work)?,
            scope_binder: original
                .scope_binder
                .map(|id| renamed(id, copy.freshening.binders, work))
                .transpose()?,
            target: owner(original.target_owner, &copy.freshening, work)?,
            requirement: original.target_requirement,
        };
        if !expected.same(actual, work)? {
            return Err(super::invalid(source.root));
        }
        super::charge(work, 1)?;
        proof
            .occurrences
            .try_reserve(1)
            .map_err(|_| super::resource())?;
        proof.occurrences.push(expected);
    }
    let mut anchors = std::collections::HashMap::new();
    anchors
        .try_reserve(copy.catalog.len())
        .map_err(|_| super::resource())?;
    for relocation in copy.catalog {
        if anchors
            .insert(relocation.original_anchor, relocation)
            .is_some()
        {
            return Err(super::invalid(source.root));
        }
    }
    for (ordinal, original) in source.method_evidence_anchors.iter().enumerate() {
        let Some(node) = nodes.get(&original.node).copied() else {
            continue;
        };
        let relocation = anchors
            .remove(&ordinal)
            .ok_or_else(|| super::invalid(node))?;
        let expected_role = match original.role {
            crate::core::dialect::MethodEvidenceAnchorRole::LexicalCaptureUse {
                owner,
                ordinal,
            } => {
                let defining = source
                    .method_evidence
                    .lexical_owners()
                    .get(owner)
                    .ok_or_else(|| super::invalid(node))?;
                let copied_source = renamed(defining.source, copy.freshening.lexicals, work)?;
                super::charge(work, target.lexical_owners().len())?;
                let owner = target
                    .lexical_owners()
                    .iter()
                    .position(|candidate| {
                        candidate.source == copied_source && candidate.method == defining.method
                    })
                    .ok_or_else(|| super::invalid(node))?;
                crate::core::dialect::MethodEvidenceAnchorRole::LexicalCaptureUse { owner, ordinal }
            }
            other => role(other, &copy.freshening, nodes, work)?,
        };
        let expected_owner = owner(original.owner, &copy.freshening, work)?;
        let occurrence = original
            .occurrence
            .map(|key| slots.get(&key).copied().ok_or_else(|| super::invalid(node)))
            .transpose()?;
        let claimed_role = relocate_claimed_role_nodes(relocation.role, nodes, work)?;
        if relocation.owner != expected_owner
            || relocation.requirement != original.requirement
            || claimed_role != expected_role
            || relocation.occurrence != occurrence
        {
            return Err(super::invalid(node));
        }
        let expected = SpecializedAnchor {
            node,
            owner: expected_owner,
            requirement: original.requirement,
            method: original.method,
            application: specialized_application(&original.application, copy, renaming, work)?,
            role: expected_role,
            occurrence,
        };
        super::charge(work, target_anchors.len())?;
        let mut matching = target_anchors
            .iter()
            .filter(|actual| actual.node == node && actual.method == original.method);
        let actual = matching.next().ok_or_else(|| super::invalid(node))?;
        if matching.next().is_some() || !expected.same(actual, work)? {
            return Err(super::invalid(node));
        }
        super::charge(work, 1)?;
        proof
            .anchors
            .try_reserve(1)
            .map_err(|_| super::resource())?;
        proof.anchors.push(expected);
    }
    if !anchors.is_empty() {
        return Err(super::invalid(source.root));
    }
    Ok(())
}
impl SpecializedOccurrence {
    fn same(
        &self,
        actual: &crate::core::dialect::MethodEvidenceOccurrence,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        if self.slot != actual.slot
            || !same_selection(&self.selection, &actual.selection, work)?
            || self.method != actual.checked_method
            || self.scope != actual.scope
            || self.scope_binder != actual.scope_binder
            || self.target != actual.target_owner
            || self.requirement != actual.target_requirement
            || self.arguments.len() != actual.method_arguments.len()
            || !same_application(&self.application, &actual.checked_application, work)?
        {
            return Ok(false);
        }
        for (expected, actual) in self.arguments.iter().zip(&actual.method_arguments) {
            if !crate::types::same_type_with_budget(expected, actual, work)
                .map_err(|()| super::resource())?
            {
                return Ok(false);
            }
        }
        match (&self.value_type, &actual.checked_value_type) {
            (None, None) => Ok(true),
            (Some(expected), Some(actual)) => {
                crate::types::same_type_with_budget(expected, actual, work)
                    .map_err(|()| super::resource())
            }
            _ => Ok(false),
        }
    }
}
impl SpecializedAnchor {
    fn same(
        &self,
        actual: &crate::core::dialect::MethodEvidenceAnchor,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        Ok(self.node == actual.node
            && self.owner == actual.owner
            && self.requirement == actual.requirement
            && self.method == actual.method
            && self.role == actual.role
            && self.occurrence == actual.occurrence
            && same_application(&self.application, &actual.application, work)?)
    }
}
impl OriginalProviderSpecialization {
    pub(crate) fn authenticate(
        &self,
        program: &UnvalidatedEffectProgram,
        scope_node: NodeId,
        scope: &ProviderScopeNode,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        let proof = &self.0;
        if proof.arena != program.arena
            || !std::sync::Arc::ptr_eq(&proof.catalog, &program.method_evidence)
            || proof.definition != scope.descriptor.definition().id
            || proof.acquire != scope.acquire.body
            || proof.finish != scope.finish.body
            || proof.body != scope.handler.body()
            || proof.handler != scope.handler.id()
            || proof.clauses.len() != scope.handler.clauses().len()
        {
            return Err(super::invalid(scope_node));
        }
        super::charge(
            work,
            proof
                .nodes
                .len()
                .checked_add(proof.occurrences.len())
                .and_then(|n| n.checked_add(proof.anchors.len()))
                .ok_or_else(super::resource)?,
        )?;
        for expected in &proof.nodes {
            let actual = super::projection::project(
                expected.node,
                super::node(program, expected.node)?,
                work,
            )?;
            if !expected.same(&actual, work)? {
                return Err(super::invalid(expected.node));
            }
        }
        for (expected, (node, binder)) in proof.parameters.iter().zip([
            (scope.acquire.body, &scope.acquire.parameter),
            (scope.finish.body, &scope.finish.parameter),
            (proof.parameters[2].node, &scope.handler_state),
        ]) {
            if !expected.same(
                &super::projection::project_binder(node, binder, work)?,
                work,
            )? {
                return Err(super::invalid(node));
            }
        }
        for (expected, actual) in proof.clauses.iter().zip(scope.handler.clauses()) {
            if !expected.same(&super::projection::project_clause(actual, work)?, work)? {
                return Err(super::invalid(expected.node));
            }
        }
        for expected in &proof.occurrences {
            expected.original.authenticate_publication(work)?;
            if !expected.same(
                program
                    .method_evidence
                    .occurrence(expected.slot)
                    .ok_or_else(|| super::invalid(scope_node))?,
                work,
            )? {
                return Err(super::invalid(scope_node));
            }
        }
        for expected in &proof.anchors {
            super::charge(work, program.method_evidence_anchors.len())?;
            let mut matching = program
                .method_evidence_anchors
                .iter()
                .filter(|anchor| anchor.node == expected.node && anchor.method == expected.method);
            if !expected.same(
                matching
                    .next()
                    .ok_or_else(|| super::invalid(expected.node))?,
                work,
            )? || matching.next().is_some()
            {
                return Err(super::invalid(expected.node));
            }
        }
        Ok(())
    }
    pub(crate) fn authenticates_state_access(
        &self,
        program: &UnvalidatedEffectProgram,
        scope: &ProviderScopeNode,
        access: NodeId,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        if self.0.arena != program.arena || self.0.definition != scope.descriptor.definition().id {
            return Ok(false);
        }
        super::charge(work, self.0.state_accesses.len())?;
        if !self.0.state_accesses.contains(&access) {
            return Ok(false);
        }
        super::charge(work, self.0.nodes.len())?;
        let expected = self
            .0
            .nodes
            .iter()
            .find(|node| node.node == access)
            .ok_or_else(|| super::invalid(access))?;
        expected.same(
            &super::projection::project(access, super::node(program, access)?, work)?,
            work,
        )
    }
    pub(crate) fn relocate(
        &self,
        remapped: &[Option<NodeId>],
        work: &mut TypeWorkBudget,
    ) -> Result<Self, BuildError> {
        self.relocate_checked(remapped, work).map_err(|error| {
            if error.reason() == crate::core::ValidationReason::Resource {
                BuildError::TypeWorkExceeded
            } else {
                BuildError::InvalidPayload
            }
        })
    }
    fn relocate_checked(
        &self,
        remapped: &[Option<NodeId>],
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        let old = &self.0;
        super::charge(
            work,
            remapped
                .len()
                .checked_add(old.nodes.len())
                .and_then(|n| n.checked_add(old.clauses.len()))
                .and_then(|n| n.checked_add(old.anchors.len()))
                .and_then(|n| n.checked_add(old.occurrences.len()))
                .and_then(|n| n.checked_add(old.state_accesses.len()))
                .and_then(|n| n.checked_add(4))
                .ok_or_else(super::resource)?,
        )?;
        let mut nodes = std::collections::HashMap::new();
        nodes
            .try_reserve(remapped.len())
            .map_err(|_| super::resource())?;
        for (ordinal, new) in remapped.iter().enumerate() {
            if let Some(new) = new {
                nodes.insert(
                    NodeId::new(
                        old.arena,
                        u32::try_from(ordinal).map_err(|_| super::resource())?,
                    ),
                    *new,
                );
            }
        }
        let empty_types = std::collections::HashMap::new();
        let empty_rows = std::collections::HashMap::new();
        let empty_pending = std::collections::HashMap::new();
        let empty_variables = std::collections::HashMap::new();
        let empty_nominals = std::collections::HashMap::new();
        let sigma = ProviderTemplateSubstitution {
            types: &empty_types,
            rows: &empty_rows,
            pending: &empty_pending,
        };
        let fresh = ProviderFreshening {
            binders: &[],
            types: &[],
            handlers: &[],
            resumes: &[],
            nominals: &[],
            lexicals: &[],
        };
        let renaming = crate::types::TemplateIdentityRenaming {
            variables: &empty_variables,
            nominals: &empty_nominals,
        };
        let mut copied_nodes = Vec::new();
        copied_nodes
            .try_reserve_exact(old.nodes.len())
            .map_err(|_| super::resource())?;
        for node in &old.nodes {
            copied_nodes.push(specialize_projection(
                node, &nodes, &fresh, &sigma, &renaming, work,
            )?);
        }
        let mut clauses = Vec::new();
        clauses
            .try_reserve_exact(old.clauses.len())
            .map_err(|_| super::resource())?;
        for clause in &old.clauses {
            clauses.push(specialize_projection(
                clause, &nodes, &fresh, &sigma, &renaming, work,
            )?);
        }
        let parameters = [
            specialize_projection(&old.parameters[0], &nodes, &fresh, &sigma, &renaming, work)?,
            specialize_projection(&old.parameters[1], &nodes, &fresh, &sigma, &renaming, work)?,
            specialize_projection(&old.parameters[2], &nodes, &fresh, &sigma, &renaming, work)?,
        ];
        let mut occurrences = Vec::new();
        occurrences
            .try_reserve_exact(old.occurrences.len())
            .map_err(|_| super::resource())?;
        for original in &old.occurrences {
            let mut arguments = Vec::new();
            arguments
                .try_reserve_exact(original.arguments.len())
                .map_err(|_| super::resource())?;
            for argument in &original.arguments {
                arguments.push(crate::types::IterativeTypeOwner::new(
                    crate::types::clone_type_with_budget(argument, work)
                        .map_err(|()| super::resource())?,
                ));
            }
            super::charge(work, 2)?;
            occurrences.push(SpecializedOccurrence {
                slot: original.slot,
                original: original.original.copy(work)?,
                selection: original.selection.clone(),
                application: original
                    .application
                    .clone_with_budget(work)
                    .map_err(|()| super::resource())?,
                arguments,
                value_type: original
                    .value_type
                    .as_ref()
                    .map(|ty| {
                        crate::types::clone_type_with_budget(ty, work)
                            .map(crate::types::IterativeTypeOwner::new)
                            .map_err(|()| super::resource())
                    })
                    .transpose()?,
                method: original.method,
                scope: original.scope,
                scope_binder: original.scope_binder,
                target: original.target,
                requirement: original.requirement,
            });
        }
        let mut anchors = Vec::new();
        anchors
            .try_reserve_exact(old.anchors.len())
            .map_err(|_| super::resource())?;
        for original in &old.anchors {
            anchors.push(SpecializedAnchor {
                node: mapped(&nodes, original.node)?,
                owner: original.owner,
                requirement: original.requirement,
                method: original.method,
                application: original
                    .application
                    .clone_with_budget(work)
                    .map_err(|()| super::resource())?,
                role: role(original.role, &fresh, &nodes, work)?,
                occurrence: original.occurrence,
            });
        }
        let mut accesses = Vec::new();
        accesses
            .try_reserve_exact(old.state_accesses.len())
            .map_err(|_| super::resource())?;
        for node in &old.state_accesses {
            accesses.push(mapped(&nodes, *node)?);
        }
        let body = mapped(&nodes, old.body)?;
        Ok(Self(std::sync::Arc::new(SpecializationProof {
            arena: body.arena(),
            catalog: std::sync::Arc::clone(&old.catalog),
            definition: old.definition,
            acquire: mapped(&nodes, old.acquire)?,
            finish: mapped(&nodes, old.finish)?,
            body,
            handler: old.handler,
            nodes: copied_nodes,
            parameters,
            clauses,
            occurrences,
            anchors,
            state_accesses: accesses,
        })))
    }
}
#[derive(Default)]
struct LocalDeclarations {
    binders: std::collections::HashSet<crate::resolved::BinderId>,
    variables: std::collections::HashMap<crate::types::TypeVariableId, crate::types::Kind>,
    handlers: std::collections::HashSet<crate::core::HandlerId>,
    resumes: std::collections::HashSet<crate::resolved::ResumeId>,
    nominals: std::collections::HashSet<crate::types::NominalTypeId>,
}
fn retain_identity<T: Eq + std::hash::Hash>(
    set: &mut std::collections::HashSet<T>,
    id: T,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    super::charge(work, 2)?;
    set.try_reserve(1).map_err(|_| super::resource())?;
    set.insert(id);
    Ok(())
}
impl LocalDeclarations {
    fn variable(
        &mut self,
        id: crate::types::TypeVariableId,
        kind: &crate::types::Kind,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        super::charge(work, 2)?;
        if let Some(previous) = self.variables.get(&id) {
            if !crate::types::same_kind_with_budget(previous, kind, work)
                .map_err(|()| super::resource())?
            {
                return Err(ValidationError::new(
                    crate::core::ValidationReason::TypeOperation,
                    None,
                ));
            }
        } else {
            self.variables
                .try_reserve(1)
                .map_err(|_| super::resource())?;
            self.variables.insert(
                id,
                crate::types::clone_kind_with_budget(kind, work).map_err(|()| super::resource())?,
            );
        }
        Ok(())
    }
    fn pattern(
        &mut self,
        pattern: &crate::core::CorePattern,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        for binder in pattern.binder_iter() {
            retain_identity(&mut self.binders, binder.id(), work)?;
        }
        Ok(())
    }
    fn node(
        &mut self,
        node: &crate::core::dialect::StoredNode<crate::core::EffectOperationFamily>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        use crate::core::{
            EffectExprKind as E, EffectOperation as O, PureComputation as C, PureExprKind as P,
            PureValue as V,
        };
        match &node.kind {
            E::Pure(P::Value(V::Function(function))) => {
                retain_identity(&mut self.binders, function.parameter().id(), work)?
            }
            E::Pure(P::Computation(C::Bind(binding))) => {
                retain_identity(&mut self.binders, binding.binder().id(), work)?
            }
            E::Pure(P::Computation(C::RecursiveBind(group))) => {
                for member in group.members() {
                    retain_identity(&mut self.binders, member.binder().id(), work)?;
                }
            }
            E::Pure(P::Computation(C::Match(matching))) => {
                for arm in matching.arms() {
                    self.pattern(arm.pattern(), work)?;
                }
            }
            E::Pure(P::Computation(C::TypeAbstraction(abstraction))) => {
                for (id, kind) in abstraction.parameters() {
                    self.variable(*id, kind, work)?;
                }
            }
            E::Pure(P::Computation(C::LocalNominalScope(scope))) => {
                retain_identity(&mut self.nominals, scope.owner(), work)?
            }
            E::Operation(O::Handler(handler)) => {
                retain_identity(&mut self.handlers, handler.id(), work)?;
                for clause in handler.clauses() {
                    retain_identity(&mut self.resumes, clause.resume(), work)?;
                    self.pattern(clause.pattern(), work)?;
                }
            }
            E::Operation(O::Resource(resource)) => {
                retain_identity(&mut self.binders, resource.handle.id(), work)?
            }
            _ => {}
        }
        Ok(())
    }
    fn foralls(
        &mut self,
        metadata: &super::projection::Metadata,
        sigma: &ProviderTemplateSubstitution<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        use crate::types::{Type, TypeStructureNode, TypeVariableId};
        let mut visit =
            |node: TypeStructureNode<'_>, work: &mut TypeWorkBudget| -> Result<bool, ()> {
                if let TypeStructureNode::Type(Type::Forall(parameters, _)) = node {
                    for (id, kind) in parameters {
                        if matches!(id, TypeVariableId::Generated(_))
                            && !sigma.types.contains_key(id)
                            && !sigma.rows.contains_key(id)
                        {
                            self.variable(*id, kind, work).map_err(|_| ())?;
                        }
                    }
                }
                Ok(false)
            };
        match metadata {
            super::projection::Metadata::Type(ty) => {
                crate::types::visit_type_structure_with_budget(ty, work, &mut visit)
                    .map_err(|()| super::resource())?;
            }
            super::projection::Metadata::Argument(argument) => {
                crate::types::visit_argument_structure_with_budget(argument, work, &mut visit)
                    .map_err(|()| super::resource())?;
            }
            super::projection::Metadata::Row(row) => {
                super::charge(
                    work,
                    row.known()
                        .len()
                        .checked_add(row.tail().map_or(0, |tail| tail.lacks().len()))
                        .and_then(|n| n.checked_add(1))
                        .ok_or_else(super::resource)?,
                )?;
                for instance in row
                    .known()
                    .iter()
                    .chain(row.tail().into_iter().flat_map(|tail| tail.lacks()))
                {
                    for argument in instance.arguments() {
                        crate::types::visit_argument_structure_with_budget(
                            argument, work, &mut visit,
                        )
                        .map_err(|()| super::resource())?;
                    }
                }
            }
            super::projection::Metadata::Kind(_) => {}
        }
        Ok(())
    }
    fn authenticate(
        &self,
        fresh: &ProviderFreshening<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        fn exact<T: Eq + std::hash::Hash>(
            declared: &std::collections::HashSet<T>,
            pairs: &[(T, T)],
            work: &mut TypeWorkBudget,
        ) -> Result<bool, ValidationError> {
            super::charge(work, pairs.len())?;
            Ok(
                declared.len() == pairs.len()
                    && pairs.iter().all(|(old, _)| declared.contains(old)),
            )
        }
        if !exact(&self.binders, fresh.binders, work)?
            || !exact(&self.handlers, fresh.handlers, work)?
            || !exact(&self.resumes, fresh.resumes, work)?
            || !exact(&self.nominals, fresh.nominals, work)?
        {
            return Err(ValidationError::new(
                crate::core::ValidationReason::Scope,
                None,
            ));
        }
        super::charge(work, fresh.types.len())?;
        if self.variables.len() != fresh.types.len() {
            return Err(ValidationError::new(
                crate::core::ValidationReason::TypeOperation,
                None,
            ));
        }
        for (old, _, kind) in fresh.types {
            if !crate::types::same_kind_with_budget(
                self.variables.get(old).ok_or_else(|| {
                    ValidationError::new(crate::core::ValidationReason::Scope, None)
                })?,
                kind,
                work,
            )
            .map_err(|()| super::resource())?
            {
                return Err(ValidationError::new(
                    crate::core::ValidationReason::TypeOperation,
                    None,
                ));
            }
        }
        Ok(())
    }
}
fn same_selection(
    expected: &crate::interface::EvidenceSelection,
    actual: &crate::interface::EvidenceSelection,
    work: &mut TypeWorkBudget,
) -> Result<bool, ValidationError> {
    use crate::interface::{EvidenceNode as N, EvidenceNodeId};
    if !expected.same_original_owner(actual)
        || expected.interface() != actual.interface()
        || expected.root() != actual.root()
        || expected.node_count() != actual.node_count()
        || expected.arguments().len() != actual.arguments().len()
    {
        return Ok(false);
    }
    super::charge(
        work,
        expected
            .node_count()
            .checked_add(expected.arguments().len())
            .ok_or_else(super::resource)?,
    )?;
    for (left, right) in expected.arguments().iter().zip(actual.arguments()) {
        if !crate::types::same_kinded_argument_with_budget(left, right, work)
            .map_err(|()| super::resource())?
        {
            return Ok(false);
        }
    }
    for ordinal in 0..expected.node_count() {
        let id = EvidenceNodeId::new(ordinal);
        match (expected.node(id), actual.node(id)) {
            (
                Some(N::Lexical {
                    source: a,
                    methods: am,
                }),
                Some(N::Lexical {
                    source: b,
                    methods: bm,
                }),
            ) => {
                super::charge(work, am.len())?;
                if a != b || am != bm {
                    return Ok(false);
                }
            }
            (
                Some(N::Abstract {
                    requirement: a,
                    methods: am,
                }),
                Some(N::Abstract {
                    requirement: b,
                    methods: bm,
                }),
            ) => {
                super::charge(work, am.len())?;
                if a != b || am != bm {
                    return Ok(false);
                }
            }
            (
                Some(N::Implementation {
                    implementation: a,
                    substitution: asub,
                    prerequisites: ap,
                    methods: am,
                }),
                Some(N::Implementation {
                    implementation: b,
                    substitution: bsub,
                    prerequisites: bp,
                    methods: bm,
                }),
            ) => {
                super::charge(
                    work,
                    asub.len()
                        .checked_add(ap.len())
                        .and_then(|n| n.checked_add(am.len()))
                        .ok_or_else(super::resource)?,
                )?;
                if a != b || asub.len() != bsub.len() || ap != bp || am != bm {
                    return Ok(false);
                }
                for (left, right) in asub.iter().zip(bsub) {
                    if left.parameter() != right.parameter()
                        || !crate::types::same_type_with_budget(
                            left.argument(),
                            right.argument(),
                            work,
                        )
                        .map_err(|()| super::resource())?
                    {
                        return Ok(false);
                    }
                }
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}
/// A bounded inventory for allocating copied identities. It is a view of
/// original declaration spaces, not a copying or execution certificate.
pub(crate) struct ProviderLocalInventory {
    pub(crate) binders: Box<[crate::resolved::BinderId]>,
    pub(crate) types: Box<[(crate::types::TypeVariableId, crate::types::Kind)]>,
    pub(crate) handlers: Box<[crate::core::HandlerId]>,
    pub(crate) resumes: Box<[crate::resolved::ResumeId]>,
    pub(crate) nominals: Box<[crate::types::NominalTypeId]>,
    pub(crate) lexicals: Box<[crate::interface::LexicalEvidenceId]>,
}
impl ProviderOriginalTemplate<'_> {
    pub(crate) fn local_identities(
        &self,
        sigma: &ProviderTemplateSubstitution<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<ProviderLocalInventory, ValidationError> {
        let (source, originals) = match self {
            Self::Lifecycle(original, source) => (*source, original.nodes.as_slice()),
            Self::Handler(original) => (original.original_program(), original.original_nodes()),
        };
        let mut declarations = LocalDeclarations::default();
        for original in originals {
            declarations.node(super::node(source, original.node)?, work)?;
            for metadata in &original.metadata {
                declarations.foralls(metadata, sigma, work)?;
            }
        }
        match self {
            Self::Lifecycle(original, _) => {
                retain_identity(&mut declarations.binders, original.parameter, work)?
            }
            Self::Handler(original) => {
                retain_identity(
                    &mut declarations.binders,
                    original.original_state().id(),
                    work,
                )?;
                retain_identity(
                    &mut declarations.handlers,
                    original.original_handler(),
                    work,
                )?;
                for clause in original.original_clauses() {
                    retain_identity(&mut declarations.resumes, clause.resume(), work)?;
                    declarations.pattern(clause.pattern(), work)?;
                }
            }
        }
        let mut lexical = std::collections::HashSet::new();
        for owner in source.method_evidence.lexical_owners() {
            retain_identity(&mut lexical, owner.source, work)?;
        }
        fn array<T>(
            set: std::collections::HashSet<T>,
            work: &mut TypeWorkBudget,
        ) -> Result<Box<[T]>, ValidationError> {
            super::charge(work, set.len())?;
            let mut values = Vec::new();
            values
                .try_reserve_exact(set.len())
                .map_err(|_| super::resource())?;
            values.extend(set);
            Ok(values.into_boxed_slice())
        }
        super::charge(work, declarations.variables.len())?;
        let mut types = Vec::new();
        types
            .try_reserve_exact(declarations.variables.len())
            .map_err(|_| super::resource())?;
        types.extend(declarations.variables);
        Ok(ProviderLocalInventory {
            binders: array(declarations.binders, work)?,
            types: types.into_boxed_slice(),
            handlers: array(declarations.handlers, work)?,
            resumes: array(declarations.resumes, work)?,
            nominals: array(declarations.nominals, work)?,
            lexicals: array(lexical, work)?,
        })
    }
}

#[cfg(test)]
mod executable_scope_tests {
    use super::*;
    use crate::{
        core::{
            EffectExprKind, EffectOperation, PureExprKind, PureValue, ValidatedEffectProgram,
            transform::{fold_effect_literal_primitives, identity_effect_traversal},
            validate_effect_modules,
        },
        elaborate::{
            ProviderCodeAvailability, check_module_with_budget_and_provider_codes, link_modules,
        },
        foreign::{ForeignRegistrations, provider_manifest, sqlite_manifest},
        interface::InterfaceConstraintBudget,
        module::{ForeignRegistrationId, ModuleGraph, ModuleRoots, load_module_graph},
        pattern::UsefulnessBudget,
        resolve::{DependencyExports, resolve_module_with_budget},
        resolved::CheckedModule,
        types::{Type, clone_effect_instance_with_budget, clone_kinded_arguments_with_budget},
    };
    use std::{path::PathBuf, sync::Arc};

    fn sqlite_scopes() -> (ModuleGraph, ValidatedEffectProgram) {
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/provider-experiments/sqlite-copying/simultaneous-entry.ash");
        let roots = ModuleRoots::empty().with_foreign_registrations(
            ForeignRegistrations::new([
                provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
                sqlite_manifest(ForeignRegistrationId::new(2)).unwrap(),
            ])
            .unwrap(),
        );
        let graph = load_module_graph(&entry, &roots).unwrap();
        let mut checked = Vec::<CheckedModule>::new();
        let mut availability = ProviderCodeAvailability::default();
        let mut resolution = TypeWorkBudget::default();
        let mut checking = TypeWorkBudget::default();
        let mut constraints = InterfaceConstraintBudget::default();
        let mut coverage = UsefulnessBudget::default();
        for loaded in graph.modules() {
            let dependencies = loaded
                .dependencies()
                .iter()
                .map(|edge| {
                    DependencyExports::new(
                        edge,
                        checked
                            .iter()
                            .find(|module| module.module() == edge.target())
                            .unwrap()
                            .exports(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module_with_budget(
                loaded,
                &dependencies,
                &mut resolution,
                &mut constraints,
            )
            .unwrap();
            let module = check_module_with_budget_and_provider_codes(
                resolved,
                &availability,
                &mut checking,
                &mut coverage,
                &mut constraints,
            )
            .unwrap();
            if let Some(code) = module.provider_code() {
                availability
                    .retain(module.module(), code, &mut checking)
                    .unwrap();
            }
            checked.push(module);
        }
        let linked = crate::evidence_validation::validate_interface_evidence(
            link_modules(checked, graph.entry()).unwrap(),
        )
        .unwrap();
        let mut elaborator =
            crate::elaborate::EffectElaborator::for_module_program(&linked).unwrap();
        let typed = elaborator
            .synthesize_effect_module_program(&linked)
            .unwrap();
        let unchecked = elaborator.finish(typed.node).unwrap();
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
        let program = validate_effect_modules(unchecked, &sources, &relation).unwrap();
        (graph, program)
    }

    #[test]
    fn sqlite_scope_transforms_revalidate_and_same_typed_template_forgery_is_rejected() {
        let (graph, program) = sqlite_scopes();
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
        for transform in [identity_effect_traversal, fold_effect_literal_primitives] {
            let rebuilt = transform(&program).unwrap();
            validate_effect_modules(rebuilt, &sources, &relation)
                .expect("scope projection and catalog relocation must survive ordinary transforms");
        }
        let mut forged = identity_effect_traversal(&program).unwrap();
        let sealed_nodes = forged
            .nodes
            .iter()
            .find_map(|node| {
                let EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) = &node.kind
                else {
                    return None;
                };
                let proof = &scope.descriptor.specialization()?.0;
                proof.nodes.iter().find_map(|projection| {
                    let stored = &forged.nodes[projection.node.index().unwrap()];
                    let EffectExprKind::Pure(PureExprKind::Value(PureValue::Constructor(value))) =
                        &stored.kind
                    else {
                        return None;
                    };
                    let original = value.constructor();
                    if stored.ty != Type::Nominal(original.owner()) {
                        return None;
                    }
                    let replacement = forged.registry.constructors().iter().find(|candidate| {
                        candidate.id.owner() == original.owner()
                            && candidate.id != original
                            && candidate.payload.is_none()
                    })?;
                    Some((projection.node, replacement.id))
                })
            })
            .expect("SQLite handler has distinct nullary results with the same declared type");
        let (node, replacement) = sealed_nodes;
        forged.nodes[node.index().unwrap()].kind = EffectExprKind::Pure(PureExprKind::Value(
            PureValue::Constructor(crate::core::ConstructorNode::new(replacement)),
        ));
        let failure = validate_effect_modules(forged, &sources, &relation).expect_err(
            "a well-typed constructor replacement must not forge original-template authority",
        );
        assert_eq!(
            failure.reason(),
            crate::core::ValidationReason::ResourceEscape
        );
        assert_eq!(failure.node(), Some(node));
    }

    #[test]
    fn sqlite_scope_preparation_and_another_occurrences_proof_cannot_authorize_execution() {
        let (graph, program) = sqlite_scopes();
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
        let mut prepared = identity_effect_traversal(&program).unwrap();
        let scope = prepared
            .nodes
            .iter_mut()
            .find_map(|node| match &mut node.kind {
                EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) => Some(scope),
                _ => None,
            })
            .unwrap();
        let original = scope.descriptor.admitted_arc().unwrap();
        let mut work = TypeWorkBudget::default();
        let metadata = ProviderScopeAdmission {
            definition: Arc::clone(&original.definition),
            native: Arc::clone(&original.native),
            arguments: clone_kinded_arguments_with_budget(original.arguments.iter(), &mut work)
                .unwrap(),
            identity: original.identity,
            retained: original.retained.clone(),
            native_effect: clone_effect_instance_with_budget(&original.native_effect, &mut work)
                .unwrap(),
            protocol: original.protocol,
        };
        scope.descriptor =
            super::super::ProviderScopeAuthority::prepared(metadata, &mut work).unwrap();
        assert!(matches!(
            validate_effect_modules(prepared, &sources, &relation)
                .unwrap_err()
                .reason(),
            crate::core::ValidationReason::ResourceEscape | crate::core::ValidationReason::Registry
        ));

        let mut forged = identity_effect_traversal(&program).unwrap();
        let scopes = forged
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(ordinal, node)| match &node.kind {
                EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) => {
                    Some((ordinal, scope))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        let (target, donor) = scopes
            .iter()
            .find_map(|target| {
                scopes
                    .iter()
                    .find(|candidate| {
                        candidate.0 != target.0
                            && candidate.1.descriptor.definition().id
                                == target.1.descriptor.definition().id
                    })
                    .map(|candidate| {
                        (
                            target.0,
                            candidate.1.descriptor.specialization().unwrap().clone(),
                        )
                    })
            })
            .expect("simultaneous statements have distinct proofs for the same defining resource");
        let identity = forged
            .nodes
            .iter()
            .enumerate()
            .map(|(ordinal, _)| Some(NodeId::new(forged.arena, u32::try_from(ordinal).unwrap())))
            .collect::<Vec<_>>();
        let EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) =
            &mut forged.nodes[target].kind
        else {
            unreachable!();
        };
        let mut replacement = scope
            .descriptor
            .admitted_arc()
            .unwrap()
            .relocate(&identity, &mut TypeWorkBudget::default())
            .unwrap();
        replacement.specialization = donor;
        scope.descriptor = super::super::ProviderScopeAuthority::Admitted(Arc::new(replacement));
        assert_eq!(
            validate_effect_modules(forged, &sources, &relation)
                .unwrap_err()
                .reason(),
            crate::core::ValidationReason::ResourceEscape
        );
    }
}
