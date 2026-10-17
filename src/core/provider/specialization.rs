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
    pub(crate) families: Box<[ProviderFamilyAdmission]>,
}

/// Genuine original family authority at its source publication phase. The
/// private original allocation, not this borrowed wrapper, owns the proof.
pub(crate) struct ProviderPreparedFamilyOriginal<'a> {
    pub(crate) authority: &'a crate::elaborate::provider::ProviderFamilyOriginalAuthority,
    pub(crate) committed: bool,
}

struct ProviderFamilyContractView<'a> {
    identity: super::ProviderFamilyIdentity,
    application: &'a crate::interface::InterfaceApplication,
    requirements: &'a [crate::interface::CheckedRequirement],
    methods: &'a [(crate::interface::MethodId, crate::types::OperationId)],
    handler: &'a crate::core::validate::CheckedHandlerContractCertificate,
}

/// Compiler claims for one complete selected family goal. The original
/// certificate and final copied graph must authenticate these before admission.
#[derive(Debug, Eq, PartialEq)]
pub(crate) struct ProviderFamilyAdmission {
    pub(crate) identity: super::ProviderFamilyIdentity,
    pub(crate) application: crate::interface::InterfaceApplication,
    pub(crate) payload: crate::types::Type,
    pub(crate) native_effect: crate::types::EffectInstance,
    pub(crate) lexical: crate::interface::LexicalEvidenceId,
    pub(crate) requirements: Box<
        [(
            crate::interface::EvidenceSelection,
            crate::interface::EvidenceNodeId,
        )],
    >,
    pub(crate) selections: Box<
        [(
            crate::interface::EvidenceSelection,
            crate::interface::EvidenceNodeId,
        )],
    >,
}
impl ProviderFamilyAdmission {
    pub(super) fn clone_with_budget(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, crate::core::BuildError> {
        use crate::core::BuildError;
        let resource = || BuildError::TypeWorkExceeded;
        work.charge(
            self.requirements
                .len()
                .checked_add(self.selections.len())
                .and_then(|count| count.checked_add(1))
                .ok_or_else(resource)?,
        )
        .map_err(|()| resource())?;
        let mut requirements = Vec::new();
        requirements
            .try_reserve_exact(self.requirements.len())
            .map_err(|_| resource())?;
        requirements.extend(self.requirements.iter().cloned());
        let mut selections = Vec::new();
        selections
            .try_reserve_exact(self.selections.len())
            .map_err(|_| resource())?;
        selections.extend(self.selections.iter().cloned());
        Ok(Self {
            identity: self.identity,
            application: self
                .application
                .clone_with_budget(work)
                .map_err(|()| resource())?,
            payload: crate::types::clone_type_with_budget(&self.payload, work)
                .map_err(|()| resource())?,
            native_effect: crate::types::clone_effect_instance_with_budget(
                &self.native_effect,
                work,
            )
            .map_err(|()| resource())?,
            lexical: self.lexical,
            requirements: requirements.into_boxed_slice(),
            selections: selections.into_boxed_slice(),
        })
    }
}
impl Drop for ProviderFamilyAdmission {
    fn drop(&mut self) {
        crate::types::discard_type_iteratively(std::mem::replace(
            &mut self.payload,
            crate::types::Type::Unit,
        ));
    }
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
    pub(crate) capture_globals: &'a [(crate::resolved::BinderId, NodeId)],
    pub(crate) families: &'a [ProviderSpecializationFamilyEntries<'a>],
}

pub(crate) struct ProviderSpecializationFamilyEntries<'a> {
    pub(crate) state: &'a crate::core::TypedBinder,
    pub(crate) handler: crate::core::HandlerId,
    pub(crate) clauses: &'a [crate::core::EffectClause],
    pub(crate) dictionaries: &'a [ProviderSpecializationDictionaryEntry<'a>],
}

pub(crate) struct ProviderSpecializationDictionaryEntry<'a> {
    pub(crate) binder: &'a crate::core::TypedBinder,
    pub(crate) initializer: NodeId,
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
    pub(in crate::core) fn authenticate(
        &self,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
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
            Atom::Packed(value) => Atom::Packed(std::sync::Arc::clone(value)),
            Atom::Intrinsic(value) => Atom::Intrinsic(*value),
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
        metadata: super::projection::MetadataView<'_>,
        renaming: &crate::types::TemplateIdentityRenaming<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<super::projection::Metadata, ValidationError> {
        use super::projection::{Metadata, MetadataView};
        let invalid = || ValidationError::new(crate::core::ValidationReason::EffectRow, None);
        Ok(match metadata {
            MetadataView::Type(ty) => Metadata::Type(crate::types::IterativeTypeOwner::new(
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
            MetadataView::Row(row) => Metadata::Row(
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
            MetadataView::Argument(argument) => {
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
            MetadataView::Kind(kind) => Metadata::Kind(
                crate::types::clone_kind_with_budget(kind, work).map_err(|()| super::resource())?,
            ),
        })
    }
}

/// Paid lookup representation of one source-scope copy phase. It is not a
/// freshening certificate: callers still authenticate every exact original,
/// fresh pair, cross-phase space and complete substitution before using it.
pub(in crate::core) struct SourceScopeFreshening<'a, 'pairs> {
    fresh: &'a ProviderFreshening<'pairs>,
    variables:
        &'a std::collections::HashMap<crate::types::TypeVariableId, crate::types::TypeVariableId>,
    binders: std::collections::HashMap<crate::resolved::BinderId, crate::resolved::BinderId>,
    handlers: std::collections::HashMap<crate::core::HandlerId, crate::core::HandlerId>,
    resumes: std::collections::HashMap<crate::resolved::ResumeId, crate::resolved::ResumeId>,
}
impl<'a, 'pairs> SourceScopeFreshening<'a, 'pairs> {
    pub(in crate::core) fn new(
        fresh: &'a ProviderFreshening<'pairs>,
        variables: &'a std::collections::HashMap<
            crate::types::TypeVariableId,
            crate::types::TypeVariableId,
        >,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        // This source profile has no local nominal/lexical declarations. The
        // optimized path cannot silently admit or erase either identity space.
        super::charge(work, 1)?;
        if !fresh.nominals.is_empty()
            || !fresh.lexicals.is_empty()
            || variables.len() != fresh.types.len()
        {
            return Err(ValidationError::new(
                crate::core::ValidationReason::ResourceEscape,
                None,
            ));
        }
        super::charge(work, fresh.types.len())?;
        for (source, target, _) in fresh.types {
            if variables.get(source) != Some(target) {
                return Err(ValidationError::new(
                    crate::core::ValidationReason::TypeOperation,
                    None,
                ));
            }
        }
        fn index<T: Copy + Eq + std::hash::Hash>(
            pairs: &[(T, T)],
            work: &mut TypeWorkBudget,
        ) -> Result<std::collections::HashMap<T, T>, ValidationError> {
            super::charge(work, pairs.len())?;
            let mut map = std::collections::HashMap::new();
            map.try_reserve(pairs.len())
                .map_err(|_| super::resource())?;
            for (source, target) in pairs {
                if map.insert(*source, *target).is_some() {
                    return Err(ValidationError::new(
                        crate::core::ValidationReason::Scope,
                        None,
                    ));
                }
            }
            Ok(map)
        }
        Ok(Self {
            fresh,
            variables,
            binders: index(fresh.binders, work)?,
            handlers: index(fresh.handlers, work)?,
            resumes: index(fresh.resumes, work)?,
        })
    }
    fn atom(
        &self,
        atom: &super::projection::Atom,
        work: &mut TypeWorkBudget,
    ) -> Result<super::projection::Atom, ValidationError> {
        use super::projection::Atom;
        // Preserve the original atom visit plus one bounded typed lookup. A
        // miss is the same unchanged external identity as the linear path.
        let mapped = match atom {
            Atom::Binder(id) => Atom::Binder(*self.binders.get(id).unwrap_or(id)),
            Atom::Variable(id) => Atom::Variable(*self.variables.get(id).unwrap_or(id)),
            Atom::Handler(id) => Atom::Handler(*self.handlers.get(id).unwrap_or(id)),
            Atom::Resume(id) => Atom::Resume(*self.resumes.get(id).unwrap_or(id)),
            _ => return self.fresh.atom(atom, work),
        };
        super::charge(work, 2)?;
        Ok(mapped)
    }
}

pub(in crate::core) fn specialize_source_projection(
    original: &impl super::projection::ProjectionView,
    copied: &std::collections::HashMap<NodeId, NodeId>,
    fresh: &SourceScopeFreshening<'_, '_>,
    substitution: &ProviderTemplateSubstitution<'_>,
    renaming: &crate::types::TemplateIdentityRenaming<'_>,
    work: &mut TypeWorkBudget,
) -> Result<super::projection::NodeProjection, ValidationError> {
    specialize_projection_with_atom(
        original,
        copied,
        |atom, work| fresh.atom(atom, work),
        substitution,
        renaming,
        work,
    )
}

pub(in crate::core) fn specialize_projection(
    original: &super::projection::NodeProjection,
    copied: &std::collections::HashMap<NodeId, NodeId>,
    fresh: &ProviderFreshening<'_>,
    substitution: &ProviderTemplateSubstitution<'_>,
    renaming: &crate::types::TemplateIdentityRenaming<'_>,
    work: &mut TypeWorkBudget,
) -> Result<super::projection::NodeProjection, ValidationError> {
    specialize_projection_with_atom(
        original,
        copied,
        |atom, work| fresh.atom(atom, work),
        substitution,
        renaming,
        work,
    )
}

fn specialize_projection_with_atom(
    original: &impl super::projection::ProjectionView,
    copied: &std::collections::HashMap<NodeId, NodeId>,
    mut atom: impl FnMut(
        &super::projection::Atom,
        &mut TypeWorkBudget,
    ) -> Result<super::projection::Atom, ValidationError>,
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
            .children()
            .len()
            .checked_add(original.atoms().len())
            .and_then(|n| n.checked_add(original.metadata().len()))
            .and_then(|n| n.checked_add(original.origins().len()))
            .and_then(|n| n.checked_add(1))
            .ok_or_else(super::resource)?,
    )?;
    let mut result = super::projection::NodeProjection {
        node: mapped(original.node())?,
        children: Vec::new(),
        atoms: Vec::new(),
        metadata: Vec::new(),
        origins: Vec::new(),
    };
    result
        .children
        .try_reserve_exact(original.children().len())
        .map_err(|_| super::resource())?;
    result
        .atoms
        .try_reserve_exact(original.atoms().len())
        .map_err(|_| super::resource())?;
    result
        .metadata
        .try_reserve_exact(original.metadata().len())
        .map_err(|_| super::resource())?;
    result
        .origins
        .try_reserve_exact(original.origins().len())
        .map_err(|_| super::resource())?;
    for child in original.children() {
        result.children.push(mapped(*child)?);
    }
    for original_atom in original.atoms() {
        result.atoms.push(atom(original_atom, work)?);
    }
    for metadata in original.metadata() {
        result
            .metadata
            .push(substitution.metadata(metadata, renaming, work)?);
    }
    for origin in original.origins() {
        result
            .origins
            .push(super::RetainedHandlerOrigin::copy(origin, work)?);
    }
    Ok(result)
}

/// Solved rows for compiler preparation. Construction reconstructs D, epsilon,
/// Omega and the normalized residual; a caller cannot supply a row solution.
#[derive(Debug)]
pub(crate) struct ResolvedProviderHandlerRows {
    original_arena: crate::core::dialect::ArenaId,
    direct: crate::types::EffectRow,
    epsilon: crate::types::EffectRow,
    output: crate::types::EffectRow,
    residual: crate::types::EffectRow,
    pending: std::collections::HashMap<crate::types::InferenceVariableId, crate::types::EffectRow>,
    node_rows: std::collections::HashMap<NodeId, crate::types::EffectRow>,
    handler_outputs: std::collections::HashMap<crate::core::HandlerId, crate::types::EffectRow>,
    captures: crate::core::capture::ActualCaptureInputs,
}
impl ResolvedProviderHandlerRows {
    pub(in crate::core) fn visit_semantic_type_variables(
        &self,
        uses: &mut crate::core::validate::semantic_type_variables::UnusedVariables<'_>,
    ) -> Result<(), ()> {
        for row in self.source_rows() {
            uses.row(row)?;
        }
        uses.charge(self.pending.len() + self.node_rows.len() + self.handler_outputs.len())?;
        for row in self
            .pending
            .values()
            .chain(self.node_rows.values())
            .chain(self.handler_outputs.values())
        {
            uses.row(row)?;
        }
        uses.capture_inputs(&self.captures)
    }
    pub(crate) fn source_rows(&self) -> [&crate::types::EffectRow; 4] {
        [&self.direct, &self.epsilon, &self.output, &self.residual]
    }
    pub(crate) fn capture_inputs(&self) -> &crate::core::capture::ActualCaptureInputs {
        &self.captures
    }
    pub(crate) fn handler_outputs(
        &self,
    ) -> &std::collections::HashMap<crate::core::HandlerId, crate::types::EffectRow> {
        &self.handler_outputs
    }

    pub(in crate::core) fn rewrite_source_claim(
        &self,
        rewrite: &mut dyn FnMut(
            &crate::types::EffectRow,
        )
            -> Result<crate::types::EffectRow, crate::core::BuildError>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, crate::core::BuildError> {
        fn rows<K: Copy + Eq + std::hash::Hash>(
            source: &std::collections::HashMap<K, crate::types::EffectRow>,
            rewrite: &mut dyn FnMut(
                &crate::types::EffectRow,
            )
                -> Result<crate::types::EffectRow, crate::core::BuildError>,
            work: &mut TypeWorkBudget,
        ) -> Result<std::collections::HashMap<K, crate::types::EffectRow>, crate::core::BuildError>
        {
            work.charge(source.len())
                .map_err(|_| crate::core::BuildError::TypeWorkExceeded)?;
            let mut result = std::collections::HashMap::new();
            result
                .try_reserve(source.len())
                .map_err(|_| crate::core::BuildError::TypeWorkExceeded)?;
            for (id, row) in source {
                result.insert(*id, rewrite(row)?);
            }
            Ok(result)
        }
        Ok(Self {
            original_arena: self.original_arena,
            direct: rewrite(&self.direct)?,
            epsilon: rewrite(&self.epsilon)?,
            output: rewrite(&self.output)?,
            residual: rewrite(&self.residual)?,
            pending: rows(&self.pending, rewrite, work)?,
            node_rows: rows(&self.node_rows, rewrite, work)?,
            handler_outputs: rows(&self.handler_outputs, rewrite, work)?,
            captures: self.captures.rewrite_rows(rewrite, work)?,
        })
    }

    /// Plain source specialization data. Final source-scope admission derives
    /// every row and actual request witness again; this is no execution proof.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::core) fn from_source_solution(
        original_arena: crate::core::dialect::ArenaId,
        rows: [crate::types::EffectRow; 3],
        pending: std::collections::HashMap<
            crate::types::InferenceVariableId,
            crate::types::EffectRow,
        >,
        node_rows: std::collections::HashMap<NodeId, crate::types::EffectRow>,
        handler_outputs: std::collections::HashMap<crate::core::HandlerId, crate::types::EffectRow>,
        captures: crate::core::capture::ActualCaptureInputs,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        let [direct, epsilon, output] = rows;
        // The private continuation retains the complete client residual,
        // including effects that also occur in the independent direct demand.
        let residual = crate::types::clone_effect_row_with_budget(&epsilon, work)
            .map_err(|_| super::resource())?;
        Ok(Self {
            original_arena,
            direct,
            epsilon,
            output,
            residual,
            pending,
            node_rows,
            handler_outputs,
            captures,
        })
    }

    #[cfg(test)]
    pub(crate) fn assert_distinct_actual_captures_for_test(&self, effect: crate::types::EffectId) {
        assert!(
            self.epsilon.is_empty(),
            "both requests have the same empty scalar body remainder"
        );
        crate::core::capture::assert_distinct_actual_captures_for_test(&self.captures, effect);
    }
    /// Both solutions name equations in the same authenticated ORIGINAL
    /// template arena. Target copied node coordinates are checked separately
    /// by final scope admission and never enter this comparison.
    pub(crate) fn same_actual_captures(
        &self,
        other: &Self,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        super::charge(work, 1)?;
        if self.original_arena != other.original_arena
            || !self
                .captures
                .same(&other.captures, work)
                .map_err(|failure| match failure {
                    crate::core::capture::Failure::Resource => super::resource(),
                    _ => ValidationError::new(crate::core::ValidationReason::ResourceEscape, None),
                })?
        {
            return Ok(false);
        }
        for (left, right) in [
            (&self.direct, &other.direct),
            (&self.epsilon, &other.epsilon),
            (&self.output, &other.output),
            (&self.residual, &other.residual),
        ] {
            if !crate::types::same_effect_rows_with_budget(left, right, work)
                .map_err(|_| super::resource())?
            {
                return Ok(false);
            }
        }
        Ok(
            same_original_row_domain(&self.pending, &other.pending, work)?
                && same_original_row_domain(&self.node_rows, &other.node_rows, work)?
                && same_original_row_domain(&self.handler_outputs, &other.handler_outputs, work)?,
        )
    }
    pub(crate) fn node_rows(&self) -> &std::collections::HashMap<NodeId, crate::types::EffectRow> {
        &self.node_rows
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

/// One source obligation position in the immutable original row domain.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum DeferredProviderRowPosition {
    Output,
    Residual,
    Pending(crate::types::InferenceVariableId),
    Node(NodeId),
    Handler(crate::core::HandlerId),
}

pub(crate) type DeferredProviderRowCompletion<'a> = Vec<(
    DeferredProviderRowPosition,
    crate::types::InferenceVariableId,
    &'a crate::types::EffectRow,
)>;

/// Ordinary source variables, never a solved row or capture certificate. The
/// caller registers every variable with its source row owner and builder guard.
#[derive(Debug)]
pub(crate) struct DeferredProviderHandlerRows {
    original_arena: crate::core::dialect::ArenaId,
    output: crate::types::EffectRow,
    residual: crate::types::EffectRow,
    pending: std::collections::HashMap<crate::types::InferenceVariableId, crate::types::EffectRow>,
    node_rows: std::collections::HashMap<NodeId, crate::types::EffectRow>,
    handler_outputs: std::collections::HashMap<crate::core::HandlerId, crate::types::EffectRow>,
    bindings: Vec<(
        DeferredProviderRowPosition,
        crate::types::InferenceVariableId,
    )>,
}

fn invalid_deferred_rows() -> ValidationError {
    ValidationError::new(crate::core::ValidationReason::NodeType, None)
}

impl DeferredProviderHandlerRows {
    pub(crate) fn row_count(
        checked: &crate::core::validate::CheckedHandlerTemplate,
        work: &mut TypeWorkBudget,
    ) -> Result<usize, ValidationError> {
        super::charge(work, 1)?;
        let (nodes, handlers) = checked.original_recipe().deferred_copy_counts();
        checked
            .original_pending_rows()
            .len()
            .checked_add(nodes)
            .and_then(|n| n.checked_add(handlers))
            .and_then(|n| n.checked_add(2))
            .ok_or_else(super::resource)
    }

    pub(crate) fn prepare(
        checked: &crate::core::validate::CheckedHandlerTemplate,
        allocate: impl FnMut() -> Option<crate::types::EffectRow>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        let (nodes, handlers) = checked.original_recipe().deferred_copy_domain(work)?;
        let records = checked.original_pending_rows();
        super::charge(work, records.len())?;
        let mut pending = Vec::new();
        pending
            .try_reserve_exact(records.len())
            .map_err(|_| super::resource())?;
        pending.extend(records.iter().map(|record| record.identity));
        Self::from_domain(
            checked.original_program().arena,
            &pending,
            &nodes,
            &handlers,
            allocate,
            work,
        )
    }

    pub(in crate::core) fn from_domain(
        original_arena: crate::core::dialect::ArenaId,
        original_pending: &[crate::types::InferenceVariableId],
        original_nodes: &[NodeId],
        original_handlers: &[crate::core::HandlerId],
        mut allocate: impl FnMut() -> Option<crate::types::EffectRow>,
        work: &mut TypeWorkBudget,
    ) -> Result<Self, ValidationError> {
        use std::collections::{HashMap, HashSet};
        let count = original_pending
            .len()
            .checked_add(original_nodes.len())
            .and_then(|n| n.checked_add(original_handlers.len()))
            .and_then(|n| n.checked_add(2))
            .ok_or_else(super::resource)?;
        // Price row storage, scalar receipt and temporary uniqueness index.
        super::charge(work, count.checked_mul(3).ok_or_else(super::resource)?)?;
        let mut seen = HashSet::new();
        seen.try_reserve(count).map_err(|_| super::resource())?;
        let mut bindings = Vec::new();
        bindings
            .try_reserve_exact(count)
            .map_err(|_| super::resource())?;
        let mut pending = HashMap::new();
        pending
            .try_reserve(original_pending.len())
            .map_err(|_| super::resource())?;
        let mut node_rows = HashMap::new();
        node_rows
            .try_reserve(original_nodes.len())
            .map_err(|_| super::resource())?;
        let mut handler_outputs = HashMap::new();
        handler_outputs
            .try_reserve(original_handlers.len())
            .map_err(|_| super::resource())?;
        let mut fresh = |position| {
            let row = allocate().ok_or_else(invalid_deferred_rows)?;
            let Some(tail) = row.tail() else {
                return Err(invalid_deferred_rows());
            };
            let crate::types::EffectRowVariable::Inference(identity) = tail.variable() else {
                return Err(invalid_deferred_rows());
            };
            if !row.known().is_empty() || !tail.lacks().is_empty() || !seen.insert(identity) {
                return Err(invalid_deferred_rows());
            }
            bindings.push((position, identity));
            Ok(row)
        };
        let output = fresh(DeferredProviderRowPosition::Output)?;
        let residual = fresh(DeferredProviderRowPosition::Residual)?;
        for original in original_pending {
            let row = fresh(DeferredProviderRowPosition::Pending(*original))?;
            if pending.insert(*original, row).is_some() {
                return Err(invalid_deferred_rows());
            }
        }
        for original in original_nodes {
            if original.arena() != original_arena {
                return Err(super::invalid(*original));
            }
            let row = fresh(DeferredProviderRowPosition::Node(*original))?;
            if node_rows.insert(*original, row).is_some() {
                return Err(super::invalid(*original));
            }
        }
        for original in original_handlers {
            let row = fresh(DeferredProviderRowPosition::Handler(*original))?;
            if handler_outputs.insert(*original, row).is_some() {
                return Err(invalid_deferred_rows());
            }
        }
        Ok(Self {
            original_arena,
            output,
            residual,
            pending,
            node_rows,
            handler_outputs,
            bindings,
        })
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
    pub(crate) fn node_rows(&self) -> &std::collections::HashMap<NodeId, crate::types::EffectRow> {
        &self.node_rows
    }

    /// Check the complete original domain before exposing any equations to the
    /// source unifier. Actual rows still require the retained alpha relocation.
    pub(crate) fn completion<'a>(
        &self,
        actual: &'a ResolvedProviderHandlerRows,
        work: &mut TypeWorkBudget,
    ) -> Result<DeferredProviderRowCompletion<'a>, ValidationError> {
        // Price the original-position visit and each retained completion entry.
        super::charge(
            work,
            self.bindings
                .len()
                .checked_mul(2)
                .ok_or_else(super::resource)?,
        )?;
        if self.original_arena != actual.original_arena
            || self.pending.len() != actual.pending.len()
            || self.node_rows.len() != actual.node_rows.len()
            || self.handler_outputs.len() != actual.handler_outputs.len()
        {
            return Err(invalid_deferred_rows());
        }
        let mut result = Vec::new();
        result
            .try_reserve_exact(self.bindings.len())
            .map_err(|_| super::resource())?;
        for &(position, source) in &self.bindings {
            let row = match position {
                DeferredProviderRowPosition::Output => Some(&actual.output),
                DeferredProviderRowPosition::Residual => Some(&actual.residual),
                DeferredProviderRowPosition::Pending(original) => actual.pending.get(&original),
                DeferredProviderRowPosition::Node(original) => actual.node_rows.get(&original),
                DeferredProviderRowPosition::Handler(original) => {
                    actual.handler_outputs.get(&original)
                }
            };
            result.push((position, source, row.ok_or_else(invalid_deferred_rows)?));
        }
        Ok(result)
    }
}

fn same_original_row_domain<K: Eq + std::hash::Hash>(
    left: &std::collections::HashMap<K, crate::types::EffectRow>,
    right: &std::collections::HashMap<K, crate::types::EffectRow>,
    work: &mut TypeWorkBudget,
) -> Result<bool, ValidationError> {
    super::charge(
        work,
        left.len()
            .checked_add(right.len())
            .ok_or_else(super::resource)?,
    )?;
    if left.len() != right.len() {
        return Ok(false);
    }
    for (key, row) in left {
        super::charge(work, 1)?;
        let Some(other) = right.get(key) else {
            return Ok(false);
        };
        if !crate::types::same_effect_rows_with_budget(row, other, work)
            .map_err(|_| super::resource())?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

#[allow(clippy::too_many_arguments)] // Independent source, actual and work authorities stay explicit.
pub(in crate::core) fn prepare_handler_rows(
    checked: &crate::core::validate::CheckedHandlerTemplate,
    types: &std::collections::HashMap<crate::types::TypeVariableId, crate::types::Type>,
    rows: &std::collections::HashMap<crate::types::TypeVariableId, crate::types::EffectRow>,
    body_answer: &crate::types::Type,
    body_effects: &crate::types::EffectRow,
    provided: &crate::types::EffectInstance,
    actual: Option<crate::core::capture::ActualProviderCapture>,
    work: &mut TypeWorkBudget,
) -> Result<ResolvedProviderHandlerRows, ValidationError> {
    use crate::types::{
        EffectRowError, clone_effect_row_with_budget, same_effect_rows_with_budget,
    };
    let hidden = checked.original_hidden();
    if types.contains_key(&hidden[0].0) || rows.contains_key(&hidden[1].0) {
        return Err(super::invalid(checked.original_program().root));
    }
    let captures = if checked.original_recipe().discards().is_empty() {
        if actual.is_some() {
            return Err(super::invalid(checked.original_program().root));
        }
        crate::core::capture::ActualCaptureInputs::empty(checked.original_template())
    } else {
        crate::core::capture::reconstruct_actual_provider_captures(
            checked.original_capture(),
            checked.original_program(),
            actual.ok_or_else(|| {
                ValidationError::new(crate::core::ValidationReason::ResourceEscape, None)
            })?,
            types,
            rows,
            body_answer,
            provided,
            work,
        )
        .map_err(|failure| match failure {
            crate::core::capture::Failure::Resource => super::resource(),
            _ => ValidationError::new(crate::core::ValidationReason::ResourceEscape, None),
        })?
    };
    let (direct, pending_rows) =
        checked
            .original_recipe()
            .realize_direct(types, rows, captures.rows(), work)?;
    let contract_direct =
        checked
            .original_row_contract()
            .realize_direct(types, rows, captures.rows(), work)?;
    if !same_effect_rows_with_budget(&direct, &contract_direct, work)
        .map_err(|_| super::resource())?
    {
        return Err(super::invalid(checked.original_program().root));
    }
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
        .map_err(|error| ValidationError::row_union_failure(error, None))?;
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
        captures.rows(),
        &output,
        work,
    )?;
    Ok(ResolvedProviderHandlerRows {
        original_arena: checked.original_program().arena,
        direct,
        epsilon,
        output,
        residual,
        pending,
        node_rows: realized.nodes,
        handler_outputs: realized.handlers,
        captures,
    })
}

/// Exact inputs for one member of a single-owner source dispatch group.
pub(crate) struct ProviderGroupRowsInput<'a> {
    pub(crate) original: &'a crate::core::validate::CheckedHandlerTemplate,
    pub(crate) types:
        &'a std::collections::HashMap<crate::types::TypeVariableId, crate::types::Type>,
    pub(crate) rows:
        &'a std::collections::HashMap<crate::types::TypeVariableId, crate::types::EffectRow>,
    pub(crate) provided: &'a crate::types::EffectInstance,
    pub(crate) native: &'a crate::types::EffectInstance,
}

/// Solves the body-only removal and each clause's own native interpretation.
/// The common continuation row is reconstructed from direct demand, never
/// from a feedback-containing final clause row.
pub(crate) fn prepare_group_handler_rows(
    inputs: &[ProviderGroupRowsInput<'_>],
    answer: &crate::types::Type,
    body: &crate::types::EffectRow,
    work: &mut TypeWorkBudget,
) -> Result<Box<[ResolvedProviderHandlerRows]>, ValidationError> {
    use crate::types::{
        EffectRow, EffectRowError, clone_effect_row_with_budget, same_effect_rows_with_budget,
    };
    if inputs.is_empty() {
        return Err(ValidationError::new(
            crate::core::ValidationReason::Registry,
            None,
        ));
    }
    super::charge(work, inputs.len())?;
    let mut remainder = clone_effect_row_with_budget(body, work).map_err(|()| super::resource())?;
    let remove =
        |row: &EffectRow, effect: &crate::types::EffectInstance, work: &mut TypeWorkBudget| {
            match row
                .remove_exact_with_budget(effect, work)
                .map_err(|()| super::resource())?
            {
                Ok(row) => Ok(row),
                Err(EffectRowError::Missing) => {
                    clone_effect_row_with_budget(row, work).map_err(|()| super::resource())
                }
                Err(_) => Err(ValidationError::new(
                    crate::core::ValidationReason::EffectRow,
                    None,
                )),
            }
        };
    for input in inputs {
        remainder = remove(&remainder, input.provided, work)?;
    }
    let mut output =
        clone_effect_row_with_budget(&remainder, work).map_err(|()| super::resource())?;
    let mut records = Vec::new();
    records
        .try_reserve_exact(inputs.len())
        .map_err(|_| super::resource())?;
    for input in inputs {
        let checked = input.original;
        // Capture-sensitive templates remain an explicit unsupported fragment;
        // this path does not fabricate a capture result for a family member.
        if checked.needs_actual_captures() {
            return Err(ValidationError::new(
                crate::core::ValidationReason::ResourceEscape,
                None,
            ));
        }
        let captures =
            crate::core::capture::ActualCaptureInputs::empty(checked.original_template());
        let (direct, pending) = checked.original_recipe().realize_direct(
            input.types,
            input.rows,
            captures.rows(),
            work,
        )?;
        let canonical = checked.original_row_contract().realize_direct(
            input.types,
            input.rows,
            captures.rows(),
            work,
        )?;
        if !same_effect_rows_with_budget(&direct, &canonical, work)
            .map_err(|()| super::resource())?
        {
            return Err(super::invalid(checked.original_program().root));
        }
        let outward = remove(&direct, input.native, work)?;
        output = output
            .union_with_budget(&outward, work)
            .map_err(|()| super::resource())?
            .map_err(|error| ValidationError::row_union_failure(error, None))?;
        records.push((direct, pending, captures));
    }
    let mut solutions = Vec::new();
    solutions
        .try_reserve_exact(inputs.len())
        .map_err(|_| super::resource())?;
    for (input, (direct, pending_rows, captures)) in inputs.iter().zip(records) {
        let checked = input.original;
        let hidden = checked.original_hidden();
        if input.types.contains_key(&hidden[0].0)
            || input.rows.contains_key(&hidden[1].0)
            || pending_rows.len() != checked.original_pending_rows().len()
        {
            return Err(super::invalid(checked.original_program().root));
        }
        super::charge(work, pending_rows.len())?;
        let mut pending = std::collections::HashMap::new();
        pending
            .try_reserve(pending_rows.len())
            .map_err(|_| super::resource())?;
        for (record, row) in checked.original_pending_rows().iter().zip(pending_rows) {
            if pending.insert(record.identity, row).is_some() {
                return Err(super::invalid(checked.original_program().root));
            }
        }
        let mut complete = OriginalSubstitutions {
            types: std::collections::HashMap::new(),
            rows: std::collections::HashMap::new(),
        };
        super::charge(
            work,
            input
                .types
                .len()
                .checked_add(input.rows.len())
                .and_then(|n| n.checked_add(2))
                .ok_or_else(super::resource)?,
        )?;
        complete
            .types
            .try_reserve(input.types.len() + 1)
            .map_err(|_| super::resource())?;
        complete
            .rows
            .try_reserve(input.rows.len() + 1)
            .map_err(|_| super::resource())?;
        for (id, ty) in input.types {
            complete.insert_type(
                *id,
                crate::types::clone_type_with_budget(ty, work).map_err(|()| super::resource())?,
            );
        }
        for (id, row) in input.rows {
            complete.insert_row(
                *id,
                clone_effect_row_with_budget(row, work).map_err(|()| super::resource())?,
            );
        }
        complete.insert_type(
            hidden[0].0,
            crate::types::clone_type_with_budget(answer, work).map_err(|()| super::resource())?,
        );
        complete.insert_row(
            hidden[1].0,
            clone_effect_row_with_budget(&output, work).map_err(|()| super::resource())?,
        );
        let realized = checked.original_recipe().realize_nodes(
            checked.original_program(),
            &complete.types,
            &complete.rows,
            &pending,
            captures.rows(),
            &output,
            work,
        )?;
        solutions.push(ResolvedProviderHandlerRows {
            original_arena: checked.original_program().arena,
            direct,
            epsilon: clone_effect_row_with_budget(&remainder, work)
                .map_err(|()| super::resource())?,
            output: clone_effect_row_with_budget(&output, work).map_err(|()| super::resource())?,
            residual: clone_effect_row_with_budget(&output, work)
                .map_err(|()| super::resource())?,
            pending,
            node_rows: realized.nodes,
            handler_outputs: realized.handlers,
            captures,
        });
    }
    Ok(solutions.into_boxed_slice())
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
/// Source-only frozen copied-flow facts. There is no conversion to the final
/// original-specialization token; final catalog admission remains independent.
#[derive(Debug)]
pub(super) struct PreparedProviderCaptureReceipt(std::sync::Arc<SpecializationProof>);

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
    families: Vec<SpecializedFamily>,
    native_storage: Vec<AdmittedNativeStorageRelation>,
    native: Option<std::sync::Arc<crate::foreign::ForeignModuleFact>>,
}

impl SpecializationProof {
    fn visit_semantic_type_variables(
        &self,
        uses: &mut crate::core::validate::semantic_type_variables::UnusedVariables<'_>,
    ) -> Result<(), ()> {
        uses.catalog(&self.catalog)?;
        uses.charge(
            self.nodes.len()
                + self.parameters.len()
                + self.clauses.len()
                + self.occurrences.len()
                + self.anchors.len()
                + self.families.len()
                + self.native_storage.len(),
        )?;
        for projection in self
            .nodes
            .iter()
            .chain(&self.parameters)
            .chain(&self.clauses)
        {
            projection.visit_semantic_type_variables(uses)?;
        }
        for occurrence in &self.occurrences {
            uses.selection(&occurrence.selection)?;
            uses.application(&occurrence.application)?;
            uses.charge(occurrence.arguments.len() + occurrence.original.arguments.len())?;
            for argument in occurrence
                .arguments
                .iter()
                .chain(&occurrence.original.arguments)
            {
                uses.ty(argument)?;
            }
            if let Some(ty) = &occurrence.value_type {
                uses.ty(ty)?;
            }
            if let Some(ty) = &occurrence.original.value {
                uses.ty(ty)?;
            }
            occurrence
                .original
                .allocation
                .visit_semantic_type_variables(uses)?;
            uses.application(&occurrence.original.application)?;
            uses.selection(&occurrence.original.selection)?;
        }
        for anchor in &self.anchors {
            uses.application(&anchor.application)?;
        }
        for family in &self.families {
            family.header.visit_semantic_type_variables(uses)?;
            family.certificate.visit_semantic_type_variables(uses)?;
            uses.instance(&family.provided)?;
            family.state.visit_semantic_type_variables(uses)?;
            uses.charge(family.clauses.len() + family.dictionaries.len())?;
            for clause in &family.clauses {
                clause.visit_semantic_type_variables(uses)?;
            }
            for dictionary in &family.dictionaries {
                dictionary.projection.visit_semantic_type_variables(uses)?;
                dictionary.initializer.visit_semantic_type_variables(uses)?;
            }
        }
        for relation in &self.native_storage {
            uses.id(relation.owner)?;
            uses.id(relation.family.parameter)?;
            uses.instance(&relation.effect)?;
            relation
                .request_projection
                .visit_semantic_type_variables(uses)?;
            relation
                .operand_projection
                .visit_semantic_type_variables(uses)?;
        }
        Ok(())
    }
}

impl OriginalProviderSpecialization {
    pub(super) fn visit_semantic_type_variables(
        &self,
        uses: &mut crate::core::validate::semantic_type_variables::UnusedVariables<'_>,
    ) -> Result<(), ()> {
        self.0.visit_semantic_type_variables(uses)
    }
}
impl PreparedProviderCaptureReceipt {
    pub(super) fn visit_semantic_type_variables(
        &self,
        uses: &mut crate::core::validate::semantic_type_variables::UnusedVariables<'_>,
    ) -> Result<(), ()> {
        self.0.visit_semantic_type_variables(uses)
    }
}
impl ProviderFamilyAdmission {
    pub(super) fn visit_semantic_type_variables(
        &self,
        uses: &mut crate::core::validate::semantic_type_variables::UnusedVariables<'_>,
    ) -> Result<(), ()> {
        uses.id(self.identity.parameter)?;
        uses.ty(&self.payload)?;
        uses.application(&self.application)?;
        uses.instance(&self.native_effect)?;
        uses.charge(self.requirements.len() + self.selections.len())?;
        for (selection, _) in self.requirements.iter().chain(&self.selections) {
            uses.selection(selection)?;
        }
        Ok(())
    }
}

struct SpecializedFamily {
    certificate: std::sync::Arc<crate::core::validate::CheckedHandlerContractCertificate>,
    header: ProviderFamilyAdmission,
    provided: crate::types::EffectInstance,
    state: super::projection::NodeProjection,
    handler: crate::core::HandlerId,
    clauses: Vec<super::projection::NodeProjection>,
    nodes: Vec<NodeId>,
    dictionaries: Vec<SpecializedDictionary>,
}

impl std::fmt::Debug for SpecializedFamily {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SpecializedFamily")
            .field("header", &self.header)
            .field("handler", &self.handler)
            .field("dictionaries", &self.dictionaries)
            .finish_non_exhaustive()
    }
}

#[derive(Debug)]
struct SpecializedDictionary {
    requirement: crate::interface::RequirementId,
    method: crate::interface::MethodId,
    binder: crate::resolved::BinderId,
    projection: super::projection::NodeProjection,
    initializer: super::projection::NodeProjection,
    producer: crate::foreign::ForeignLayoutProducer,
}

/// Minted only by original-template projection and exact native-flow transfer.
#[derive(Debug)]
pub(crate) struct AdmittedNativeStorageRelation {
    request: NodeId,
    operand: NodeId,
    request_projection: super::projection::NodeProjection,
    operand_projection: super::projection::NodeProjection,
    operation: crate::types::OperationId,
    effect: crate::types::EffectInstance,
    owner: crate::types::TypeVariableId,
    family: super::ProviderFamilyIdentity,
    member: usize,
    result: super::HandlerNativeStorageResult,
}

impl AdmittedNativeStorageRelation {
    pub(crate) fn request(&self) -> NodeId {
        self.request
    }
    pub(crate) fn operation(&self) -> crate::types::OperationId {
        self.operation
    }
    pub(crate) fn effect(&self) -> &crate::types::EffectInstance {
        &self.effect
    }
    pub(crate) fn owner(&self) -> crate::types::TypeVariableId {
        self.owner
    }
    pub(crate) fn family(&self) -> super::ProviderFamilyIdentity {
        self.family
    }
    pub(crate) fn member(&self) -> usize {
        self.member
    }
    pub(in crate::core) fn result(&self) -> super::HandlerNativeStorageResult {
        self.result
    }
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
fn target_node(
    arena: crate::core::dialect::ArenaId,
    nodes: &[crate::core::dialect::StoredNode<crate::core::EffectOperationFamily>],
    node: NodeId,
) -> Result<&crate::core::dialect::StoredNode<crate::core::EffectOperationFamily>, ValidationError>
{
    if node.arena() != arena {
        return Err(super::invalid(node));
    }
    nodes
        .get(node.index().map_err(|_| super::invalid(node))?)
        .ok_or_else(|| super::invalid(node))
}

fn reconstruct_group_rows(
    admission: &ProviderScopeAdmission,
    copies: &[ProviderCopiedTemplate<'_>],
    body: &crate::core::dialect::StoredNode<crate::core::EffectOperationFamily>,
    work: &mut TypeWorkBudget,
) -> Result<Box<[ResolvedProviderHandlerRows]>, ValidationError> {
    use crate::types::{KindedArgument, TemplateIdentityRenaming};
    let count = admission
        .families
        .len()
        .checked_add(1)
        .ok_or_else(super::resource)?;
    super::charge(work, count.checked_mul(4).ok_or_else(super::resource)?)?;
    let mut formals = Vec::new();
    let mut provided = Vec::new();
    let mut natives = Vec::new();
    let mut originals = Vec::new();
    formals
        .try_reserve_exact(count)
        .map_err(|_| super::resource())?;
    provided
        .try_reserve_exact(count)
        .map_err(|_| super::resource())?;
    natives
        .try_reserve_exact(count)
        .map_err(|_| super::resource())?;
    originals
        .try_reserve_exact(count)
        .map_err(|_| super::resource())?;
    let variables = std::collections::HashMap::new();
    let nominals = std::collections::HashMap::new();
    let renaming = TemplateIdentityRenaming {
        variables: &variables,
        nominals: &nominals,
    };
    for member in 0..count {
        let copy = copies.get(member + 2).ok_or_else(super::resource)?;
        let ProviderOriginalTemplate::Handler(original) = copy.original else {
            return Err(super::invalid(original_root(copy)));
        };
        let mut sigma = OriginalSubstitutions {
            types: std::collections::HashMap::new(),
            rows: std::collections::HashMap::new(),
        };
        super::charge(
            work,
            admission
                .arguments
                .len()
                .checked_add(usize::from(member != 0))
                .ok_or_else(super::resource)?,
        )?;
        sigma
            .types
            .try_reserve(admission.arguments.len() + usize::from(member != 0))
            .map_err(|_| super::resource())?;
        sigma
            .rows
            .try_reserve(admission.arguments.len())
            .map_err(|_| super::resource())?;
        for (formal, actual) in admission
            .definition
            .parameters
            .iter()
            .zip(&admission.arguments)
        {
            authenticate_actual(formal.id, actual, &copy.substitution, work)?;
            match actual {
                KindedArgument::TypeArg(ty) => {
                    sigma.insert_type(
                        formal.id,
                        crate::types::clone_type_with_budget(ty, work)
                            .map_err(|()| super::resource())?,
                    );
                }
                KindedArgument::RowArg(row) => {
                    sigma.insert_row(
                        formal.id,
                        crate::types::clone_effect_row_with_budget(row, work)
                            .map_err(|()| super::resource())?,
                    );
                }
            }
        }
        let (provided_template, native_template) = if member == 0 {
            (
                &admission.definition.provided.instance,
                &admission.definition.interpreted.instance,
            )
        } else {
            let family = admission
                .definition
                .family_template
                .as_ref()
                .ok_or_else(|| super::invalid(original.original_program().root))?;
            let claim = &admission.families[member - 1];
            if claim.identity.definition != admission.definition.id
                || claim.identity.parameter != family.parameter.id
            {
                return Err(super::invalid(original.original_program().root));
            }
            let actual = crate::types::KindedArgument::TypeArg(
                crate::types::clone_type_with_budget(&claim.payload, work)
                    .map_err(|()| super::resource())?,
            );
            let actual = crate::types::IterativeArgumentOwner::new(actual);
            authenticate_actual(family.parameter.id, &actual, &copy.substitution, work)?;
            sigma.insert_type(
                family.parameter.id,
                crate::types::clone_type_with_budget(&claim.payload, work)
                    .map_err(|()| super::resource())?,
            );
            (&family.provided.instance, &family.interpreted.instance)
        };
        provided.push(substitute_instance(
            provided_template,
            &copy.substitution,
            &renaming,
            work,
        )?);
        natives.push(substitute_instance(
            native_template,
            &copy.substitution,
            &renaming,
            work,
        )?);
        originals.push(original);
        formals.push(sigma);
    }
    let mut inputs = Vec::new();
    super::charge(work, count)?;
    inputs
        .try_reserve_exact(count)
        .map_err(|_| super::resource())?;
    for member in 0..count {
        inputs.push(ProviderGroupRowsInput {
            original: originals[member],
            types: &formals[member].types,
            rows: &formals[member].rows,
            provided: &provided[member],
            native: &natives[member],
        });
    }
    prepare_group_handler_rows(&inputs, &body.ty, &body.effects, work)
}

fn family_certificate<'a>(
    admission: &ProviderScopeAdmission,
    registry: &'a crate::resolved::ResolvedRegistry,
    at: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<&'a crate::elaborate::provider::CheckedProviderContracts, ValidationError> {
    super::charge(work, registry.provider_contract_count())?;
    let certificate = registry
        .provider_contracts()
        .find(|(module, _)| **module == admission.definition.id.module())
        .map(|(_, certificate)| certificate.as_ref())
        .ok_or_else(|| super::invalid(at))?;
    super::charge(work, certificate.resource_count())?;
    if !certificate
        .resource_contracts()
        .any(|(_, _, fact)| std::sync::Arc::ptr_eq(fact, &admission.definition))
    {
        return Err(super::invalid(at));
    }
    Ok(certificate)
}

/// Reconstructs the member header from the genuine original certificate and
/// the complete outer Type/Row actuals. Hidden answer/row equations, disjoint
/// freshening, and source ownership remain the enclosing admission's checks.
fn authenticate_family_header(
    admission: &ProviderScopeAdmission,
    family: &ProviderFamilyAdmission,
    copy: &ProviderCopiedTemplate<'_>,
    registry: &crate::resolved::ResolvedRegistry,
    renaming: &crate::types::TemplateIdentityRenaming<'_>,
    work: &mut TypeWorkBudget,
) -> Result<crate::types::EffectInstance, ValidationError> {
    let at = original_root(copy);
    let certificate = family_certificate(admission, registry, at, work)?;
    super::charge(
        work,
        certificate
            .resource_count()
            .checked_mul(5)
            .ok_or_else(super::resource)?,
    )?;
    let fact = admission.definition.id;
    let contract = ProviderFamilyContractView {
        identity: certificate
            .family_identity(fact)
            .ok_or_else(|| super::invalid(at))?,
        application: certificate
            .family_provider_application(fact)
            .ok_or_else(|| super::invalid(at))?,
        requirements: certificate
            .family_requirements(fact)
            .ok_or_else(|| super::invalid(at))?,
        methods: certificate
            .family_methods(fact)
            .ok_or_else(|| super::invalid(at))?,
        handler: certificate
            .family_handler_certificate(fact)
            .ok_or_else(|| super::invalid(at))?,
    };
    authenticate_family_header_with_contract(
        admission, family, copy, registry, renaming, &contract, work,
    )
}

fn authenticate_family_header_with_contract(
    admission: &ProviderScopeAdmission,
    family: &ProviderFamilyAdmission,
    copy: &ProviderCopiedTemplate<'_>,
    registry: &crate::resolved::ResolvedRegistry,
    renaming: &crate::types::TemplateIdentityRenaming<'_>,
    contract: &ProviderFamilyContractView<'_>,
    work: &mut TypeWorkBudget,
) -> Result<crate::types::EffectInstance, ValidationError> {
    use crate::types::{Kind, KindedArgument, Type};
    let ProviderOriginalTemplate::Handler(original) = copy.original else {
        return Err(ValidationError::new(
            crate::core::ValidationReason::NodeType,
            None,
        ));
    };
    let at = original.original_program().root;
    let fact = admission.definition.as_ref();
    let written = fact
        .family_template
        .as_ref()
        .ok_or_else(|| super::invalid(at))?;
    let ProviderFamilyContractView {
        identity,
        application,
        requirements,
        methods,
        handler: original_certificate,
    } = *contract;
    if !original.authenticates_certificate(original_certificate) {
        return Err(super::invalid(at));
    }
    if family.identity != identity
        || identity.definition != fact.id
        || identity.parameter != written.parameter.id
        || written.parameter.kind != Kind::Type
        || original.original_template() != crate::resolved::ProviderTemplateId::new(fact.id, 3)
        || admission.arguments.len() != fact.parameters.len()
        || family.requirements.len() != requirements.len()
        || !matches!(&family.payload, Type::Unit | Type::Bool | Type::Int)
    {
        return Err(super::invalid(at));
    }
    original.authenticate_source(work)?;
    original.authenticate_definition(fact, work)?;
    super::charge(work, fact.parameters.len())?;
    for (parameter, actual) in fact.parameters.iter().zip(&admission.arguments) {
        match (&parameter.kind, actual) {
            (Kind::Type, KindedArgument::TypeArg(actual)) => {
                let substituted = copy
                    .substitution
                    .types
                    .get(&parameter.id)
                    .ok_or_else(|| super::invalid(at))?;
                if !crate::types::same_type_with_budget(substituted, actual, work)
                    .map_err(|()| super::resource())?
                {
                    return Err(super::invalid(at));
                }
            }
            (Kind::EffectRow, KindedArgument::RowArg(actual)) => {
                let substituted = copy
                    .substitution
                    .rows
                    .get(&parameter.id)
                    .ok_or_else(|| super::invalid(at))?;
                if !crate::types::same_effect_rows_with_budget(substituted, actual, work)
                    .map_err(|()| super::resource())?
                {
                    return Err(super::invalid(at));
                }
            }
            _ => return Err(super::invalid(at)),
        }
    }
    let payload = copy
        .substitution
        .types
        .get(&identity.parameter)
        .ok_or_else(|| super::invalid(at))?;
    if !crate::types::same_type_with_budget(payload, &family.payload, work)
        .map_err(|()| super::resource())?
        || !same_application(application, &written.provider_application, work)?
        || !same_application(
            &specialized_application(application, copy, renaming, work)?,
            &family.application,
            work,
        )?
    {
        return Err(super::invalid(at));
    }
    let provided = substitute_instance(
        &written.provided.instance,
        &copy.substitution,
        renaming,
        work,
    )?;
    let native = substitute_instance(
        &written.interpreted.instance,
        &copy.substitution,
        renaming,
        work,
    )?;
    if crate::types::compare_effect_instances_with_budget(&native, &family.native_effect, work)
        .map_err(|()| super::resource())?
        != std::cmp::Ordering::Equal
        || registry.foreign_effect(provided.effect())
    {
        return Err(super::invalid(at));
    }
    let mut original_native = false;
    for registered in registry.foreign_modules() {
        super::charge(work, 1)?;
        if std::sync::Arc::ptr_eq(registered, &admission.native) {
            if original_native {
                return Err(super::invalid(at));
            }
            original_native = true;
        }
    }
    let storage = admission
        .native
        .storage
        .as_ref()
        .ok_or_else(|| super::invalid(at))?;
    if !original_native
        || native.effect() != storage.effect()
        || fact.state.ty.outer_nominal() != Some(storage.state())
        || !matches!(native.arguments().get(storage.owner_parameter()),
            Some(KindedArgument::TypeArg(Type::Variable(owner))) if *owner == admission.identity)
        || !matches!(native.arguments().get(storage.payload_parameter()),
            Some(KindedArgument::TypeArg(payload)) if crate::types::same_type_with_budget(
                payload, &family.payload, work).map_err(|()| super::resource())?)
    {
        return Err(super::invalid(at));
    }
    authenticate_family_selections(
        admission,
        family,
        requirements,
        methods,
        copy,
        registry,
        renaming,
        at,
        work,
    )?;
    Ok(provided)
}

/// A locator retains the whole immutable plan. The selected family may occur
/// beneath an implementation root, but must be reachable from that exact root.
fn authenticate_family_selection_reachability(
    selection: &crate::interface::EvidenceSelection,
    selected: crate::interface::EvidenceNodeId,
    at: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    use crate::interface::EvidenceNode;
    let count = selection.node_count();
    if selected.index() >= count || selection.root().index() >= count {
        return Err(super::invalid(at));
    }
    super::charge(work, count.checked_add(1).ok_or_else(super::resource)?)?;
    let mut seen = Vec::new();
    seen.try_reserve_exact(count)
        .map_err(|_| super::resource())?;
    seen.resize(count, false);
    let mut pending = Vec::new();
    pending.try_reserve(1).map_err(|_| super::resource())?;
    pending.push(selection.root());
    let mut found = false;
    while let Some(node) = pending.pop() {
        super::charge(work, 1)?;
        let visited = seen
            .get_mut(node.index())
            .ok_or_else(|| super::invalid(at))?;
        if *visited {
            continue;
        }
        *visited = true;
        found |= node == selected;
        let prerequisites = match selection.node(node).ok_or_else(|| super::invalid(at))? {
            EvidenceNode::ProviderFamily { prerequisites, .. }
            | EvidenceNode::Implementation { prerequisites, .. } => prerequisites,
            EvidenceNode::NativeLayout { .. }
            | EvidenceNode::Lexical { .. }
            | EvidenceNode::Abstract { .. } => &[],
        };
        super::charge(work, prerequisites.len())?;
        pending
            .try_reserve(prerequisites.len())
            .map_err(|_| super::resource())?;
        for prerequisite in prerequisites {
            if prerequisite.index() >= node.index() {
                return Err(super::invalid(at));
            }
            pending.push(*prerequisite);
        }
    }
    if found {
        Ok(())
    } else {
        Err(super::invalid(at))
    }
}

/// Independently authenticates every retained occurrence plan. Equivalent
/// family goals may share one handler, never another occurrence's plan receipt.
#[expect(
    clippy::too_many_arguments,
    reason = "original certificate, full sigma and immutable occurrence plans remain separate"
)]
fn authenticate_family_selections(
    admission: &ProviderScopeAdmission,
    family: &ProviderFamilyAdmission,
    requirements: &[crate::interface::CheckedRequirement],
    methods: &[(crate::interface::MethodId, crate::types::OperationId)],
    copy: &ProviderCopiedTemplate<'_>,
    registry: &crate::resolved::ResolvedRegistry,
    renaming: &crate::types::TemplateIdentityRenaming<'_>,
    at: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    use crate::interface::EvidenceNode;
    use crate::types::{IterativeTypeOwner, Kind, KindedArgument, Type};
    if family.selections.is_empty()
        || requirements.len() != 1
        || requirements.len() != family.requirements.len()
    {
        return Err(super::invalid(at));
    }
    let layout = admission
        .native
        .layout
        .as_ref()
        .ok_or_else(|| super::invalid(at))?;
    let storage = admission
        .native
        .storage
        .as_ref()
        .ok_or_else(|| super::invalid(at))?;
    super::charge(work, admission.native.canonical_interfaces().len())?;
    let canonical = admission
        .native
        .canonical_interfaces()
        .iter()
        .find(|interface| interface.id == layout.interface())
        .ok_or_else(|| super::invalid(at))?;
    let [parameter] = canonical.parameters.as_ref() else {
        return Err(super::invalid(at));
    };
    let [method] = canonical.methods.as_ref() else {
        return Err(super::invalid(at));
    };
    if parameter.kind != Kind::Type
        || parameter.id != layout.payload_parameter()
        || method.id != layout.method()
        || method.id.interface() != canonical.id
        || method.id.declaration() != 0
        || !method.type_parameters.is_empty()
        || layout.witness() != storage.witness()
    {
        return Err(super::invalid(at));
    }
    super::charge(work, family.selections.len())?;
    for (index, (selection, selected)) in family.selections.iter().enumerate() {
        super::charge(work, index)?;
        if family.selections[..index].iter().any(|(other, node)| {
            selected == node
                && selection.shares_plan_with(other)
                && selection.root() == other.root()
        }) {
            return Err(super::invalid(at));
        }
        authenticate_family_selection_reachability(selection, *selected, at, work)?;
        let Some(EvidenceNode::ProviderFamily {
            source,
            definition,
            parameter,
            application,
            prerequisites,
            methods: selected_methods,
        }) = selection.node(*selected)
        else {
            return Err(super::invalid(at));
        };
        if source != family.lexical
            || definition != family.identity.definition
            || parameter != family.identity.parameter
            || prerequisites.len() != requirements.len()
            || selected_methods.len() != methods.len()
            || !same_application(application, &family.application, work)?
        {
            return Err(super::invalid(at));
        }
        super::charge(
            work,
            selected_methods
                .len()
                .checked_add(requirements.len())
                .ok_or_else(super::resource)?,
        )?;
        if !selected_methods
            .iter()
            .copied()
            .eq(methods.iter().map(|(method, _)| *method))
        {
            return Err(super::invalid(at));
        }
        for (ordinal, (required, prerequisite)) in
            requirements.iter().zip(prerequisites).enumerate()
        {
            if required.id.owner()
                != crate::interface::RequirementOwner::ResourceFamily(admission.definition.id)
                || usize::try_from(required.id.declaration()).ok() != Some(ordinal)
                || prerequisite.index() >= selected.index()
            {
                return Err(super::invalid(at));
            }
            let required = specialized_application(required.application(), copy, renaming, work)?;
            let [KindedArgument::TypeArg(payload)] = required.arguments() else {
                return Err(super::invalid(at));
            };
            let (encoding, size, alignment) = match payload {
                Type::Unit => (crate::foreign::ForeignScalarEncoding::Unit, 0, 1),
                Type::Bool => (crate::foreign::ForeignScalarEncoding::Bool, 1, 1),
                Type::Int => (crate::foreign::ForeignScalarEncoding::Signed64, 8, 8),
                _ => return Err(super::invalid(at)),
            };
            let Some(EvidenceNode::NativeLayout { producer }) = selection.node(*prerequisite)
            else {
                return Err(super::invalid(at));
            };
            let dictionary =
                registry
                    .foreign_layout_dictionary(producer, work)
                    .map_err(|failure| {
                        if failure.is_resource_exhaustion() {
                            super::resource()
                        } else {
                            super::invalid(at)
                        }
                    })?;
            let producer_payload = IterativeTypeOwner::new(producer.payload_type());
            if required.interface() != canonical.id
                || producer.interface() != required.interface()
                || producer.method() != method.id
                || producer.witness() != layout.witness()
                || dictionary.producer() != producer
                || !crate::types::same_type_with_budget(&producer_payload, payload, work)
                    .map_err(|()| super::resource())?
                || !crate::types::same_type_with_budget(dictionary.payload_type(), payload, work)
                    .map_err(|()| super::resource())?
                || dictionary.encoding() != encoding
                || dictionary.size() != size
                || dictionary.natural_alignment() != alignment
            {
                return Err(super::invalid(at));
            }
            // The first occurrence still supplies the one copied dictionary
            // binder. Later plans authenticate independently above.
            if index == 0 {
                let (first, first_prerequisite) = &family.requirements[ordinal];
                if !first.shares_plan_with(selection)
                    || first.root() != selection.root()
                    || first_prerequisite != prerequisite
                {
                    return Err(super::invalid(at));
                }
            }
        }
    }
    Ok(())
}

/// The first authenticated occurrence supplies the original dictionary formal.
/// Each later occurrence carries its own separately authenticated receipt.
fn authenticate_family_prerequisite(
    family: &ProviderFamilyAdmission,
    ordinal: usize,
    at: NodeId,
    work: &mut TypeWorkBudget,
) -> Result<crate::foreign::ForeignLayoutProducer, ValidationError> {
    use crate::interface::EvidenceNode;
    super::charge(
        work,
        family
            .requirements
            .len()
            .checked_add(1)
            .ok_or_else(super::resource)?,
    )?;
    let (selection, selected) = family
        .selections
        .first()
        .ok_or_else(|| super::invalid(at))?;
    let Some(EvidenceNode::ProviderFamily {
        source,
        definition,
        parameter,
        application,
        prerequisites,
        ..
    }) = selection.node(*selected)
    else {
        return Err(super::invalid(at));
    };
    if source != family.lexical
        || definition != family.identity.definition
        || parameter != family.identity.parameter
        || prerequisites.len() != family.requirements.len()
        || !same_application(application, &family.application, work)?
    {
        return Err(super::invalid(at));
    }
    for ((first, locator), prerequisite) in family.requirements.iter().zip(prerequisites) {
        if !first.shares_plan_with(selection)
            || first.root() != selection.root()
            || locator != prerequisite
            || prerequisite.index() >= selected.index()
        {
            return Err(super::invalid(at));
        }
    }
    let prerequisite = *prerequisites
        .get(ordinal)
        .ok_or_else(|| super::invalid(at))?;
    let Some(EvidenceNode::NativeLayout { producer }) = selection.node(prerequisite) else {
        return Err(super::invalid(at));
    };
    Ok(producer)
}

/// After `authenticate_family_header` succeeds for these same inputs, produces
/// immutable dictionary projections, never binding or execution authority.
/// Final reauthentication must match each to one ordinary Let with this
/// binder/initializer and check domination of the owning scope.
#[expect(
    clippy::too_many_arguments,
    reason = "original certificate, copied graph and canonical native authority remain separate"
)]
fn authenticate_family_dictionaries(
    admission: &ProviderScopeAdmission,
    family: &ProviderFamilyAdmission,
    entry: &ProviderSpecializationFamilyEntries<'_>,
    copy: &ProviderCopiedTemplate<'_>,
    registry: &crate::resolved::ResolvedRegistry,
    arena: crate::core::dialect::ArenaId,
    target: &[crate::core::dialect::StoredNode<crate::core::EffectOperationFamily>],
    nodes: &std::collections::HashMap<NodeId, NodeId>,
    renaming: &crate::types::TemplateIdentityRenaming<'_>,
    work: &mut TypeWorkBudget,
) -> Result<Vec<SpecializedDictionary>, ValidationError> {
    let at = original_root(copy);
    let certificate = family_certificate(admission, registry, at, work)?;
    super::charge(work, certificate.resource_count())?;
    let requirements = certificate
        .family_requirements(admission.definition.id)
        .ok_or_else(|| super::invalid(at))?;
    authenticate_family_dictionaries_with_requirements(
        admission,
        family,
        entry,
        copy,
        registry,
        arena,
        target,
        nodes,
        renaming,
        requirements,
        work,
    )
}

#[expect(
    clippy::too_many_arguments,
    reason = "source and final admission share canonical dictionary projection checks"
)]
fn authenticate_family_dictionaries_with_requirements(
    admission: &ProviderScopeAdmission,
    family: &ProviderFamilyAdmission,
    entry: &ProviderSpecializationFamilyEntries<'_>,
    copy: &ProviderCopiedTemplate<'_>,
    registry: &crate::resolved::ResolvedRegistry,
    arena: crate::core::dialect::ArenaId,
    target: &[crate::core::dialect::StoredNode<crate::core::EffectOperationFamily>],
    nodes: &std::collections::HashMap<NodeId, NodeId>,
    renaming: &crate::types::TemplateIdentityRenaming<'_>,
    requirements: &[crate::interface::CheckedRequirement],
    work: &mut TypeWorkBudget,
) -> Result<Vec<SpecializedDictionary>, ValidationError> {
    use crate::core::{EffectExprKind, PureExprKind, PureValue};
    use crate::types::{IterativeTypeOwner, Kind, KindedArgument, Type};
    let ProviderOriginalTemplate::Handler(original) = copy.original else {
        return Err(ValidationError::new(
            crate::core::ValidationReason::NodeType,
            None,
        ));
    };
    let at = original.original_program().root;
    let formals = original.original_dictionary_parameters();
    if requirements.len() != family.requirements.len() || entry.dictionaries.len() != formals.len()
    {
        return Err(super::invalid(at));
    }
    let layout = admission
        .native
        .layout
        .as_ref()
        .ok_or_else(|| super::invalid(at))?;
    let storage = admission
        .native
        .storage
        .as_ref()
        .ok_or_else(|| super::invalid(at))?;
    super::charge(work, admission.native.canonical_interfaces().len())?;
    let canonical = admission
        .native
        .canonical_interfaces()
        .iter()
        .find(|interface| interface.id == layout.interface())
        .ok_or_else(|| super::invalid(at))?;
    let [interface_parameter] = canonical.parameters.as_ref() else {
        return Err(super::invalid(at));
    };
    let [method] = canonical.methods.as_ref() else {
        return Err(super::invalid(at));
    };
    if interface_parameter.kind != Kind::Type
        || interface_parameter.id != layout.payload_parameter()
        || method.id != layout.method()
        || method.id.interface() != canonical.id
        || method.id.declaration() != 0
        || !method.type_parameters.is_empty()
        || layout.witness() != storage.witness()
    {
        return Err(super::invalid(at));
    }
    super::charge(
        work,
        formals
            .len()
            .checked_add(requirements.len())
            .ok_or_else(super::resource)?,
    )?;
    let mut dictionaries = Vec::new();
    dictionaries
        .try_reserve_exact(formals.len())
        .map_err(|_| super::resource())?;
    let mut binders = std::collections::HashSet::new();
    binders
        .try_reserve(formals.len())
        .map_err(|_| super::resource())?;
    let mut position = 0usize;
    for (ordinal, requirement) in requirements.iter().enumerate() {
        if requirement.id.owner()
            != crate::interface::RequirementOwner::ResourceFamily(admission.definition.id)
            || usize::try_from(requirement.id.declaration()).ok() != Some(ordinal)
            || requirement.interface() != canonical.id
        {
            return Err(super::invalid(at));
        }
        // This scalar checkpoint admits the sealed one-method Layout contract;
        // other prerequisite categories remain unsupported rather than erased.
        let [KindedArgument::TypeArg(payload)] = requirement.arguments() else {
            return Err(super::invalid(at));
        };
        let formal = formals.get(position).ok_or_else(|| super::invalid(at))?;
        let supplied = entry
            .dictionaries
            .get(position)
            .ok_or_else(|| super::invalid(at))?;
        let mut replacements = std::collections::HashMap::new();
        super::charge(work, 1)?;
        replacements.try_reserve(1).map_err(|_| super::resource())?;
        replacements.insert(interface_parameter.id, payload);
        let signature = IterativeTypeOwner::new(
            crate::types::substitute_type_variables_borrowed_with(
                &method.annotation.ty,
                &replacements,
                |units| work.charge(units),
                || (),
            )
            .map_err(|()| super::resource())?,
        );
        if !crate::types::same_type_with_budget(&signature, formal.ty(), work)
            .map_err(|()| super::resource())?
        {
            return Err(super::invalid(at));
        }
        let expected = specialized_application(requirement.application(), copy, renaming, work)?;
        let [KindedArgument::TypeArg(payload)] = expected.arguments() else {
            return Err(super::invalid(at));
        };
        if !matches!(payload, Type::Unit | Type::Bool | Type::Int) {
            return Err(super::invalid(at));
        }
        let producer = authenticate_family_prerequisite(family, ordinal, at, work)?;
        let dictionary = registry
            .foreign_layout_dictionary(producer, work)
            .map_err(|failure| {
                if failure.is_resource_exhaustion() {
                    super::resource()
                } else {
                    super::invalid(at)
                }
            })?;
        let (encoding, size, alignment) = match payload {
            Type::Unit => (crate::foreign::ForeignScalarEncoding::Unit, 0, 1),
            Type::Bool => (crate::foreign::ForeignScalarEncoding::Bool, 1, 1),
            Type::Int => (crate::foreign::ForeignScalarEncoding::Signed64, 8, 8),
            _ => return Err(super::invalid(at)),
        };
        let producer_payload = IterativeTypeOwner::new(producer.payload_type());
        if producer.interface() != expected.interface()
            || producer.method() != method.id
            || producer.witness() != layout.witness()
            || dictionary.producer() != producer
            || !crate::types::same_type_with_budget(dictionary.payload_type(), payload, work)
                .map_err(|()| super::resource())?
            || !crate::types::same_type_with_budget(&producer_payload, payload, work)
                .map_err(|()| super::resource())?
            || dictionary.encoding() != encoding
            || dictionary.size() != size
            || dictionary.natural_alignment() != alignment
        {
            return Err(super::invalid(at));
        }
        let binder = renamed(formal.id(), copy.freshening.binders, work)?;
        if binder == formal.id()
            || binder != supplied.binder.id()
            || !matches!(binder, crate::resolved::BinderId::Generated(_))
            || supplied.binder.arena() != arena
            || !binders.insert(binder)
        {
            return Err(super::invalid(at));
        }
        let original_projection = super::projection::project_binder(at, formal, work)?;
        let projection = specialize_projection(
            &original_projection,
            nodes,
            &copy.freshening,
            &copy.substitution,
            renaming,
            work,
        )?;
        let actual_projection =
            super::projection::project_binder(projection.node, supplied.binder, work)?;
        if !projection.same(&actual_projection, work)? {
            return Err(super::invalid(projection.node));
        }
        let stored = target_node(arena, target, supplied.initializer)?;
        let EffectExprKind::Pure(PureExprKind::Value(PureValue::Intrinsic(intrinsic))) =
            &stored.kind
        else {
            return Err(super::invalid(supplied.initializer));
        };
        let producer_type = IterativeTypeOwner::new(producer.producer_type());
        if intrinsic.operation()
            != (crate::core::packed::Intrinsic::ForeignLayoutWitness { producer })
            || intrinsic.module() != producer.interface().module()
            || !stored.effects.is_empty()
            || !crate::types::same_type_with_budget(&stored.ty, &producer_type, work)
                .map_err(|()| super::resource())?
            || !crate::types::same_type_with_budget(supplied.binder.ty(), &stored.ty, work)
                .map_err(|()| super::resource())?
        {
            return Err(super::invalid(supplied.initializer));
        }
        dictionaries.push(SpecializedDictionary {
            requirement: requirement.id,
            method: method.id,
            binder,
            projection,
            initializer: super::projection::project(supplied.initializer, stored, work)?,
            producer,
        });
        position = position.checked_add(1).ok_or_else(super::resource)?;
    }
    if position != formals.len() {
        return Err(super::invalid(at));
    }
    Ok(dictionaries)
}

/// Transfers sealed original flow facts only after every copied node and catalog
/// occurrence has matched its original projection under the complete sigma.
#[expect(
    clippy::too_many_arguments,
    reason = "source token, sigma and copied graph are separate authority"
)]
fn transfer_native_storage_relations(
    admission: &ProviderScopeAdmission,
    index: usize,
    copy: &ProviderCopiedTemplate<'_>,
    arena: crate::core::dialect::ArenaId,
    target: &[crate::core::dialect::StoredNode<crate::core::EffectOperationFamily>],
    nodes: &std::collections::HashMap<NodeId, NodeId>,
    renaming: &crate::types::TemplateIdentityRenaming<'_>,
    proof: &mut SpecializationProof,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    let ProviderOriginalTemplate::Handler(original) = copy.original else {
        return Err(super::invalid(original_root(copy)));
    };
    let family = admission
        .families
        .get(index)
        .ok_or_else(|| super::invalid(proof.body))?;
    let storage = admission
        .native
        .storage
        .as_ref()
        .ok_or_else(|| super::invalid(proof.body))?;
    let member = index.checked_add(1).ok_or_else(super::resource)?;
    let relations = original.original_native_storage_relations();
    super::charge(work, relations.len())?;
    proof
        .native_storage
        .try_reserve(relations.len())
        .map_err(|_| super::resource())?;
    for relation in relations {
        let request = mapped(nodes, relation.request())?;
        let effect = substitute_instance(relation.effect(), &copy.substitution, renaming, work)?;
        let crate::core::EffectExprKind::Operation(crate::core::EffectOperation::Request(actual)) =
            &target_node(arena, target, request)?.kind
        else {
            return Err(super::invalid(request));
        };
        let crate::core::EffectExprKind::Operation(crate::core::EffectOperation::Request(source)) =
            &super::node(original.original_program(), relation.request())?.kind
        else {
            return Err(super::invalid(request));
        };
        let owner = copy
            .substitution
            .types
            .get(&relation.owner())
            .ok_or_else(|| super::invalid(request))?;
        let result_matches = match relation.result() {
            super::HandlerNativeStorageResult::Store { allocated, refused } => {
                relation.operation() == storage.store()
                    && allocated == storage.allocated_constructor()
                    && refused == storage.refused_constructor()
            }
            super::HandlerNativeStorageResult::Load => relation.operation() == storage.load(),
        };
        if relation.family() != family.identity
            || !matches!(owner, crate::types::Type::Variable(owner) if *owner == admission.identity)
            || !result_matches
            || effect.effect() != storage.effect()
            || actual.operation() != relation.operation()
            || actual.operand() != mapped(nodes, source.operand())?
            || source.operation() != relation.operation()
            || crate::types::compare_effect_instances_with_budget(
                source.effect(),
                relation.effect(),
                work,
            )
            .map_err(|()| super::resource())?
                != std::cmp::Ordering::Equal
            || crate::types::compare_effect_instances_with_budget(actual.effect(), &effect, work)
                .map_err(|()| super::resource())?
                != std::cmp::Ordering::Equal
            || crate::types::compare_effect_instances_with_budget(
                &effect,
                &family.native_effect,
                work,
            )
            .map_err(|()| super::resource())?
                != std::cmp::Ordering::Equal
        {
            return Err(super::invalid(request));
        }
        let operand = actual.operand();
        proof.native_storage.push(AdmittedNativeStorageRelation {
            request,
            operand,
            request_projection: super::projection::project(
                request,
                target_node(arena, target, request)?,
                work,
            )?,
            operand_projection: super::projection::project(
                operand,
                target_node(arena, target, operand)?,
                work,
            )?,
            operation: relation.operation(),
            effect,
            owner: admission.identity,
            family: relation.family(),
            member,
            result: relation.result(),
        });
    }
    Ok(())
}

fn same_family_header(
    expected: &ProviderFamilyAdmission,
    actual: &ProviderFamilyAdmission,
    work: &mut TypeWorkBudget,
) -> Result<bool, ValidationError> {
    if expected.identity != actual.identity
        || expected.lexical != actual.lexical
        || expected.requirements.len() != actual.requirements.len()
        || expected.selections.len() != actual.selections.len()
        || !same_application(&expected.application, &actual.application, work)?
        || !crate::types::same_type_with_budget(&expected.payload, &actual.payload, work)
            .map_err(|()| super::resource())?
        || crate::types::compare_effect_instances_with_budget(
            &expected.native_effect,
            &actual.native_effect,
            work,
        )
        .map_err(|()| super::resource())?
            != std::cmp::Ordering::Equal
    {
        return Ok(false);
    }
    super::charge(
        work,
        expected
            .requirements
            .len()
            .checked_add(expected.selections.len())
            .ok_or_else(super::resource)?,
    )?;
    Ok(expected
        .requirements
        .iter()
        .zip(&actual.requirements)
        .all(|((left, lp), (right, rp))| {
            lp == rp && left.shares_plan_with(right) && left.root() == right.root()
        })
        && expected
            .selections
            .iter()
            .zip(&actual.selections)
            .all(|((left, lp), (right, rp))| {
                lp == rp && left.shares_plan_with(right) && left.root() == right.root()
            }))
}

fn authenticate_family_members(
    proof: &SpecializationProof,
    scope: &ProviderScopeNode,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    if proof.families.len() != scope.attached.len()
        || proof.families.len() != scope.descriptor.family_members().len()
    {
        return Err(super::invalid(proof.body));
    }
    super::charge(work, proof.families.len())?;
    for (index, expected) in proof.families.iter().enumerate() {
        let member = index.checked_add(1).ok_or_else(super::resource)?;
        let handler = scope
            .handler_member(member)
            .ok_or_else(|| super::invalid(proof.body))?;
        let state = scope
            .handler_state_member(member)
            .ok_or_else(|| super::invalid(proof.body))?;
        if !same_family_header(
            &expected.header,
            &scope.descriptor.family_members()[index],
            work,
        )? || handler.id() != expected.handler
            || handler.body() != proof.body
            || handler.clauses().len() != expected.clauses.len()
            || crate::types::compare_effect_instances_with_budget(
                handler.effect(),
                &expected.provided,
                work,
            )
            .map_err(|()| super::resource())?
                != std::cmp::Ordering::Equal
            || !expected.state.same(
                &super::projection::project_binder(expected.state.node, state, work)?,
                work,
            )?
        {
            return Err(super::invalid(proof.body));
        }
        super::charge(work, expected.clauses.len())?;
        for (expected, clause) in expected.clauses.iter().zip(handler.clauses()) {
            if !expected.same(&super::projection::project_clause(clause, work)?, work)? {
                return Err(super::invalid(expected.node));
            }
        }
    }
    Ok(())
}

/// Capture admission authenticates the copied request signature and its member
/// receipt. Final Core admission separately authenticates all original nodes,
/// origins, catalog occurrences and dictionary domination.
pub(in crate::core) fn authenticate_native_storage_relations<
    'a,
    F: crate::core::dialect::CoreOperationFamily,
>(
    arena: crate::core::dialect::ArenaId,
    nodes: &[crate::core::dialect::StoredNode<F>],
    scope: &'a ProviderScopeNode,
    operation: for<'b> fn(&'b F::Kind) -> Option<&'b crate::core::EffectOperation>,
    work: &mut TypeWorkBudget,
) -> Result<&'a [AdmittedNativeStorageRelation], ValidationError> {
    let specialization = scope
        .descriptor
        .specialization()
        .ok_or_else(|| super::invalid(scope.handler.body()))?;
    authenticate_copied_native_storage_relations(
        arena,
        nodes,
        scope,
        &specialization.0,
        operation,
        work,
    )
}

/// Borrowed source-analysis facts after exact current-arena reauthentication.
/// These facts cannot construct a final specialization or final layout token.
struct AuthenticatedProviderCaptureProjection<'a> {
    proof: &'a SpecializationProof,
    scope: &'a ProviderScopeNode,
    nodes_address: *const (),
    nodes_len: usize,
    operation_family: std::any::TypeId,
}
impl<'a> AuthenticatedProviderCaptureProjection<'a> {
    pub(in crate::core) fn native_storage_relations(&self) -> &'a [AdmittedNativeStorageRelation] {
        &self.proof.native_storage
    }
    pub(in crate::core) fn authenticates_scope<F: crate::core::dialect::CoreOperationFamily>(
        &self,
        nodes: &[crate::core::dialect::StoredNode<F>],
        scope: &ProviderScopeNode,
    ) -> bool {
        self.operation_family == std::any::TypeId::of::<F>()
            && self.nodes_len == nodes.len()
            && std::ptr::eq(self.nodes_address, nodes.as_ptr().cast::<()>())
            && std::ptr::eq(self.scope, scope)
    }
    pub(in crate::core) fn authenticates_layout<F: crate::core::dialect::CoreOperationFamily>(
        &self,
        nodes: &[crate::core::dialect::StoredNode<F>],
        ordinal: usize,
        producer: crate::foreign::ForeignLayoutProducer,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        super::charge(work, 1)?;
        if self.operation_family != std::any::TypeId::of::<F>()
            || self.nodes_len != nodes.len()
            || ordinal >= nodes.len()
            || !std::ptr::eq(self.nodes_address, nodes.as_ptr().cast::<()>())
        {
            return Ok(false);
        }
        super::charge(work, self.proof.families.len())?;
        for family in &self.proof.families {
            super::charge(work, family.dictionaries.len())?;
            for dictionary in &family.dictionaries {
                if dictionary.initializer.node.index().ok() == Some(ordinal)
                    && dictionary.producer == producer
                {
                    return Ok(true);
                }
            }
        }
        Ok(false)
    }
}

/// Exact copied-flow receipt for a still-prepared source scope. This cannot
/// authenticate an admitted scope or construct a final Core layout token.
pub(in crate::core) struct AuthenticatedPreparedProviderCapture<'a>(
    AuthenticatedProviderCaptureProjection<'a>,
);
impl<'a> AuthenticatedPreparedProviderCapture<'a> {
    pub(in crate::core) fn native_storage_relations(&self) -> &'a [AdmittedNativeStorageRelation] {
        self.0.native_storage_relations()
    }
    pub(in crate::core) fn authenticates_scope<F: crate::core::dialect::CoreOperationFamily>(
        &self,
        nodes: &[crate::core::dialect::StoredNode<F>],
        scope: &ProviderScopeNode,
    ) -> bool {
        self.0.authenticates_scope(nodes, scope)
    }
    pub(in crate::core) fn authenticates_layout<F: crate::core::dialect::CoreOperationFamily>(
        &self,
        nodes: &[crate::core::dialect::StoredNode<F>],
        ordinal: usize,
        producer: crate::foreign::ForeignLayoutProducer,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        self.0.authenticates_layout(nodes, ordinal, producer, work)
    }
}

/// Source analysis of a genuine admitted specialization. This borrows only
/// reauthenticated dictionary bindings and native-flow projections; it is not
/// independent whole-program Core validation or a Prepared receipt.
pub(in crate::core) struct AuthenticatedAdmittedProviderCapture<'a>(
    AuthenticatedProviderCaptureProjection<'a>,
);

/// Both source phases retain their distinct original authority. A graph borrows
/// each exact-slice view once for dictionary values and native request transfer.
pub(in crate::core) enum AuthenticatedProviderSourceCapture<'a> {
    Prepared(AuthenticatedPreparedProviderCapture<'a>),
    Admitted(AuthenticatedAdmittedProviderCapture<'a>),
}
impl<'a> AuthenticatedProviderSourceCapture<'a> {
    pub(in crate::core) fn native_storage_relations(&self) -> &'a [AdmittedNativeStorageRelation] {
        match self {
            Self::Prepared(view) => view.native_storage_relations(),
            Self::Admitted(view) => view.0.native_storage_relations(),
        }
    }
    pub(in crate::core) fn authenticates_scope<F: crate::core::dialect::CoreOperationFamily>(
        &self,
        nodes: &[crate::core::dialect::StoredNode<F>],
        scope: &ProviderScopeNode,
    ) -> bool {
        match self {
            Self::Prepared(view) => view.authenticates_scope(nodes, scope),
            Self::Admitted(view) => view.0.authenticates_scope(nodes, scope),
        }
    }
    pub(in crate::core) fn authenticates_layout<F: crate::core::dialect::CoreOperationFamily>(
        &self,
        nodes: &[crate::core::dialect::StoredNode<F>],
        ordinal: usize,
        producer: crate::foreign::ForeignLayoutProducer,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ValidationError> {
        match self {
            Self::Prepared(view) => view.authenticates_layout(nodes, ordinal, producer, work),
            Self::Admitted(view) => view.0.authenticates_layout(nodes, ordinal, producer, work),
        }
    }
}

/// Source capture alone may consume this separately sealed receipt. A legacy
/// Prepared descriptor or any final specialization cannot supply this token.
/// Every original copied projection is checked against the post-zonk arena.
pub(in crate::core) fn authenticate_prepared_provider_capture<
    'a,
    F: crate::core::dialect::CoreOperationFamily,
>(
    arena: crate::core::dialect::ArenaId,
    nodes: &'a [crate::core::dialect::StoredNode<F>],
    scope: &'a ProviderScopeNode,
    operation: for<'b> fn(&'b F::Kind) -> Option<&'b crate::core::EffectOperation>,
    work: &mut TypeWorkBudget,
) -> Result<AuthenticatedPreparedProviderCapture<'a>, ValidationError> {
    let receipt = scope
        .descriptor
        .prepared_capture()
        .ok_or_else(|| super::invalid(scope.handler.body()))?;
    let proof = &receipt.0;
    super::charge(
        work,
        proof
            .nodes
            .len()
            .checked_add(proof.clauses.len())
            .ok_or_else(super::resource)?,
    )?;
    for expected in &proof.nodes {
        let stored = capture_target_node(arena, nodes, expected.node)?;
        let actual = super::projection::project_with::<F>(expected.node, stored, operation, work)?;
        if !expected.same(&actual, work)? {
            return Err(super::invalid(expected.node));
        }
    }
    if proof.clauses.len() != scope.handler.clauses().len() {
        return Err(super::invalid(proof.body));
    }
    for (expected, clause) in proof.clauses.iter().zip(scope.handler.clauses()) {
        if !expected.same(&super::projection::project_clause(clause, work)?, work)? {
            return Err(super::invalid(expected.node));
        }
    }
    authenticate_capture_dictionary_bindings(arena, nodes, proof, operation, work)?;
    authenticate_copied_native_storage_relations(arena, nodes, scope, proof, operation, work)?;
    Ok(AuthenticatedPreparedProviderCapture(
        AuthenticatedProviderCaptureProjection {
            proof,
            scope,
            nodes_address: nodes.as_ptr().cast::<()>(),
            nodes_len: nodes.len(),
            operation_family: std::any::TypeId::of::<F>(),
        },
    ))
}

/// A final copied specialization may be analyzed before whole-program Core
/// validation, while cleanup rows are still being solved. Authenticate only the
/// exact source-analysis facts consumed here; final catalog, whole-forest and
/// dictionary domination validation remain in OriginalProviderSpecialization.
#[inline(never)]
pub(in crate::core) fn authenticate_admitted_provider_capture<
    'a,
    F: crate::core::dialect::CoreOperationFamily,
>(
    arena: crate::core::dialect::ArenaId,
    nodes: &'a [crate::core::dialect::StoredNode<F>],
    scope: &'a ProviderScopeNode,
    operation: for<'b> fn(&'b F::Kind) -> Option<&'b crate::core::EffectOperation>,
    work: &mut TypeWorkBudget,
) -> Result<AuthenticatedAdmittedProviderCapture<'a>, ValidationError> {
    let specialization = scope
        .descriptor
        .specialization()
        .ok_or_else(|| super::invalid(scope.handler.body()))?;
    let proof = &specialization.0;
    authenticate_copied_native_storage_relations(arena, nodes, scope, proof, operation, work)?;
    authenticate_capture_dictionary_bindings(arena, nodes, proof, operation, work)?;
    Ok(AuthenticatedAdmittedProviderCapture(
        AuthenticatedProviderCaptureProjection {
            proof,
            scope,
            nodes_address: nodes.as_ptr().cast::<()>(),
            nodes_len: nodes.len(),
            operation_family: std::any::TypeId::of::<F>(),
        },
    ))
}

fn authenticate_capture_dictionary_bindings<F: crate::core::dialect::CoreOperationFamily>(
    arena: crate::core::dialect::ArenaId,
    nodes: &[crate::core::dialect::StoredNode<F>],
    proof: &SpecializationProof,
    operation: for<'b> fn(&'b F::Kind) -> Option<&'b crate::core::EffectOperation>,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    super::charge(work, proof.families.len())?;
    for family in &proof.families {
        super::charge(work, family.dictionaries.len())?;
        for dictionary in &family.dictionaries {
            authenticate_dictionary_binding_nodes(arena, nodes, dictionary, operation, None, work)?;
        }
    }
    Ok(())
}

fn capture_target_node<F: crate::core::dialect::CoreOperationFamily>(
    arena: crate::core::dialect::ArenaId,
    nodes: &[crate::core::dialect::StoredNode<F>],
    node: NodeId,
) -> Result<&crate::core::dialect::StoredNode<F>, ValidationError> {
    if node.arena() != arena {
        return Err(super::invalid(node));
    }
    nodes
        .get(node.index().map_err(|_| super::invalid(node))?)
        .ok_or_else(|| super::invalid(node))
}

fn authenticate_copied_native_storage_relations<
    'a,
    F: crate::core::dialect::CoreOperationFamily,
>(
    arena: crate::core::dialect::ArenaId,
    nodes: &[crate::core::dialect::StoredNode<F>],
    scope: &ProviderScopeNode,
    proof: &'a SpecializationProof,
    operation: for<'b> fn(&'b F::Kind) -> Option<&'b crate::core::EffectOperation>,
    work: &mut TypeWorkBudget,
) -> Result<&'a [AdmittedNativeStorageRelation], ValidationError> {
    if proof.arena != arena
        || proof.definition != scope.descriptor.definition().id
        || proof.body != scope.handler.body()
        || proof.handler != scope.handler.id()
        || proof.acquire != scope.acquire.body
        || proof.finish != scope.finish.body
        || proof.families.len() != scope.attached.len()
        || proof.families.len() != scope.descriptor.family_members().len()
    {
        return Err(super::invalid(proof.body));
    }
    if proof.families.is_empty() && proof.native_storage.is_empty() {
        return Ok(&proof.native_storage);
    }
    if proof
        .native
        .as_ref()
        .is_none_or(|native| !std::ptr::eq(native.as_ref(), scope.descriptor.native()))
    {
        return Err(super::invalid(proof.body));
    }
    authenticate_family_members(proof, scope, work)?;
    for (expected, binder) in [
        (&proof.parameters[0], &scope.acquire.parameter),
        (&proof.parameters[1], &scope.finish.parameter),
        (&proof.parameters[2], &scope.handler_state),
    ] {
        if !expected.same(
            &super::projection::project_binder(expected.node, binder, work)?,
            work,
        )? {
            return Err(super::invalid(expected.node));
        }
    }
    let storage = scope
        .descriptor
        .native()
        .storage
        .as_ref()
        .ok_or_else(|| super::invalid(proof.body))?;
    super::charge(work, proof.native_storage.len())?;
    for receipt in &proof.native_storage {
        let get = |node: NodeId| {
            if node.arena() != arena {
                return Err(super::invalid(node));
            }
            nodes
                .get(node.index().map_err(|_| super::invalid(node))?)
                .ok_or_else(|| super::invalid(node))
        };
        let stored = get(receipt.request)?;
        let Some(crate::core::EffectOperation::Request(request)) = operation(&stored.kind) else {
            return Err(super::invalid(receipt.request));
        };
        let family = receipt
            .member
            .checked_sub(1)
            .and_then(|index| proof.families.get(index))
            .ok_or_else(|| super::invalid(receipt.request))?;
        let result_matches = match receipt.result {
            super::HandlerNativeStorageResult::Store { allocated, refused } => {
                receipt.operation == storage.store()
                    && allocated == storage.allocated_constructor()
                    && refused == storage.refused_constructor()
            }
            super::HandlerNativeStorageResult::Load => receipt.operation == storage.load(),
        };
        if !result_matches
            || receipt.family != family.header.identity
            || receipt.owner != scope.descriptor.identity()
            || request.operation() != receipt.operation
            || request.operand() != receipt.operand
            || receipt.effect.effect() != storage.effect()
            || crate::types::compare_effect_instances_with_budget(
                request.effect(),
                &receipt.effect,
                work,
            )
            .map_err(|()| super::resource())?
                != std::cmp::Ordering::Equal
            || crate::types::compare_effect_instances_with_budget(
                &receipt.effect,
                &family.header.native_effect,
                work,
            )
            .map_err(|()| super::resource())?
                != std::cmp::Ordering::Equal
        {
            return Err(super::invalid(receipt.request));
        }
        for (expected, actual) in [
            (&receipt.request_projection, stored),
            (&receipt.operand_projection, get(receipt.operand)?),
        ] {
            let current =
                super::projection::project_with::<F>(expected.node, actual, operation, work)?;
            if !expected.same(&current, work)? {
                return Err(super::invalid(expected.node));
            }
        }
    }
    Ok(&proof.native_storage)
}

/// Only an ordinary nonrecursive Let may realize an original dictionary formal.
fn authenticate_dictionary_binding(
    expected: &SpecializedDictionary,
    program: &UnvalidatedEffectProgram,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    authenticate_dictionary_binding_nodes(
        program.arena,
        &program.nodes,
        expected,
        super::row::effect_operation,
        Some(&program.registry),
        work,
    )?;
    Ok(())
}

fn authenticate_dictionary_binding_nodes<F: crate::core::dialect::CoreOperationFamily>(
    arena: crate::core::dialect::ArenaId,
    nodes: &[crate::core::dialect::StoredNode<F>],
    expected: &SpecializedDictionary,
    operation: for<'b> fn(&'b F::Kind) -> Option<&'b crate::core::EffectOperation>,
    registry: Option<&crate::resolved::ResolvedRegistry>,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    super::charge(work, nodes.len())?;
    let mut matched = false;
    for stored in nodes {
        use crate::core::{PureComputation as C, PureExprKind as P, PureValue as V};
        let mut other_declaration = false;
        let mut declarations = 0usize;
        F::visit_operation_binders(&stored.kind, &mut |binder| {
            declarations = declarations.saturating_add(1);
            other_declaration |= binder.id() == expected.binder;
        });
        super::charge(work, declarations)?;
        match F::pure(&stored.kind) {
            Some(P::Value(V::Function(function))) => {
                other_declaration |= function.parameter().id() == expected.binder;
            }
            Some(P::Computation(C::RecursiveBind(group))) => {
                super::charge(work, group.members().len())?;
                other_declaration |= group
                    .members()
                    .iter()
                    .any(|member| member.binder().id() == expected.binder);
            }
            Some(P::Computation(C::Match(matching))) => {
                super::charge(work, matching.arms().len())?;
                for arm in matching.arms() {
                    for binder in arm.pattern().binder_iter() {
                        super::charge(work, 1)?;
                        other_declaration |= binder.id() == expected.binder;
                    }
                }
            }
            _ => {}
        }
        if other_declaration {
            return Err(super::invalid(expected.projection.node));
        }
        let Some(P::Computation(C::Bind(binding))) = F::pure(&stored.kind) else {
            continue;
        };
        if binding.binder().id() != expected.binder {
            continue;
        }
        if matched
            || binding.initializer() != expected.initializer.node
            || !expected.projection.same(
                &super::projection::project_binder(
                    expected.projection.node,
                    binding.binder(),
                    work,
                )?,
                work,
            )?
        {
            return Err(super::invalid(expected.projection.node));
        }
        matched = true;
    }
    if !matched {
        return Err(super::invalid(expected.projection.node));
    }
    let stored = capture_target_node(arena, nodes, expected.initializer.node)?;
    if !expected.initializer.same(
        &super::projection::project_with::<F>(expected.initializer.node, stored, operation, work)?,
        work,
    )? {
        return Err(super::invalid(expected.initializer.node));
    }
    let Some(crate::core::PureExprKind::Value(crate::core::PureValue::Intrinsic(intrinsic))) =
        F::pure(&stored.kind)
    else {
        return Err(super::invalid(expected.initializer.node));
    };
    let ty = crate::types::IterativeTypeOwner::new(expected.producer.producer_type());
    if let Some(registry) = registry {
        registry
            .foreign_layout_dictionary(expected.producer, work)
            .map_err(|failure| {
                if failure.is_resource_exhaustion() {
                    super::resource()
                } else {
                    super::invalid(expected.initializer.node)
                }
            })?;
    }
    if intrinsic.operation()
        != (crate::core::packed::Intrinsic::ForeignLayoutWitness {
            producer: expected.producer,
        })
        || intrinsic.module() != expected.producer.interface().module()
        || !F::effect_row(&stored.effects).is_empty()
        || !crate::types::same_type_with_budget(&stored.ty, &ty, work)
            .map_err(|()| super::resource())?
    {
        return Err(super::invalid(expected.initializer.node));
    }
    Ok(())
}

/// Source receipts freeze only complete types and rows. Later source zonking
/// must preserve these projections; inference is never a wildcard authority.
fn authenticate_concrete_capture_projections(
    proof: &SpecializationProof,
    work: &mut TypeWorkBudget,
) -> Result<(), ValidationError> {
    use crate::types::{
        EffectRowVariable, IterativeArgumentOwner, KindedArgument, Type, TypeStructureNode,
    };
    fn unresolved(node: TypeStructureNode<'_>, _: &mut TypeWorkBudget) -> Result<bool, ()> {
        Ok(matches!(node, TypeStructureNode::Type(Type::Inference(_)))
            || matches!(node, TypeStructureNode::Tail(tail)
                if matches!(tail.variable(), EffectRowVariable::Inference(_))))
    }
    fn check(
        projection: &super::projection::NodeProjection,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        super::charge(work, projection.metadata.len())?;
        for metadata in &projection.metadata {
            let pending = match metadata {
                super::projection::Metadata::Type(ty) => {
                    crate::types::visit_type_structure_with_budget(ty, work, unresolved)
                }
                super::projection::Metadata::Argument(argument) => {
                    crate::types::visit_argument_structure_with_budget(argument, work, unresolved)
                }
                super::projection::Metadata::Row(row) => {
                    let row = crate::types::clone_effect_row_with_budget(row, work)
                        .map_err(|()| super::resource())?;
                    let argument = IterativeArgumentOwner::new(KindedArgument::RowArg(row));
                    crate::types::visit_argument_structure_with_budget(&argument, work, unresolved)
                }
                super::projection::Metadata::Kind(_) => Ok(false),
            }
            .map_err(|()| super::resource())?;
            if pending {
                return Err(super::invalid(projection.node));
            }
        }
        Ok(())
    }
    super::charge(
        work,
        proof
            .nodes
            .len()
            .checked_add(proof.clauses.len())
            .and_then(|count| count.checked_add(proof.parameters.len()))
            .and_then(|count| count.checked_add(proof.families.len()))
            .ok_or_else(super::resource)?,
    )?;
    for projection in proof
        .nodes
        .iter()
        .chain(&proof.parameters)
        .chain(&proof.clauses)
    {
        check(projection, work)?;
    }
    for family in &proof.families {
        check(&family.state, work)?;
        super::charge(
            work,
            family
                .clauses
                .len()
                .checked_add(family.dictionaries.len())
                .ok_or_else(super::resource)?,
        )?;
        for clause in &family.clauses {
            check(clause, work)?;
        }
        for dictionary in &family.dictionaries {
            check(&dictionary.projection, work)?;
            check(&dictionary.initializer, work)?;
        }
    }
    Ok(())
}

fn original_root(copy: &ProviderCopiedTemplate<'_>) -> NodeId {
    match copy.original {
        ProviderOriginalTemplate::Lifecycle(_, program) => program.root,
        ProviderOriginalTemplate::Handler(original) => original.original_program().root,
    }
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
        let proof =
            self.reconstruct_provider_scope_capture(&admission, &entries, copies, None, work)?;
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
            families: std::mem::take(&mut admission.families),
        };
        Ok(std::sync::Arc::new(descriptor))
    }

    /// Source capture preparation authenticates copied flow without publishing
    /// a final catalog, executable descriptor, or final specialization token.
    pub(crate) fn prepare_provider_scope_capture(
        &self,
        admission: ProviderScopeAdmission,
        entries: ProviderSpecializationEntries<'_>,
        copies: &[ProviderCopiedTemplate<'_>],
        original: ProviderPreparedFamilyOriginal<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<super::ProviderScopeAuthority, ValidationError> {
        if admission.families.is_empty()
            || !std::sync::Arc::ptr_eq(original.authority.fact(), &admission.definition)
        {
            return Err(super::invalid(entries.body));
        }
        original.authority.authenticate(original.committed, work)?;
        let contract = ProviderFamilyContractView {
            identity: original.authority.identity(),
            application: original.authority.application(),
            requirements: original.authority.requirements(),
            methods: original.authority.methods(),
            handler: original.authority.handler_certificate(),
        };
        let proof = self.reconstruct_provider_scope_capture(
            &admission,
            &entries,
            copies,
            Some(&contract),
            work,
        )?;
        authenticate_concrete_capture_projections(&proof, work)?;
        super::charge(work, 1)?;
        Ok(super::ProviderScopeAuthority::prepared_with_capture(
            admission,
            PreparedProviderCaptureReceipt(std::sync::Arc::new(proof)),
        ))
    }

    fn reconstruct_provider_scope_capture(
        &self,
        admission: &ProviderScopeAdmission,
        entries: &ProviderSpecializationEntries<'_>,
        copies: &[ProviderCopiedTemplate<'_>],
        source_contract: Option<&ProviderFamilyContractView<'_>>,
        work: &mut TypeWorkBudget,
    ) -> Result<SpecializationProof, ValidationError> {
        use super::projection::{project, project_binder, project_clause};
        use crate::types::{
            KindedArgument, TemplateIdentityRenaming, Type, same_effect_rows_with_budget,
            same_type_with_budget,
        };
        let (arena, target, catalog) = self
            .provider_projection_parts()
            .map_err(|_| super::invalid(entries.body))?;
        let grouped = !admission.families.is_empty();
        let expected_copies = admission
            .families
            .len()
            .checked_add(3)
            .ok_or_else(super::resource)?;
        if copies.len() != expected_copies
            || entries.families.len() != admission.families.len()
            || admission.arguments.len() != admission.definition.parameters.len()
            || !matches!(admission.arguments.first(),Some(KindedArgument::TypeArg(Type::Variable(id))) if *id==admission.identity)
        {
            return Err(super::invalid(entries.body));
        }
        let body = target_node(arena, target, entries.body)?;
        let group_rows = if grouped {
            Some(reconstruct_group_rows(admission, copies, body, work)?)
        } else {
            None
        };
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
            families: Vec::new(),
            native_storage: Vec::new(),
            native: grouped.then(|| std::sync::Arc::clone(&admission.native)),
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
        let mut family_phases = Vec::new();
        if grouped {
            super::charge(work, admission.families.len())?;
            family_phases
                .try_reserve_exact(admission.families.len())
                .map_err(|_| super::resource())?;
            family_phases.resize(admission.families.len(), false);
            proof
                .families
                .try_reserve_exact(admission.families.len())
                .map_err(|_| super::resource())?;
        }
        for (copy_index, copy) in copies.iter().enumerate() {
            let family_index = (grouped && copy_index >= 3).then(|| copy_index - 3);
            copy.freshening.authenticate(work)?;
            if copy.substitution.types.len()
                != type_count
                    .checked_add(1)
                    .and_then(|count| count.checked_add(usize::from(family_index.is_some())))
                    .ok_or_else(super::resource)?
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
                    if grouped && copy_index != phase {
                        return Err(super::invalid(entries.body));
                    }
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
                    let (actual_state_binder, actual_handler, actual_clauses) =
                        if let Some(index) = family_index {
                            let family = entries
                                .families
                                .get(index)
                                .ok_or_else(|| super::invalid(entries.body))?;
                            (family.state, family.handler, family.clauses)
                        } else {
                            if grouped && copy_index != 2 {
                                return Err(super::invalid(entries.body));
                            }
                            (entries.state, entries.handler, entries.clauses)
                        };
                    if original.original_template().definition() != admission.definition.id
                        || original.original_template()
                            != crate::resolved::ProviderTemplateId::new(
                                admission.definition.id,
                                if family_index.is_some() { 3 } else { 2 },
                            )
                        || renamed(original.original_handler(), copy.freshening.handlers, work)?
                            != actual_handler
                        || original.original_clauses().len() != actual_clauses.len()
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
                        actual_state_binder,
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
                    let actual_capture = if original.original_recipe().discards().is_empty() {
                        None
                    } else {
                        Some(
                            crate::core::capture::prepare_actual_provider_capture(
                                self,
                                entries.body,
                                entries.capture_globals,
                                &[],
                                &[],
                                &[],
                                &admission.native_effect,
                                crate::core::provider::row::effect_operation,
                                work,
                            )
                            .map_err(|failure| match failure {
                                crate::core::capture::Failure::Resource => super::resource(),
                                _ => super::invalid(entries.body),
                            })?,
                        )
                    };
                    let legacy_rows = if grouped {
                        None
                    } else {
                        Some(original.prepare_rows(
                            &formals.types,
                            &formals.rows,
                            &body.ty,
                            &body.effects,
                            &provided,
                            actual_capture,
                            work,
                        )?)
                    };
                    let rows = if let Some(rows) = &group_rows {
                        rows.get(family_index.map_or(0, |index| index + 1))
                            .ok_or_else(|| super::invalid(entries.body))?
                    } else {
                        legacy_rows
                            .as_ref()
                            .ok_or_else(|| super::invalid(entries.body))?
                    };
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
                    let mut family_clauses = Vec::new();
                    if family_index.is_some() {
                        super::charge(work, actual_clauses.len())?;
                        family_clauses
                            .try_reserve_exact(actual_clauses.len())
                            .map_err(|_| super::resource())?;
                    }
                    for (frozen, actual) in original
                        .original_clause_projections()
                        .iter()
                        .zip(actual_clauses)
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
                        if family_index.is_some() {
                            family_clauses.push(expected);
                        } else {
                            proof.clauses.push(expected);
                        }
                    }
                    if let Some(index) = family_index {
                        let family = &admission.families[index];
                        let (provided, dictionaries) = if let Some(contract) = source_contract {
                            let provided = authenticate_family_header_with_contract(
                                admission,
                                family,
                                copy,
                                self.provider_registry(),
                                &renaming,
                                contract,
                                work,
                            )?;
                            let dictionaries = authenticate_family_dictionaries_with_requirements(
                                admission,
                                family,
                                &entries.families[index],
                                copy,
                                self.provider_registry(),
                                arena,
                                target,
                                &nodes,
                                &renaming,
                                contract.requirements,
                                work,
                            )?;
                            (provided, dictionaries)
                        } else {
                            let provided = authenticate_family_header(
                                admission,
                                family,
                                copy,
                                self.provider_registry(),
                                &renaming,
                                work,
                            )?;
                            let dictionaries = authenticate_family_dictionaries(
                                admission,
                                family,
                                &entries.families[index],
                                copy,
                                self.provider_registry(),
                                arena,
                                target,
                                &nodes,
                                &renaming,
                                work,
                            )?;
                            (provided, dictionaries)
                        };
                        let mut member_nodes = Vec::new();
                        super::charge(work, copy.nodes.len())?;
                        member_nodes
                            .try_reserve_exact(copy.nodes.len())
                            .map_err(|_| super::resource())?;
                        member_nodes.extend(copy.nodes.iter().map(|(_, copied)| *copied));
                        super::charge(work, 1)?;
                        proof.families.push(SpecializedFamily {
                            certificate: std::sync::Arc::new(original.contract_certificate()),
                            header: family.clone_with_budget(work).map_err(|failure| {
                                if failure == BuildError::TypeWorkExceeded {
                                    super::resource()
                                } else {
                                    super::invalid(entries.body)
                                }
                            })?,
                            provided,
                            state: actual_state,
                            handler: actual_handler,
                            clauses: family_clauses,
                            nodes: member_nodes,
                            dictionaries,
                        });
                    }
                    (
                        original.original_program(),
                        original.original_nodes(),
                        family_index.map_or(2, |index| index + 3),
                    )
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
                    for dictionary in original.original_dictionary_parameters() {
                        retain_identity(&mut declarations.binders, dictionary.id(), work)?;
                    }
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
            let phase_seen = if phase < 3 {
                &mut phases[phase]
            } else {
                family_phases
                    .get_mut(phase - 3)
                    .ok_or_else(|| super::invalid(entries.body))?
            };
            if *phase_seen {
                return Err(super::invalid(entries.body));
            }
            *phase_seen = true;
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
            if source_contract.is_some() {
                // Source forests deliberately have no final occurrence or
                // anchor addresses. Canonical original family selection and
                // dictionary routes were checked above from the genuine token.
                if !copy.occurrences.is_empty() || !copy.catalog.is_empty() {
                    return Err(super::invalid(entries.body));
                }
                super::charge(
                    work,
                    copy.original_slots
                        .len()
                        .checked_add(source.method_evidence.occurrences().len())
                        .ok_or_else(super::resource)?,
                )?;
                if copy.original_slots.len() != source.method_evidence.occurrences().len() {
                    return Err(super::invalid(source.root));
                }
                let mut slots = std::collections::HashSet::new();
                slots
                    .try_reserve(copy.original_slots.len())
                    .map_err(|_| super::resource())?;
                for pin in copy.original_slots {
                    if !slots.insert(pin.storage_id())
                        || source
                            .method_evidence
                            .occurrence(pin.storage_id())
                            .is_none()
                    {
                        return Err(super::invalid(source.root));
                    }
                }
            } else {
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
            if let Some(index) = family_index {
                transfer_native_storage_relations(
                    admission, index, copy, arena, target, &nodes, &renaming, &mut proof, work,
                )?;
            }
        }
        if !phases.into_iter().all(|phase| phase) || family_phases.iter().any(|phase| !phase) {
            return Err(super::invalid(entries.body));
        }
        Ok(proof)
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
                TypeStructureNode::Type(Type::Nominal(id) | Type::ForeignOwnerApply(id, _)) => {
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
#[allow(clippy::too_many_arguments)] // Independent source, actual and work authorities stay explicit.
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
            || proof.families.len() != scope.attached.len()
            || proof.families.len() != scope.descriptor.family_members().len()
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
        if !proof.families.is_empty() || !proof.native_storage.is_empty() {
            authenticate_native_storage_relations::<crate::core::EffectOperationFamily>(
                program.arena,
                &program.nodes,
                scope,
                super::row::effect_operation,
                work,
            )?;
            for family in &proof.families {
                family
                    .certificate
                    .authenticate(scope.descriptor.definition(), true, work)?;
                super::charge(work, family.dictionaries.len())?;
                for dictionary in &family.dictionaries {
                    authenticate_dictionary_binding(dictionary, program, work)?;
                }
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
    /// Resolves only a retained original ResourceFamily formal at an exact
    /// copied method anchor. Ordinary Core scope checking establishes domination.
    #[expect(
        clippy::too_many_arguments,
        reason = "copied occurrence and owning scope are independent coordinates"
    )]
    pub(crate) fn family_dictionary_binder(
        &self,
        program: &UnvalidatedEffectProgram,
        scope_node: NodeId,
        scope: &ProviderScopeNode,
        occurrence_node: NodeId,
        definition: crate::resolved::ResourceDefinitionId,
        position: usize,
        work: &mut TypeWorkBudget,
    ) -> Result<Option<crate::resolved::BinderId>, ValidationError> {
        let proof = &self.0;
        if proof.definition != definition {
            return Ok(None);
        }
        super::charge(
            work,
            proof
                .families
                .len()
                .checked_add(proof.anchors.len())
                .ok_or_else(super::resource)?,
        )?;
        let mut selected = None;
        for family in &proof.families {
            super::charge(work, family.nodes.len())?;
            if family.nodes.contains(&occurrence_node) && selected.replace(family).is_some() {
                return Err(super::invalid(occurrence_node));
            }
        }
        let Some(family) = selected else {
            return Ok(None);
        };
        let owner = crate::core::dialect::MethodEvidenceOwner::ResourceFamily(definition);
        let mut matching = false;
        for anchor in &proof.anchors {
            if anchor.node != occurrence_node {
                continue;
            }
            super::charge(work, proof.occurrences.len())?;
            if anchor
                .occurrence
                .and_then(|slot| proof.occurrences.iter().find(|entry| entry.slot == slot))
                .is_some_and(|occurrence| {
                    occurrence.scope == Some(owner) && occurrence.scope_binder.is_none()
                })
            {
                matching = true;
            }
        }
        if !matching {
            return Err(super::invalid(occurrence_node));
        }
        self.authenticate(program, scope_node, scope, work)?;
        let dictionary = family
            .dictionaries
            .get(position)
            .ok_or_else(|| super::invalid(occurrence_node))?;
        if dictionary.requirement.owner()
            != crate::interface::RequirementOwner::ResourceFamily(definition)
            || dictionary.method.interface() != dictionary.producer.interface()
        {
            return Err(super::invalid(occurrence_node));
        }
        authenticate_dictionary_binding(dictionary, program, work)?;
        Ok(Some(dictionary.binder))
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
        let mut families = Vec::new();
        super::charge(
            work,
            old.families
                .len()
                .checked_add(old.native_storage.len())
                .ok_or_else(super::resource)?,
        )?;
        families
            .try_reserve_exact(old.families.len())
            .map_err(|_| super::resource())?;
        for original in &old.families {
            let count = original
                .nodes
                .len()
                .checked_add(original.clauses.len())
                .and_then(|n| n.checked_add(original.dictionaries.len()))
                .ok_or_else(super::resource)?;
            super::charge(work, count)?;
            let mut member_nodes = Vec::new();
            let mut member_clauses = Vec::new();
            let mut dictionaries = Vec::new();
            member_nodes
                .try_reserve_exact(original.nodes.len())
                .map_err(|_| super::resource())?;
            member_clauses
                .try_reserve_exact(original.clauses.len())
                .map_err(|_| super::resource())?;
            dictionaries
                .try_reserve_exact(original.dictionaries.len())
                .map_err(|_| super::resource())?;
            for node in &original.nodes {
                member_nodes.push(mapped(&nodes, *node)?);
            }
            for clause in &original.clauses {
                member_clauses.push(specialize_projection(
                    clause, &nodes, &fresh, &sigma, &renaming, work,
                )?);
            }
            for dictionary in &original.dictionaries {
                dictionaries.push(SpecializedDictionary {
                    requirement: dictionary.requirement,
                    method: dictionary.method,
                    binder: dictionary.binder,
                    producer: dictionary.producer,
                    projection: specialize_projection(
                        &dictionary.projection,
                        &nodes,
                        &fresh,
                        &sigma,
                        &renaming,
                        work,
                    )?,
                    initializer: specialize_projection(
                        &dictionary.initializer,
                        &nodes,
                        &fresh,
                        &sigma,
                        &renaming,
                        work,
                    )?,
                });
            }
            families.push(SpecializedFamily {
                certificate: std::sync::Arc::clone(&original.certificate),
                header: original
                    .header
                    .clone_with_budget(work)
                    .map_err(|_| super::resource())?,
                provided: crate::types::clone_effect_instance_with_budget(&original.provided, work)
                    .map_err(|()| super::resource())?,
                state: specialize_projection(
                    &original.state,
                    &nodes,
                    &fresh,
                    &sigma,
                    &renaming,
                    work,
                )?,
                handler: original.handler,
                clauses: member_clauses,
                nodes: member_nodes,
                dictionaries,
            });
        }
        let mut native_storage = Vec::new();
        native_storage
            .try_reserve_exact(old.native_storage.len())
            .map_err(|_| super::resource())?;
        for original in &old.native_storage {
            native_storage.push(AdmittedNativeStorageRelation {
                request: mapped(&nodes, original.request)?,
                operand: mapped(&nodes, original.operand)?,
                request_projection: specialize_projection(
                    &original.request_projection,
                    &nodes,
                    &fresh,
                    &sigma,
                    &renaming,
                    work,
                )?,
                operand_projection: specialize_projection(
                    &original.operand_projection,
                    &nodes,
                    &fresh,
                    &sigma,
                    &renaming,
                    work,
                )?,
                operation: original.operation,
                effect: crate::types::clone_effect_instance_with_budget(&original.effect, work)
                    .map_err(|()| super::resource())?,
                owner: original.owner,
                family: original.family,
                member: original.member,
                result: original.result,
            });
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
            families,
            native_storage,
            native: old.native.as_ref().map(std::sync::Arc::clone),
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
            E::Operation(O::SourceCopyWindow(scope)) => {
                self.variable(scope.identity(), &crate::types::Kind::Type, work)?;
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
        self.foralls_view(metadata.view(), sigma, work)
    }
    fn foralls_view(
        &mut self,
        metadata: super::projection::MetadataView<'_>,
        sigma: &ProviderTemplateSubstitution<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        let mut visit = |node: crate::types::TypeStructureNode<'_>, work: &mut TypeWorkBudget| {
            self.forall_structure(node, sigma, work)
        };
        match metadata {
            super::projection::MetadataView::Type(ty) => {
                crate::types::visit_type_structure_with_budget(ty, work, &mut visit)
                    .map_err(|()| super::resource())?;
            }
            super::projection::MetadataView::Argument(argument) => {
                crate::types::visit_argument_structure_with_budget(argument, work, &mut visit)
                    .map_err(|()| super::resource())?;
            }
            super::projection::MetadataView::Row(row) => {
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
            super::projection::MetadataView::Kind(_) => {}
        }
        Ok(())
    }
    fn forall_structure(
        &mut self,
        node: crate::types::TypeStructureNode<'_>,
        sigma: &ProviderTemplateSubstitution<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ()> {
        use crate::types::{Type, TypeStructureNode, TypeVariableId};
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
    }
    fn type_foralls(
        &mut self,
        ty: &crate::types::Type,
        sigma: &ProviderTemplateSubstitution<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        crate::types::visit_type_structure_with_budget(ty, work, |node, work| {
            self.forall_structure(node, sigma, work)
        })
        .map_err(|()| super::resource())?;
        Ok(())
    }
    fn pattern_foralls(
        &mut self,
        root: &crate::core::CorePattern,
        sigma: &ProviderTemplateSubstitution<'_>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), ValidationError> {
        use crate::core::CorePatternKind;
        super::charge(work, 1)?;
        let mut pending = Vec::new();
        pending.try_reserve(1).map_err(|_| super::resource())?;
        pending.push(root);
        while let Some(pattern) = pending.pop() {
            super::charge(work, 1)?;
            self.type_foralls(&pattern.ty, sigma, work)?;
            match &pattern.kind {
                CorePatternKind::Binder(binder) => self.type_foralls(binder.ty(), sigma, work)?,
                CorePatternKind::Tuple(fields) => {
                    super::charge(work, fields.len())?;
                    pending
                        .try_reserve(fields.len())
                        .map_err(|_| super::resource())?;
                    pending.extend(fields.iter().rev());
                }
                CorePatternKind::Constructor {
                    payload: Some(payload),
                    ..
                } => {
                    super::charge(work, 1)?;
                    pending.try_reserve(1).map_err(|_| super::resource())?;
                    pending.push(payload);
                }
                _ => {}
            }
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
/// One invocation's exact original forest. No checked result escapes this
/// representation owner or transfers between programs, phases or contexts.
pub(in crate::core) struct SourceResourceOriginalForest<'a> {
    pub(in crate::core) inventory: ProviderLocalInventory,
    pub(in crate::core) projections:
        std::collections::HashMap<NodeId, super::projection::BorrowedNodeProjection<'a>>,
}

/// Original source-resource forest declarations, without an experimental
/// provider certificate. Extra wrapper metadata is retained explicitly.
pub(in crate::core) fn source_resource_original_forest<'a>(
    program: &'a UnvalidatedEffectProgram,
    roots: &[NodeId],
    extra_binders: &[&crate::core::TypedBinder],
    extra_patterns: &[&crate::core::CorePattern],
    extra_handler: Option<&crate::core::HandlerNode>,
    sigma: &ProviderTemplateSubstitution<'_>,
    work: &mut TypeWorkBudget,
) -> Result<SourceResourceOriginalForest<'a>, ValidationError> {
    let order = crate::core::transform::provider_entry_forest_order(
        program,
        roots,
        &std::collections::HashSet::new(),
        work,
    )
    .map_err(|_| super::resource())?;
    let mut declarations = LocalDeclarations::default();
    // This map exists only for this invocation and exact original forest. It
    // retains representation already paid by project(), never a validation or
    // specialization result. Target projections and comparisons remain fresh.
    super::charge(work, order.len())?;
    let mut projections = std::collections::HashMap::new();
    projections
        .try_reserve(order.len())
        .map_err(|_| super::resource())?;
    for id in order {
        let stored = super::node(program, id)?;
        declarations.node(stored, work)?;
        let projection = super::projection::project_borrowed(id, stored, work)?;
        for metadata in &projection.metadata {
            declarations.foralls_view(*metadata, sigma, work)?;
        }
        if projections.insert(id, projection).is_some() {
            return Err(super::invalid(id));
        }
    }
    for binder in extra_binders {
        retain_identity(&mut declarations.binders, binder.id(), work)?;
        declarations.type_foralls(binder.ty(), sigma, work)?;
    }
    for pattern in extra_patterns {
        declarations.pattern(pattern, work)?;
        declarations.pattern_foralls(pattern, sigma, work)?;
    }
    if let Some(handler) = extra_handler {
        retain_identity(&mut declarations.handlers, handler.id(), work)?;
        for clause in handler.clauses() {
            retain_identity(&mut declarations.resumes, clause.resume(), work)?;
            declarations.pattern(clause.pattern(), work)?;
            declarations.pattern_foralls(clause.pattern(), sigma, work)?;
        }
        for argument in handler.effect().arguments() {
            crate::types::visit_argument_structure_with_budget(argument, work, |node, work| {
                declarations.forall_structure(node, sigma, work)
            })
            .map_err(|()| super::resource())?;
        }
    }
    if !program.method_evidence.lexical_owners().is_empty() {
        return Err(super::invalid(program.root));
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
    let inventory = ProviderLocalInventory {
        binders: array(declarations.binders, work)?,
        types: types.into_boxed_slice(),
        handlers: array(declarations.handlers, work)?,
        resumes: array(declarations.resumes, work)?,
        nominals: array(declarations.nominals, work)?,
        lexicals: Box::new([]),
    };
    Ok(SourceResourceOriginalForest {
        inventory,
        projections,
    })
}
/// Original source-resource forest declarations, without an experimental
/// provider certificate. Extra wrapper metadata is retained explicitly.
pub(crate) fn source_resource_local_identities(
    program: &UnvalidatedEffectProgram,
    roots: &[NodeId],
    extra_binders: &[&crate::core::TypedBinder],
    extra_patterns: &[&crate::core::CorePattern],
    extra_handler: Option<&crate::core::HandlerNode>,
    sigma: &ProviderTemplateSubstitution<'_>,
    work: &mut TypeWorkBudget,
) -> Result<ProviderLocalInventory, ValidationError> {
    Ok(source_resource_original_forest(
        program,
        roots,
        extra_binders,
        extra_patterns,
        extra_handler,
        sigma,
        work,
    )?
    .inventory)
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
                for dictionary in original.original_dictionary_parameters() {
                    retain_identity(&mut declarations.binders, dictionary.id(), work)?;
                }
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
        foreign::{ForeignRegistrations, provider_manifest, sqlite_manifest, typed_arena_manifest},
        interface::InterfaceConstraintBudget,
        module::{ForeignRegistrationId, ModuleGraph, ModuleRoots, load_module_graph},
        pattern::UsefulnessBudget,
        resolve::{DependencyExports, resolve_module_with_budget},
        resolved::CheckedModule,
        types::{Type, clone_effect_instance_with_budget, clone_kinded_arguments_with_budget},
    };
    use std::{path::PathBuf, sync::Arc};

    #[test]
    fn deferred_source_rows_require_unique_variables_complete_original_domains_and_exact_work() {
        use crate::types::{EffectRow, EffectRowVariable, InferenceVariableId};
        let arena = crate::core::dialect::ArenaId::new(1);
        let pending = InferenceVariableId::new(0);
        let node = NodeId::new(arena, 0);
        let handler = crate::core::HandlerId::new(0);
        let make = |work: &mut TypeWorkBudget| {
            let mut next = 100;
            DeferredProviderHandlerRows::from_domain(
                arena,
                &[pending],
                &[node],
                &[handler],
                || {
                    let row = EffectRow::open(
                        EffectRowVariable::Inference(InferenceVariableId::new(next)),
                        Box::new([]),
                    );
                    next += 1;
                    Some(row)
                },
                work,
            )
        };
        let mut measured = TypeWorkBudget::unbounded();
        let deferred = make(&mut measured).unwrap();
        assert_eq!(deferred.bindings.len(), 5);
        let cost = measured.used();
        for prefix in [0, 13] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert!(make(&mut short).is_err());
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                make(&mut exact).unwrap();
                assert_eq!(exact.used(), prefix + cost);
            }
        }
        for malformed in 0..2 {
            let result = DeferredProviderHandlerRows::from_domain(
                arena,
                &[pending],
                &[node],
                &[handler],
                || {
                    Some(if malformed == 0 {
                        EffectRow::empty()
                    } else {
                        EffectRow::open(
                            EffectRowVariable::Inference(InferenceVariableId::new(100)),
                            Box::new([]),
                        )
                    })
                },
                &mut TypeWorkBudget::unbounded(),
            );
            assert!(
                result.is_err(),
                "closed or duplicate source variable {malformed}"
            );
        }
        let module = crate::module::ModuleId::new(0);
        let template = crate::resolved::ProviderTemplateId::new(
            crate::resolved::ResourceDefinitionId::new(module, 0),
            2,
        );
        let actual = || ResolvedProviderHandlerRows {
            original_arena: arena,
            direct: EffectRow::empty(),
            epsilon: EffectRow::empty(),
            output: EffectRow::empty(),
            residual: EffectRow::empty(),
            pending: std::collections::HashMap::from([(pending, EffectRow::empty())]),
            node_rows: std::collections::HashMap::from([(node, EffectRow::empty())]),
            handler_outputs: std::collections::HashMap::from([(handler, EffectRow::empty())]),
            captures: crate::core::capture::ActualCaptureInputs::empty(template),
        };
        let complete = actual();
        let mut measured = TypeWorkBudget::unbounded();
        let equations = deferred.completion(&complete, &mut measured).unwrap();
        assert_eq!(equations.len(), 5);
        assert!(equations.iter().all(|(_, _, row)| row.is_empty()));
        let cost = measured.used();
        for prefix in [0, 13] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert!(deferred.completion(&complete, &mut short).is_err());
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            deferred.completion(&complete, &mut exact).unwrap();
            assert_eq!(exact.used(), prefix + cost);
        }
        for mutation in 0..6 {
            let mut candidate = actual();
            match mutation {
                0 => candidate.original_arena = crate::core::dialect::ArenaId::new(2),
                1 => {
                    candidate.pending = std::collections::HashMap::from([(
                        InferenceVariableId::new(1),
                        EffectRow::empty(),
                    )])
                }
                2 => {
                    candidate.node_rows = std::collections::HashMap::from([(
                        NodeId::new(arena, 1),
                        EffectRow::empty(),
                    )])
                }
                3 => {
                    candidate.handler_outputs = std::collections::HashMap::from([(
                        crate::core::HandlerId::new(1),
                        EffectRow::empty(),
                    )])
                }
                4 => {
                    candidate
                        .node_rows
                        .insert(NodeId::new(arena, 1), EffectRow::empty());
                }
                _ => candidate.pending.clear(),
            }
            assert!(
                deferred
                    .completion(&candidate, &mut TypeWorkBudget::unbounded())
                    .is_err(),
                "mutation {mutation}"
            );
        }
    }

    #[test]
    fn actual_source_final_solved_rows_require_original_domains_and_exact_budget() {
        use crate::types::{EffectId, EffectInstance, EffectRow, InferenceVariableId};
        let module = crate::module::ModuleId::new(0);
        let arena = crate::core::dialect::ArenaId::new(1);
        let template = crate::resolved::ProviderTemplateId::new(
            crate::resolved::ResourceDefinitionId::new(module, 0),
            2,
        );
        let h =
            || EffectRow::singleton(EffectInstance::new(EffectId::new(module, 0), Box::new([])));
        let rows = || ResolvedProviderHandlerRows {
            original_arena: arena,
            direct: h(),
            epsilon: EffectRow::empty(),
            output: h(),
            residual: h(),
            pending: std::collections::HashMap::from([(
                InferenceVariableId::new(0),
                EffectRow::empty(),
            )]),
            node_rows: std::collections::HashMap::from([(NodeId::new(arena, 0), h())]),
            handler_outputs: std::collections::HashMap::from([(
                crate::core::HandlerId::new(0),
                h(),
            )]),
            captures: crate::core::capture::ActualCaptureInputs::empty(template),
        };
        let expected = rows();
        for mutation in 0..14 {
            let mut actual = rows();
            match mutation {
                0 => actual.original_arena = crate::core::dialect::ArenaId::new(2),
                1 => actual.direct = EffectRow::empty(),
                2 => actual.epsilon = h(),
                3 => actual.output = EffectRow::empty(),
                4 => actual.residual = EffectRow::empty(),
                5 => {
                    actual.pending = std::collections::HashMap::from([(
                        InferenceVariableId::new(1),
                        EffectRow::empty(),
                    )])
                }
                6 => {
                    actual.node_rows =
                        std::collections::HashMap::from([(NodeId::new(arena, 1), h())])
                }
                7 => {
                    actual.handler_outputs =
                        std::collections::HashMap::from([(crate::core::HandlerId::new(1), h())])
                }
                8 => actual.pending.clear(),
                9 => {
                    actual.node_rows.insert(NodeId::new(arena, 1), h());
                }
                10 => {
                    actual.pending =
                        std::collections::HashMap::from([(InferenceVariableId::new(0), h())])
                }
                11 => {
                    actual.node_rows = std::collections::HashMap::from([(
                        NodeId::new(arena, 0),
                        EffectRow::empty(),
                    )])
                }
                12 => {
                    actual.handler_outputs = std::collections::HashMap::from([(
                        crate::core::HandlerId::new(0),
                        EffectRow::empty(),
                    )])
                }
                _ => actual.handler_outputs.clear(),
            }
            assert!(
                !expected
                    .same_actual_captures(&actual, &mut TypeWorkBudget::unbounded())
                    .unwrap(),
                "mutation {mutation}"
            );
        }
        let equal = rows();
        let mut measured = TypeWorkBudget::unbounded();
        assert!(
            expected
                .same_actual_captures(&equal, &mut measured)
                .unwrap()
        );
        let cost = measured.used();
        for prefix in [0, 13] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                expected
                    .same_actual_captures(&equal, &mut short)
                    .unwrap_err()
                    .reason(),
                crate::core::ValidationReason::Resource
            );
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                assert!(expected.same_actual_captures(&equal, &mut exact).unwrap());
                assert_eq!(exact.used(), prefix + cost);
            }
        }
    }

    fn sqlite_scopes() -> (ModuleGraph, ValidatedEffectProgram) {
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/provider-experiments/sqlite-copying/simultaneous-entry.ash");
        checked_provider_scopes(entry)
    }

    fn checked_provider_scopes(entry: PathBuf) -> (ModuleGraph, ValidatedEffectProgram) {
        let roots = ModuleRoots::empty().with_foreign_registrations(
            ForeignRegistrations::new([
                provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
                sqlite_manifest(ForeignRegistrationId::new(2)).unwrap(),
            ])
            .unwrap(),
        );
        checked_provider_scopes_with_roots(entry, roots)
    }

    fn checked_arena_scopes(entry: PathBuf) -> (ModuleGraph, ValidatedEffectProgram) {
        let roots = ModuleRoots::empty().with_foreign_registrations(
            ForeignRegistrations::new([
                provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
                typed_arena_manifest(ForeignRegistrationId::new(2)).unwrap(),
            ])
            .unwrap(),
        );
        checked_provider_scopes_with_roots(entry, roots)
    }

    fn checked_source_provider_scopes_with_roots(
        entry: PathBuf,
        roots: ModuleRoots,
        source_capture_observer: Option<fn(&crate::core::EffectCoreBuilder)>,
    ) -> (ModuleGraph, Vec<CheckedModule>) {
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
            let module = if loaded.id() == graph.entry() {
                if let Some(observer) = source_capture_observer {
                    crate::elaborate::check_effect_module_with_source_capture_for_test(
                        resolved,
                        &availability,
                        &mut checking,
                        &mut coverage,
                        &mut constraints,
                        observer,
                    )
                } else {
                    check_module_with_budget_and_provider_codes(
                        resolved,
                        &availability,
                        &mut checking,
                        &mut coverage,
                        &mut constraints,
                    )
                }
            } else {
                check_module_with_budget_and_provider_codes(
                    resolved,
                    &availability,
                    &mut checking,
                    &mut coverage,
                    &mut constraints,
                )
            }
            .expect(
                "the untouched source fixture must check through the genuine provider pipeline",
            );
            if let Some(code) = module.provider_code() {
                availability
                    .retain(module.module(), code, &mut checking)
                    .unwrap();
            }
            checked.push(module);
        }
        (graph, checked)
    }

    fn checked_provider_scopes_with_roots(
        entry: PathBuf,
        roots: ModuleRoots,
    ) -> (ModuleGraph, ValidatedEffectProgram) {
        let (graph, checked) = checked_source_provider_scopes_with_roots(entry, roots, None);
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
        let program = validate_effect_modules(unchecked, &sources, &relation)
            .expect("the untouched source fixture must compile and independently validate first");
        (graph, program)
    }

    #[test]
    fn arena_source_capture_receipt_is_exact_budgeted_and_not_executable() {
        fn scope_at(
            nodes: &[crate::core::dialect::StoredNode<crate::core::EffectOperationFamily>],
            ordinal: usize,
        ) -> &ProviderScopeNode {
            let EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) =
                &nodes[ordinal].kind
            else {
                panic!("the fixture's real source ProviderScope must remain present");
            };
            scope
        }
        fn observe(builder: &crate::core::EffectCoreBuilder) {
            use crate::{
                core::{EffectOperationFamily, PureComputation, TupleNode, dialect::StoredNode},
                source::Origin,
                types::{InferenceVariableId, Type},
            };
            let (arena, nodes, _) = builder.provider_projection_parts().unwrap();
            let scope_ordinal = nodes
                .iter()
                .position(|node| {
                    matches!(&node.kind,
                EffectExprKind::Operation(EffectOperation::ProviderScope(scope))
                    if scope.member_count() > 1 && scope.descriptor.prepared_capture().is_some())
                })
                .expect("actual ModuleCheck must mint a genuine finite-family source receipt");
            let scope = scope_at(nodes, scope_ordinal);
            let proof = &scope.descriptor.prepared_capture().unwrap().0;
            let operation = super::super::row::effect_operation;
            let mut measured = TypeWorkBudget::unbounded();
            let view = authenticate_prepared_provider_capture(
                arena,
                nodes,
                scope,
                operation,
                &mut measured,
            )
            .expect("the untouched post-zonk copied source forest must authenticate first");
            let cost = measured.used();
            assert!(cost > 0);
            assert!(view.authenticates_scope(nodes, scope));
            assert!(
                !view.native_storage_relations().is_empty(),
                "the genuine fixture must retain actual Store/Load flow receipts"
            );
            let dictionary = proof
                .families
                .iter()
                .flat_map(|family| &family.dictionaries)
                .next()
                .expect("the real source family has its canonical Layout initializer");
            let initializer = dictionary.initializer.node.index().unwrap();
            assert!(
                view.authenticates_layout(
                    nodes,
                    initializer,
                    dictionary.producer,
                    &mut TypeWorkBudget::unbounded()
                )
                .unwrap()
            );
            let clone_nodes = || {
                nodes
                    .iter()
                    .map(|node| StoredNode::<EffectOperationFamily> {
                        dialect: node.dialect,
                        ty: node.ty.clone(),
                        effects: node.effects.clone(),
                        origin: node.origin.clone(),
                        kind: node.kind.clone(),
                    })
                    .collect::<Vec<_>>()
            };
            let identical = clone_nodes();
            assert!(!view.authenticates_scope(&identical, scope_at(&identical, scope_ordinal)));
            assert!(
                !view
                    .authenticates_layout(
                        &identical,
                        initializer,
                        dictionary.producer,
                        &mut TypeWorkBudget::unbounded()
                    )
                    .unwrap(),
                "a cloned slice is not this view's arena"
            );
            let other_scope = scope.clone();
            assert!(
                !view.authenticates_scope(nodes, &other_scope),
                "an identical separately allocated scope is not this view's scope"
            );
            let other_ordinal = (0..nodes.len())
                .find(|index| {
                    *index != initializer
                        && proof
                            .families
                            .iter()
                            .flat_map(|family| &family.dictionaries)
                            .all(|dictionary| {
                                dictionary.initializer.node.index().unwrap() != *index
                            })
                })
                .unwrap();
            assert!(
                !view
                    .authenticates_layout(
                        nodes,
                        other_ordinal,
                        dictionary.producer,
                        &mut TypeWorkBudget::unbounded()
                    )
                    .unwrap()
            );
            assert!(
                !view
                    .authenticates_layout(
                        nodes,
                        nodes.len(),
                        dictionary.producer,
                        &mut TypeWorkBudget::unbounded()
                    )
                    .unwrap()
            );
            let native = proof.native.as_ref().unwrap();
            let layout = native.layout.as_ref().unwrap();
            let other_payload = if dictionary.producer.payload_type() == Type::Bool {
                Type::Int
            } else {
                Type::Bool
            };
            let other_producer = layout
                .dictionary_for_payload(&other_payload)
                .unwrap()
                .producer();
            assert_ne!(other_producer, dictionary.producer);
            assert!(
                !view
                    .authenticates_layout(
                        nodes,
                        initializer,
                        other_producer,
                        &mut TypeWorkBudget::unbounded()
                    )
                    .unwrap(),
                "another genuine dictionary is not this initializer's producer"
            );
            for prefix in [0usize, 17] {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                authenticate_prepared_provider_capture(arena, nodes, scope, operation, &mut exact)
                    .expect("the measured source receipt charge must fit exactly");
                assert_eq!(exact.used(), prefix + cost);
                let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
                short.charge(prefix).unwrap();
                let error = authenticate_prepared_provider_capture(
                    arena, nodes, scope, operation, &mut short,
                )
                .err()
                .expect("one unit short must refuse without a source authority view");
                assert_eq!(error.reason(), crate::core::ValidationReason::Resource);
                assert!(short.used() < prefix + cost);
            }
            assert!(scope.descriptor.specialization().is_none());
            assert!(scope.descriptor.admitted_arc().is_none());
            let failure = authenticate_native_storage_relations(
                arena,
                nodes,
                scope,
                operation,
                &mut TypeWorkBudget::unbounded(),
            )
            .expect_err(
                "source flow authority must not satisfy the final admitted relation consumer",
            );
            assert_eq!(
                failure.reason(),
                crate::core::ValidationReason::ResourceEscape
            );
            assert_eq!(failure.node(), Some(scope.handler.body()));

            let mut work = TypeWorkBudget::unbounded();
            let registry = builder.provider_registry();
            let definition = Arc::clone(
                scope
                    .descriptor
                    .prepared_definition_for_test()
                    .expect("the source descriptor retains its genuine original definition Arc"),
            );
            let native = registry
                .foreign_modules()
                .find(|fact| std::ptr::eq(fact.as_ref(), scope.descriptor.native()))
                .unwrap();
            let mut families = Vec::new();
            for family in scope.descriptor.family_members() {
                families.push(family.clone_with_budget(&mut work).unwrap());
            }
            let metadata = ProviderScopeAdmission {
                definition,
                native: Arc::clone(native),
                arguments: clone_kinded_arguments_with_budget(
                    scope.descriptor.arguments().iter(),
                    &mut work,
                )
                .unwrap(),
                identity: scope.descriptor.identity(),
                retained: scope.descriptor.retained().to_vec().into_boxed_slice(),
                native_effect: clone_effect_instance_with_budget(
                    scope.descriptor.native_effect(),
                    &mut work,
                )
                .unwrap(),
                protocol: scope.descriptor.protocol(),
                families: families.into_boxed_slice(),
            };
            let mut metadata_only = scope.clone();
            metadata_only.descriptor =
                super::super::ProviderScopeAuthority::prepared(metadata, &mut work).unwrap();
            let failure = authenticate_prepared_provider_capture(arena, nodes, &metadata_only, operation, &mut work)
                .err().expect("matching metadata without the privately minted copied-flow receipt has no authority");
            assert_eq!(
                failure.reason(),
                crate::core::ValidationReason::ResourceEscape
            );
            assert_eq!(failure.node(), Some(scope.handler.body()));

            let operand = view
                .native_storage_relations()
                .iter()
                .find_map(|relation| {
                    matches!(
                        relation.result(),
                        super::super::HandlerNativeStorageResult::Store { .. }
                    )
                    .then_some(relation.operand)
                })
                .expect("the source fixture contains a real native Store operand");
            for mutation in 0..4 {
                let mut changed = clone_nodes();
                authenticate_prepared_provider_capture(arena, &changed, scope_at(&changed, scope_ordinal),
                    operation, &mut TypeWorkBudget::unbounded())
                    .expect("each mutation begins from an independently reauthenticated identical source graph");
                let target = if mutation == 1 {
                    initializer
                } else {
                    operand.index().unwrap()
                };
                match mutation {
                    0 => {
                        let EffectExprKind::Pure(PureExprKind::Computation(
                            PureComputation::Tuple(tuple),
                        )) = &changed[target].kind
                        else {
                            panic!("the actual native Store operand must be its source tuple");
                        };
                        let mut elements = tuple.elements().to_vec();
                        assert_eq!(elements.len(), 4);
                        assert_ne!(elements[2], elements[3]);
                        assert_eq!(changed[elements[2].index().unwrap()].ty, Type::Int);
                        assert_eq!(changed[elements[3].index().unwrap()].ty, Type::Int);
                        elements.swap(2, 3);
                        changed[target].kind = EffectExprKind::Pure(PureExprKind::Computation(
                            PureComputation::Tuple(TupleNode::new(elements)),
                        ));
                    }
                    1 => {
                        changed[target].kind = EffectExprKind::Pure(PureExprKind::Value(
                            PureValue::Intrinsic(crate::core::packed::IntrinsicNode::new(
                                crate::core::packed::Intrinsic::ForeignLayoutWitness {
                                    producer: other_producer,
                                },
                                other_producer.interface().module(),
                            )),
                        ))
                    }
                    2 => {
                        let original = changed[target].origin.take().unwrap();
                        let span = original.primary_span();
                        changed[target].origin = Some(Origin::Related {
                            primary: Box::new(original),
                            related: vec![span],
                        });
                    }
                    3 => changed[target].ty = Type::Inference(InferenceVariableId::new(0)),
                    _ => unreachable!(),
                }
                let error = authenticate_prepared_provider_capture(arena, &changed, scope_at(&changed, scope_ordinal),
                    operation, &mut TypeWorkBudget::unbounded()).err()
                    .expect("copied edge, dictionary, richer origin or inference mutation must invalidate the source receipt");
                assert_eq!(
                    error.reason(),
                    crate::core::ValidationReason::ResourceEscape
                );
                assert_eq!(
                    error.node(),
                    Some(NodeId::new(arena, u32::try_from(target).unwrap()))
                );
            }
        }
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/provider-experiments/arena-typed/allocation-entry.ash");
        let roots = ModuleRoots::empty().with_foreign_registrations(
            ForeignRegistrations::new([
                provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
                typed_arena_manifest(ForeignRegistrationId::new(2)).unwrap(),
            ])
            .unwrap(),
        );
        let (graph, checked) =
            checked_source_provider_scopes_with_roots(entry, roots, Some(observe));
        assert_eq!(checked.last().unwrap().module(), graph.entry());
        // This regression ends at genuine source checking. Independent final
        // evidence/Core admission and actual execution remain separate gates.
    }

    #[test]
    fn attached_arena_cleanup_rows_restore_both_caches_and_retry_exactly() {
        fn observe(builder: &crate::core::EffectCoreBuilder) {
            use crate::{
                core::{BuildError, EffectCoreBuilder, EffectOperationFamily, dialect::StoredNode},
                types::EffectRow,
            };
            fn rows(builder: &EffectCoreBuilder) -> Vec<(EffectRow, Option<EffectRow>)> {
                builder
                    .nodes
                    .iter()
                    .map(|node| {
                        let output = match &node.kind {
                            EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) => {
                                Some(scope.handler_output.effects().clone())
                            }
                            _ => None,
                        };
                        (node.effects.clone(), output)
                    })
                    .collect()
            }

            let (arena, nodes, _) = builder.provider_projection_parts().unwrap();
            let ordinal = nodes
                .iter()
                .position(|node| {
                    matches!(&node.kind,
                        EffectExprKind::Operation(EffectOperation::ProviderScope(scope))
                            if scope.member_count() > 1
                                && scope.descriptor.prepared_capture().is_some())
                })
                .expect("actual source checking must prepare an attached arena group first");
            let EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) =
                &nodes[ordinal].kind
            else {
                unreachable!();
            };
            let view = authenticate_prepared_provider_capture(
                arena,
                nodes,
                scope,
                super::super::row::effect_operation,
                &mut TypeWorkBudget::unbounded(),
            )
            .expect("the untouched genuine source group must authenticate first");
            assert!(view.authenticates_scope(nodes, scope));
            assert!(!view.native_storage_relations().is_empty());
            let stale = EffectRow::singleton(scope.handler.effect().clone());
            assert_ne!(nodes[ordinal].effects, stale);
            assert_ne!(*scope.handler_output.effects(), stale);

            // Copy genuine source nodes only for the production row replayer.
            // This scratch builder is never finished or offered for admission;
            // no prepared receipt is minted or reauthenticated after mutation.
            let replay = |seed_stale: bool| {
                let mut replay = EffectCoreBuilder::with_effect_registry(Arc::new(
                    builder.provider_registry().clone(),
                ));
                replay.nodes = nodes
                    .iter()
                    .map(|node| StoredNode::<EffectOperationFamily> {
                        dialect: node.dialect,
                        ty: node.ty.clone(),
                        effects: node.effects.clone(),
                        origin: node.origin.clone(),
                        kind: node.kind.clone(),
                    })
                    .collect();
                replay.type_work = TypeWorkBudget::unbounded();
                if seed_stale {
                    replay.nodes[ordinal].effects = stale.clone();
                    let EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) =
                        &mut replay.nodes[ordinal].kind
                    else {
                        unreachable!();
                    };
                    scope.handler_output.effects = stale.clone();
                }
                replay
            };
            let mut untouched = replay(false);
            untouched
                .finish_cleanup_effect_rows()
                .expect("the untouched completed source forest must replay successfully first");
            let expected = rows(&untouched);
            assert_eq!(expected, rows(builder));

            let mut measured = replay(true);
            measured
                .finish_cleanup_effect_rows()
                .expect("stale attached-group row caches must recompute successfully first");
            let work = measured.type_work.used();
            assert!(work > 0);
            assert_eq!(rows(&measured), expected);
            assert_ne!(measured.nodes[ordinal].effects, stale);
            let EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) =
                &measured.nodes[ordinal].kind
            else {
                unreachable!();
            };
            assert_ne!(*scope.handler_output.effects(), stale);

            let mut retry = replay(true);
            let previous = rows(&retry);
            retry.type_work = TypeWorkBudget::with_limit(work - 1);
            assert_eq!(
                retry.finish_cleanup_effect_rows(),
                Err(BuildError::TypeWorkExceeded)
            );
            assert_eq!(rows(&retry), previous, "both row caches must roll back");
            assert!(retry.type_work.used() < work);

            // Retry the same restored forest with an exact remaining allowance.
            let prefix = 17;
            retry.type_work = TypeWorkBudget::with_limit(prefix + work);
            retry.type_work.charge(prefix).unwrap();
            retry.finish_cleanup_effect_rows().unwrap();
            assert_eq!(retry.type_work.used(), prefix + work);
            assert_eq!(rows(&retry), expected);
        }

        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/provider-experiments/arena-typed/allocation-entry.ash");
        let roots = ModuleRoots::empty().with_foreign_registrations(
            ForeignRegistrations::new([
                provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
                typed_arena_manifest(ForeignRegistrationId::new(2)).unwrap(),
            ])
            .unwrap(),
        );
        let (graph, checked) =
            checked_source_provider_scopes_with_roots(entry, roots, Some(observe));
        assert_eq!(checked.last().unwrap().module(), graph.entry());
    }

    #[test]
    fn admitted_arena_source_capture_view_is_exact_and_budgeted() {
        use crate::core::{EffectOperationFamily, PureComputation, TupleNode, dialect::StoredNode};
        fn scope_at(
            nodes: &[StoredNode<EffectOperationFamily>],
            ordinal: usize,
        ) -> &ProviderScopeNode {
            let EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) =
                &nodes[ordinal].kind
            else {
                panic!("the genuine admitted arena scope must remain present");
            };
            scope
        }
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/provider-experiments/arena-typed/allocation-entry.ash");
        let (_, program) = checked_arena_scopes(entry);
        // This fixture has already passed independent Core validation. The
        // identity traversal retains its genuine relocated specialization.
        let original = identity_effect_traversal(&program).unwrap();
        let nodes = &original.nodes;
        let ordinal = nodes
            .iter()
            .position(|node| {
                matches!(&node.kind,
            EffectExprKind::Operation(EffectOperation::ProviderScope(scope))
                if scope.member_count() > 1 && scope.descriptor.admitted_arc().is_some())
            })
            .expect("the fixture must have a genuine admitted family group");
        let scope = scope_at(nodes, ordinal);
        let proof = &scope.descriptor.specialization().unwrap().0;
        let dictionary = proof
            .families
            .iter()
            .flat_map(|family| &family.dictionaries)
            .next()
            .unwrap();
        let initializer = dictionary.initializer.node.index().unwrap();
        let operand = proof
            .native_storage
            .iter()
            .find_map(|receipt| {
                matches!(
                    receipt.result,
                    super::super::HandlerNativeStorageResult::Store { .. }
                )
                .then_some(receipt.operand)
            })
            .expect("the fixture must retain a native Store receipt");
        let operation = super::super::row::effect_operation;
        let mut measured = TypeWorkBudget::unbounded();
        let admitted = authenticate_admitted_provider_capture(
            original.arena,
            nodes,
            scope,
            operation,
            &mut measured,
        )
        .expect("the untouched admitted source view must authenticate first");
        let cost = measured.used();
        assert!(cost > 0);
        let view = AuthenticatedProviderSourceCapture::Admitted(admitted);
        assert!(view.authenticates_scope(nodes, scope));
        assert!(!view.native_storage_relations().is_empty());
        assert!(
            view.authenticates_layout(
                nodes,
                initializer,
                dictionary.producer,
                &mut TypeWorkBudget::unbounded()
            )
            .unwrap()
        );
        for prefix in [0, 17] {
            let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
            short.charge(prefix).unwrap();
            let failure = authenticate_admitted_provider_capture(
                original.arena,
                nodes,
                scope,
                operation,
                &mut short,
            )
            .err()
            .expect("one unit short must not return an admitted source view");
            assert_eq!(failure.reason(), crate::core::ValidationReason::Resource);
            assert!(short.used() < prefix + cost);
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                authenticate_admitted_provider_capture(
                    original.arena,
                    nodes,
                    scope,
                    operation,
                    &mut exact,
                )
                .expect("the same immutable arena must retry with its exact measured allowance");
                assert_eq!(exact.used(), prefix + cost);
            }
        }
        let clone_nodes = || {
            nodes
                .iter()
                .map(|node| StoredNode::<EffectOperationFamily> {
                    dialect: node.dialect,
                    ty: node.ty.clone(),
                    effects: node.effects.clone(),
                    origin: node.origin.clone(),
                    kind: node.kind.clone(),
                })
                .collect::<Vec<_>>()
        };
        let identical = clone_nodes();
        assert!(!view.authenticates_scope(&identical, scope_at(&identical, ordinal)));
        assert!(
            !view
                .authenticates_layout(
                    &identical,
                    initializer,
                    dictionary.producer,
                    &mut TypeWorkBudget::unbounded()
                )
                .unwrap(),
            "equal copied nodes are a different slice"
        );
        let other_scope = scope.clone();
        assert!(
            !view.authenticates_scope(nodes, &other_scope),
            "an equal separately allocated scope is not this view's scope"
        );

        for change_dictionary in [true, false] {
            let mut changed = clone_nodes();
            authenticate_admitted_provider_capture(
                original.arena,
                &changed,
                scope_at(&changed, ordinal),
                operation,
                &mut TypeWorkBudget::unbounded(),
            )
            .expect("each copied graph must authenticate before its mutation");
            let target = if change_dictionary {
                initializer
            } else {
                operand.index().unwrap()
            };
            if change_dictionary {
                assert_ne!(changed[target].ty, Type::Bool);
                changed[target].ty = Type::Bool;
            } else {
                let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Tuple(tuple))) =
                    &changed[target].kind
                else {
                    panic!("the native Store operand must remain a tuple");
                };
                let mut elements = tuple.elements().to_vec();
                assert_eq!(elements.len(), 4);
                assert_ne!(elements[2], elements[3]);
                for child in &elements[2..] {
                    assert_eq!(changed[child.index().unwrap()].ty, Type::Int);
                    assert!(changed[child.index().unwrap()].effects.is_empty());
                }
                elements.swap(2, 3);
                changed[target].kind = EffectExprKind::Pure(PureExprKind::Computation(
                    PureComputation::Tuple(TupleNode::new(elements)),
                ));
            }
            let failure = authenticate_admitted_provider_capture(
                original.arena,
                &changed,
                scope_at(&changed, ordinal),
                operation,
                &mut TypeWorkBudget::unbounded(),
            )
            .err()
            .expect("changed dictionary or same-typed native edges cannot reuse the receipt");
            assert_eq!(
                failure.reason(),
                crate::core::ValidationReason::ResourceEscape
            );
            assert_eq!(
                failure.node(),
                Some(if change_dictionary {
                    dictionary.initializer.node
                } else {
                    operand
                })
            );
        }
    }

    fn nested_arena_dictionary_scopes() -> (ModuleGraph, ValidatedEffectProgram) {
        static NEXT_FIXTURE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        struct FixtureDirectory(PathBuf);
        impl Drop for FixtureDirectory {
            fn drop(&mut self) {
                let _ = std::fs::remove_dir_all(&self.0);
            }
        }
        let sequence = NEXT_FIXTURE.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let directory = FixtureDirectory(std::env::temp_dir().join(format!(
            "ash-arena-core-dictionary-{}-{sequence}",
            std::process::id(),
        )));
        std::fs::create_dir(&directory.0).unwrap();
        let fixtures = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/provider-experiments/arena-typed");
        std::fs::copy(
            fixtures.join("provider.ash"),
            directory.0.join("provider.ash"),
        )
        .unwrap();
        let arena = std::fs::read_to_string(fixtures.join("arena.ash")).unwrap();
        let original = "(arena, layout, alignment, value) => resume (perform Native.Storage<R, Payload>.store (state, layout, alignment, value))";
        assert_eq!(arena.matches(original).count(), 1);
        // Exercise the real ResourceFamily dictionary formal through direct
        // calls, value aliases, a captured Witness value and a captured method
        // alias. The observed helper result supplies the actual native layout;
        // an ordinary Int result also uses the witnessed metadata in its body.
        let arena = arena.replace(
            original,
            r#"(arena, layout, alignment, value) => {
let direct : Native.LayoutWitness<Payload> = Native.witness ()
let witness : Unit -> Native.LayoutWitness<Payload> = Native.witness
let aliased : Native.LayoutWitness<Payload> = witness ()
let retained : Unit -> Native.LayoutWitness<Payload> = fn(unit) {
direct
}
let helper : Unit -> Native.LayoutWitness<Payload> = fn(unit) {
witness unit
}
let natural_alignment : Unit -> Int = fn(unit) {
let metadata : Native.LayoutWitness<Payload> = witness unit
0
}
let captured : Native.LayoutWitness<Payload> = retained ()
let observed : Native.LayoutWitness<Payload> = helper ()
match (aliased, captured, observed) {
(aliased_proof, captured_proof, observed_proof) => resume (perform Native.Storage<R, Payload>.store (state, observed_proof, natural_alignment (), value))
}
}"#,
        );
        std::fs::write(directory.0.join("arena.ash"), arena).unwrap();
        let entry = directory.0.join("entry.ash");
        std::fs::write(
            &entry,
            r#"import provider as Provider
import arena as Memory

main : Unit -> Provider.Scope<Memory.ArenaInitError, Memory.ArenaFinishError, Int>
main () = resource Memory.Arena<A> outer = (Memory.ArenaConfig (8, 1)) {
match (Memory.allocate (outer, 41)) {
Memory.Allocated(first) => {
let ignored = resource Memory.Arena<B> inner = (Memory.ArenaConfig (8, 1)) {
match (Memory.allocate (inner, 99)) {
Memory.Allocated(second) => Memory.load (inner, second)
Memory.AllocationRefused(error) => 0
}
}
Memory.load (outer, first)
}
Memory.AllocationRefused(error) => 0
}
}
"#,
        )
        .unwrap();
        super::super::with_declared_layout_checks_for_test(|| checked_arena_scopes(entry))
    }

    fn core_reaches(program: &UnvalidatedEffectProgram, start: NodeId, target: NodeId) -> bool {
        let mut pending = vec![start];
        let mut seen = std::collections::HashSet::new();
        while let Some(node) = pending.pop() {
            if node == target {
                return true;
            }
            if seen.insert(node) {
                let kind = &program.nodes[node.index().unwrap()].kind;
                pending.extend((0..kind.child_count()).filter_map(|index| kind.child_at(index)));
            }
        }
        false
    }

    #[test]
    fn arena_scope_transforms_reject_changed_forwarding_and_native_operand_edges() {
        use crate::core::{CoreMatchArm, CorePattern, CorePatternKind, PureComputation};
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/provider-experiments/arena-typed/allocation-entry.ash");
        let (graph, program) = checked_arena_scopes(entry);
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
            validate_effect_modules(transform(&program).unwrap(), &sources, &relation).expect(
                "the real typed Arena fixture must independently validate after each transform",
            );
        }
        for transform in [identity_effect_traversal, fold_effect_literal_primitives] {
            let mut forged = transform(&program).unwrap();
            let forwarding = forged
                .nodes
                .iter()
                .find_map(|stored| {
                    let EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) =
                        &stored.kind
                    else {
                        return None;
                    };
                    scope
                        .attached
                        .iter()
                        .flat_map(|member| member.forwardings.iter())
                        .find_map(|forwarding| {
                            forged.nodes.iter().find_map(|stored| {
                                let EffectExprKind::Pure(PureExprKind::Computation(
                                    PureComputation::Bind(binding),
                                )) = &stored.kind
                                else {
                                    return None;
                                };
                                if binding.binder().id() != forwarding.binder {
                                    return None;
                                }
                                let initializer = binding.initializer();
                                let EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(
                                    function,
                                ))) = &forged.nodes[initializer.index().unwrap()].kind
                                else {
                                    return None;
                                };
                                let Type::Tuple(elements) = function.parameter().ty() else {
                                    return None;
                                };
                                (elements.len() == 4 && elements[3] == Type::Int).then(|| {
                                    (initializer, function.parameter().clone(), function.body())
                                })
                            })
                        })
                })
                .expect(
                    "the admitted Int family has an ordinary allocate_checked forwarding function",
                );
            let (initializer, parameter, request) = forwarding;
            let original = &forged.nodes[request.index().unwrap()];
            let EffectExprKind::Operation(EffectOperation::Request(call)) = &original.kind else {
                panic!("the genuine forwarding body must be its source operation request");
            };
            assert!(
                matches!(&forged.nodes[call.operand().index().unwrap()].kind,
                EffectExprKind::Pure(PureExprKind::Variable(variable)) if variable.binder() == parameter.id())
            );
            let repeated = NodeId::new(forged.arena, u32::try_from(forged.nodes.len()).unwrap());
            let origin = original.origin.as_ref().unwrap().clone();
            let pattern = CorePattern::new(
                original.ty.clone(),
                origin.clone(),
                CorePatternKind::Wildcard,
            );
            let replacement = crate::core::dialect::StoredNode {
                dialect: original.dialect,
                ty: original.ty.clone(),
                effects: original.effects.clone(),
                origin: Some(origin.clone()),
                kind: EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Match(
                    crate::core::MatchNode::new(
                        request,
                        vec![CoreMatchArm::new(pattern, request, origin)],
                    ),
                ))),
            };
            // Both requests retain the original operand and result type. This
            // changes execution to two allocations without introducing binders,
            // missing children, or a different declared function effect row.
            forged.nodes.push(replacement);
            forged.nodes[initializer.index().unwrap()].kind =
                EffectExprKind::Pure(PureExprKind::Value(PureValue::Function(
                    crate::core::function::FunctionNode::new(parameter, repeated),
                )));
            let failure = validate_effect_modules(forged, &sources, &relation).expect_err(
                "a well-typed repeated request cannot acquire exact forwarding authority",
            );
            assert_ne!(failure.reason(), crate::core::ValidationReason::Resource);

            let mut forged = transform(&program).unwrap();
            let operand = forged
                .nodes
                .iter()
                .find_map(|stored| {
                    let EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) =
                        &stored.kind
                    else {
                        return None;
                    };
                    scope
                        .descriptor
                        .specialization()?
                        .0
                        .native_storage
                        .iter()
                        .find_map(|receipt| {
                            matches!(
                                receipt.result,
                                super::super::HandlerNativeStorageResult::Store { .. }
                            )
                            .then_some(receipt.operand)
                        })
                })
                .expect("the admitted Int store has its original native operand receipt");
            let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Tuple(tuple))) =
                &forged.nodes[operand.index().unwrap()].kind
            else {
                panic!("native store must retain its actual operand tuple");
            };
            let mut elements = tuple.elements().to_vec();
            assert_eq!(elements.len(), 4);
            assert_ne!(elements[2], elements[3]);
            for child in &elements[2..] {
                assert_eq!(forged.nodes[child.index().unwrap()].ty, Type::Int);
                assert!(forged.nodes[child.index().unwrap()].effects.is_empty());
            }
            // Swapping retains both live child nodes and their binder scopes,
            // while changing the native alignment and stored payload paths.
            elements.swap(2, 3);
            forged.nodes[operand.index().unwrap()].kind =
                EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Tuple(
                    crate::core::TupleNode::new(elements),
                )));
            let failure = validate_effect_modules(forged, &sources, &relation).expect_err(
                "unchanged native request and operand IDs cannot authenticate changed child edges",
            );
            assert_ne!(failure.reason(), crate::core::ValidationReason::Resource);
        }
    }

    #[test]
    fn arena_scope_transforms_reject_a_different_genuine_same_typed_family_dictionary() {
        use crate::core::PureComputation;
        let (graph, program) = nested_arena_dictionary_scopes();
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
            validate_effect_modules(transform(&program).unwrap(), &sources, &relation).expect(
                "both real nested Int scopes and their copied dictionary calls must validate first",
            );
        }
        for transform in [identity_effect_traversal, fold_effect_literal_primitives] {
            let mut forged = transform(&program).unwrap();
            let mut occurrences = Vec::new();
            for (index, stored) in forged.nodes.iter().enumerate() {
                let EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) = &stored.kind
                else {
                    continue;
                };
                let proof = &scope.descriptor.specialization().unwrap().0;
                for family in &proof.families {
                    assert_eq!(family.header.payload, Type::Int);
                    for dictionary in &family.dictionaries {
                        for node in &family.nodes {
                            if matches!(&forged.nodes[node.index().unwrap()].kind,
                                EffectExprKind::Pure(PureExprKind::Variable(variable)) if variable.binder() == dictionary.binder)
                            {
                                occurrences.push((
                                    NodeId::new(forged.arena, u32::try_from(index).unwrap()),
                                    dictionary.binder,
                                    dictionary.producer,
                                    *node,
                                ));
                            }
                        }
                    }
                }
            }
            let replacement = occurrences.iter().find_map(|(outer, donor, producer, _)| {
                let binding = forged.nodes.iter().find_map(|stored| {
                    let EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding))) = &stored.kind else { return None; };
                    (binding.binder().id() == *donor).then_some(binding)
                })?;
                occurrences.iter().find_map(|(inner, original, inner_producer, node)| {
                    if outer == inner || donor == original || producer != inner_producer
                        || !core_reaches(&forged, binding.body(), *inner) {
                        return None;
                    }
                    assert_eq!(binding.binder().ty(), &forged.nodes[node.index().unwrap()].ty);
                    assert!(forged.nodes[node.index().unwrap()].effects.is_empty());
                    Some((*node, *donor))
                })
            }).expect("a genuine outer Int Layout dictionary must dominate the inner copied family occurrence");
            let (node, donor) = replacement;
            forged.nodes[node.index().unwrap()].kind = EffectExprKind::Pure(
                PureExprKind::Variable(crate::core::variable::VariableNode::new(donor)),
            );
            let failure = validate_effect_modules(forged, &sources, &relation)
                .expect_err("same producer and type do not replace the copied occurrence's exact dictionary binder");
            assert_ne!(failure.reason(), crate::core::ValidationReason::Resource);
        }
    }

    #[test]
    fn mixed_resource_owner_vectors_reject_independent_core_mutations_after_both_transforms() {
        use crate::types::{EffectRow, EffectRowVariable, KindedArgument};
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/provider-experiments/control-source/callback-open.ash");
        let (graph, program) = checked_provider_scopes(entry);
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
                .expect("the actual mixed-owner public pipeline must survive each rebuild");
            for mutation in 0..8 {
                let mut forged = transform(&program).unwrap();
                let stored = forged.nodes.iter_mut().find(|node|
                    matches!(&node.ty, Type::ResourceApply(_, arguments)
                        if matches!(arguments.as_ref(), [KindedArgument::TypeArg(_), KindedArgument::RowArg(_)]))
                    && matches!(&node.kind, EffectExprKind::Pure(PureExprKind::Variable(_))))
                    .expect("the checked callback resource has a concrete mixed-owner access occurrence");
                let Type::ResourceApply(resource, actuals) = &stored.ty else {
                    unreachable!()
                };
                let original_resource = *resource;
                let mut arguments = clone_kinded_arguments_with_budget(
                    actuals.iter(),
                    &mut TypeWorkBudget::unbounded(),
                )
                .unwrap()
                .into_vec();
                let unknown =
                    crate::types::TypeVariableId::resolved(original_resource.module(), u32::MAX);
                assert!(
                    forged.registry.type_variable(unknown).is_none(),
                    "the forged scope tail must be genuinely unbound"
                );
                let mut identity = original_resource;
                match mutation {
                    0 => {
                        identity = crate::resolved::ResourceDefinitionId::new(
                            original_resource.module(),
                            u32::MAX,
                        )
                    }
                    1 => arguments[0] = KindedArgument::RowArg(EffectRow::empty()),
                    2 => arguments[1] = KindedArgument::TypeArg(Type::Unit),
                    3 => {
                        arguments.pop();
                    }
                    4 => arguments.push(KindedArgument::RowArg(EffectRow::empty())),
                    5 => arguments.swap(0, 1),
                    6 => arguments[0] = KindedArgument::TypeArg(Type::Variable(unknown)),
                    7 => {
                        arguments[1] = KindedArgument::RowArg(EffectRow::with_tail(
                            Box::new([]),
                            EffectRowVariable::Rigid(unknown),
                            Box::new([]),
                        ))
                    }
                    _ => unreachable!(),
                }
                crate::types::discard_type_iteratively(std::mem::replace(
                    &mut stored.ty,
                    Type::ResourceApply(identity, arguments.into_boxed_slice()),
                ));
                let failure = validate_effect_modules(forged, &sources, &relation).expect_err(
                    "an independently mutated mixed-owner argument must not acquire Core authority",
                );
                assert_ne!(
                    failure.reason(),
                    crate::core::ValidationReason::Resource,
                    "mutation {mutation} must fail its owner/tag/saturation/scope relation, not a work limit"
                );
            }
        }
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
            families: Box::new([]),
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
