//! Bounded compiler claims for copying immutable checked template occurrences.
//!
//! Copying grants no authority. Final Core independently reconstructs the
//! original projection, complete substitution, freshness and catalog relation.

use crate::{
    core::{BuildError, HandlerId},
    interface::LexicalEvidenceId,
    resolved::{BinderId, ResumeId},
    types::{
        ConstructorId, EffectRow, InferenceVariableId, KindedArgument, NominalTypeId,
        TemplateIdentityRenaming, Type, TypeVariableId, TypeWorkBudget,
    },
};
use std::collections::HashMap;

/// Borrowed complete actual substitution and local identity relocation. These
/// are compiler claims, not certificates or executable permission.
pub(crate) struct ProviderCopyContext<'a> {
    pub(crate) types: &'a HashMap<TypeVariableId, Type>,
    pub(crate) rows: &'a HashMap<TypeVariableId, EffectRow>,
    pub(crate) pending: &'a HashMap<InferenceVariableId, EffectRow>,
    pub(crate) node_rows: &'a HashMap<super::super::NodeId, EffectRow>,
    pub(crate) variables: &'a HashMap<TypeVariableId, TypeVariableId>,
    pub(crate) nominals: &'a HashMap<NominalTypeId, NominalTypeId>,
    pub(crate) binders: &'a HashMap<BinderId, BinderId>,
    pub(crate) handlers: &'a HashMap<HandlerId, HandlerId>,
    pub(crate) resumes: &'a HashMap<ResumeId, ResumeId>,
    pub(crate) lexicals: &'a HashMap<LexicalEvidenceId, LexicalEvidenceId>,
}
impl ProviderCopyContext<'_> {
    fn renaming(&self) -> TemplateIdentityRenaming<'_> {
        TemplateIdentityRenaming {
            nominals: self.nominals,
            variables: self.variables,
        }
    }
    pub(crate) fn ty(
        &self,
        original: &Type,
        work: &mut TypeWorkBudget,
    ) -> Result<Type, BuildError> {
        crate::types::substitute_type_for_template_with(
            original,
            self.types,
            self.rows,
            self.pending,
            &self.renaming(),
            |cells| {
                work.charge(cells)
                    .map_err(|()| BuildError::TypeWorkExceeded)
            },
            || BuildError::TypeWorkExceeded,
        )?
        .map_err(|_| BuildError::InvalidPayload)
    }
    pub(crate) fn row(
        &self,
        original: &EffectRow,
        work: &mut TypeWorkBudget,
    ) -> Result<EffectRow, BuildError> {
        crate::types::substitute_row_for_template_with(
            original,
            self.types,
            self.rows,
            self.pending,
            &self.renaming(),
            |cells| {
                work.charge(cells)
                    .map_err(|()| BuildError::TypeWorkExceeded)
            },
            || BuildError::TypeWorkExceeded,
        )?
        .map_err(|_| BuildError::InvalidPayload)
    }
    /// Realization has already applied full sigma. This pass performs only
    /// local identity alpha relocation, never substitutes caller payload again.
    pub(crate) fn realized_row(
        &self,
        original: &EffectRow,
        work: &mut TypeWorkBudget,
    ) -> Result<EffectRow, BuildError> {
        let types = HashMap::new();
        let rows = HashMap::new();
        let pending = HashMap::new();
        crate::types::substitute_row_for_template_with(
            original,
            &types,
            &rows,
            &pending,
            &self.renaming(),
            |cells| {
                work.charge(cells)
                    .map_err(|()| BuildError::TypeWorkExceeded)
            },
            || BuildError::TypeWorkExceeded,
        )?
        .map_err(|_| BuildError::InvalidPayload)
    }
    pub(crate) fn argument(
        &self,
        original: &KindedArgument,
        work: &mut TypeWorkBudget,
    ) -> Result<KindedArgument, BuildError> {
        crate::types::substitute_argument_for_template_with(
            original,
            self.types,
            self.rows,
            self.pending,
            &self.renaming(),
            |cells| {
                work.charge(cells)
                    .map_err(|()| BuildError::TypeWorkExceeded)
            },
            || BuildError::TypeWorkExceeded,
        )?
        .map_err(|_| BuildError::InvalidPayload)
    }
    pub(crate) fn binder(
        &self,
        id: BinderId,
        work: &mut TypeWorkBudget,
    ) -> Result<BinderId, BuildError> {
        lookup(self.binders, id, work)
    }
    pub(crate) fn variable(
        &self,
        id: TypeVariableId,
        work: &mut TypeWorkBudget,
    ) -> Result<TypeVariableId, BuildError> {
        lookup(self.variables, id, work)
    }
    pub(crate) fn handler(
        &self,
        id: HandlerId,
        work: &mut TypeWorkBudget,
    ) -> Result<HandlerId, BuildError> {
        lookup(self.handlers, id, work)
    }
    pub(crate) fn resume(
        &self,
        id: ResumeId,
        work: &mut TypeWorkBudget,
    ) -> Result<ResumeId, BuildError> {
        lookup(self.resumes, id, work)
    }
    pub(crate) fn lexical(
        &self,
        id: LexicalEvidenceId,
        work: &mut TypeWorkBudget,
    ) -> Result<LexicalEvidenceId, BuildError> {
        lookup(self.lexicals, id, work)
    }
    pub(crate) fn nominal(
        &self,
        id: NominalTypeId,
        work: &mut TypeWorkBudget,
    ) -> Result<NominalTypeId, BuildError> {
        lookup(self.nominals, id, work)
    }
    pub(crate) fn constructor(
        &self,
        id: ConstructorId,
        work: &mut TypeWorkBudget,
    ) -> Result<ConstructorId, BuildError> {
        Ok(ConstructorId::new(
            self.nominal(id.owner(), work)?,
            id.constructor(),
        ))
    }
}
fn lookup<K: Copy + Eq + std::hash::Hash>(
    map: &HashMap<K, K>,
    id: K,
    work: &mut TypeWorkBudget,
) -> Result<K, BuildError> {
    work.charge(1).map_err(|()| BuildError::TypeWorkExceeded)?;
    Ok(map.get(&id).copied().unwrap_or(id))
}

/// Explicit final-catalog address for an original anchor. This relation is a
/// compiler claim consumed again by the independent specialization proof.
pub(crate) struct ProviderCatalogRelocation {
    pub(crate) original_anchor: usize,
    pub(crate) owner: Option<super::super::dialect::MethodEvidenceOwner>,
    pub(crate) requirement: Option<crate::interface::RequirementId>,
    pub(crate) occurrence: Option<usize>,
    // Catalogue/binder/lexical fields are final scalar claims. AdapterEdge
    // producer_node is an original-arena address relocated by the forest map.
    pub(crate) role: super::super::dialect::MethodEvidenceAnchorRole,
}

/// Scalar forest relation, retaining the original arena identity on every pair.
pub(crate) struct ProviderCopiedForest {
    pub(crate) roots: Vec<super::super::NodeId>,
    pub(crate) nodes: Vec<(super::super::NodeId, super::super::NodeId)>,
}

/// Append an immutable checked forest through the ordinary transform engine.
/// The final builder must already contain the authenticated target registry and
/// final catalogue. Replacement nodes and catalog addresses are explicit claims;
/// copying never manufactures their authority.
pub(crate) fn copy_provider_forest(
    builder: &mut super::super::CoreBuilder<super::super::EffectOperationFamily>,
    original: &super::super::UnvalidatedEffectProgram,
    roots: &[super::super::NodeId],
    replacements: &HashMap<super::super::NodeId, super::super::NodeId>,
    context: &ProviderCopyContext<'_>,
    catalog: &[ProviderCatalogRelocation],
) -> Result<ProviderCopiedForest, super::super::transform::TransformError> {
    copy_provider_forest_inner(
        builder,
        original,
        roots,
        replacements,
        context,
        Some(catalog),
    )
}

/// Typed source-check preparation for real capture reconstruction. This keeps
/// all copied graph metadata and complete substitution, but emits no catalogue
/// anchors into the source checker's unpublished empty catalogue. Original
/// selection/certificate pins must remain in the compiler preparation plan.
/// No result of this function is executable authority.
pub(crate) fn copy_prepared_provider_forest(
    builder: &mut super::super::CoreBuilder<super::super::EffectOperationFamily>,
    original: &super::super::UnvalidatedEffectProgram,
    roots: &[super::super::NodeId],
    replacements: &HashMap<super::super::NodeId, super::super::NodeId>,
    context: &ProviderCopyContext<'_>,
) -> Result<ProviderCopiedForest, super::super::transform::TransformError> {
    copy_provider_forest_inner(builder, original, roots, replacements, context, None)
}

fn copy_provider_forest_inner(
    builder: &mut super::super::CoreBuilder<super::super::EffectOperationFamily>,
    original: &super::super::UnvalidatedEffectProgram,
    roots: &[super::super::NodeId],
    replacements: &HashMap<super::super::NodeId, super::super::NodeId>,
    context: &ProviderCopyContext<'_>,
    catalog: Option<&[ProviderCatalogRelocation]>,
) -> Result<ProviderCopiedForest, super::super::transform::TransformError> {
    use super::super::{dialect::MethodEvidenceAnchorRole, transform};
    use std::collections::HashSet;
    let resource = || BuildError::TypeWorkExceeded;
    builder
        .type_work
        .charge(replacements.len())
        .map_err(|()| resource())?;
    let mut replaced = HashSet::new();
    replaced
        .try_reserve(replacements.len())
        .map_err(|_| resource())?;
    for old in replacements.keys() {
        replaced.insert(*old);
    }
    let order =
        transform::provider_entry_forest_order(original, roots, &replaced, &mut builder.type_work)?;
    builder
        .type_work
        .charge(original.nodes.len())
        .map_err(|()| resource())?;
    let mut remapped = Vec::new();
    remapped
        .try_reserve_exact(original.nodes.len())
        .map_err(|_| resource())?;
    remapped.resize(original.nodes.len(), None);
    builder
        .type_work
        .charge(context.binders.len())
        .map_err(|()| resource())?;
    let mut reserved = Vec::new();
    reserved
        .try_reserve_exact(context.binders.len())
        .map_err(|_| resource())?;
    reserved.extend(context.binders.values().copied());
    builder.reserve_provider_copy_binders(&reserved)?;
    builder
        .type_work
        .charge(order.len())
        .map_err(|()| resource())?;
    let mut nodes = Vec::new();
    nodes
        .try_reserve_exact(order.len())
        .map_err(|_| resource())?;
    for old in order {
        let copied = match replacements.get(&old) {
            Some(copied) => {
                builder.provider_node_at_ordinal(*copied, copied.index()?)?;
                *copied
            }
            None => transform::rebuild_provider_draft_node_with_context(
                builder, original, &remapped, old, context,
            )?,
        };
        let index = old.index()?;
        *remapped.get_mut(index).ok_or(BuildError::InvalidPayload)? = Some(copied);
        nodes.push((old, copied));
    }
    if let Some(catalog) = catalog {
        builder
            .type_work
            .charge(
                original
                    .method_evidence_anchors
                    .len()
                    .checked_add(catalog.len())
                    .ok_or_else(resource)?,
            )
            .map_err(|()| resource())?;
        let mut addresses = HashMap::new();
        addresses
            .try_reserve(catalog.len())
            .map_err(|_| resource())?;
        for relocation in catalog {
            if addresses
                .insert(relocation.original_anchor, relocation)
                .is_some()
            {
                return Err(BuildError::InvalidPayload.into());
            }
        }
        for (ordinal, anchor) in original.method_evidence_anchors.iter().enumerate() {
            let node = remapped.get(anchor.node.index()?).copied().flatten();
            let Some(node) = node else { continue };
            // Replaced admission sites are authenticated by the replacement's own
            // proof; original source authority is not attached to arbitrary nodes.
            if replacements.contains_key(&anchor.node) {
                continue;
            }
            let relocation = addresses
                .remove(&ordinal)
                .ok_or(BuildError::InvalidPayload)?;
            // Every target role is explicit, including catalog ordinals. Its source
            // selection/certificate relation is independently checked at admission.
            // Scalar claims are final catalogue addresses; node claims still name
            // the exact original forest until this complete map supplies targets.
            let role = match relocation.role {
                MethodEvidenceAnchorRole::AdapterEdge {
                    adapter,
                    adapter_selection_node,
                    ordinal,
                    producer_node,
                    producer_selection_node,
                    producer_binder,
                    producer,
                } => {
                    let producer_node = remapped
                        .get(producer_node.index()?)
                        .copied()
                        .flatten()
                        .ok_or(BuildError::InvalidPayload)?;
                    builder.provider_node_at_ordinal(producer_node, producer_node.index()?)?;
                    MethodEvidenceAnchorRole::AdapterEdge {
                        adapter,
                        adapter_selection_node,
                        ordinal,
                        producer_node,
                        producer_selection_node,
                        producer_binder,
                        producer,
                    }
                }
                other => other,
            };
            let mut arguments = OwnedArguments(Vec::new());
            builder
                .type_work
                .charge(anchor.application.arguments().len())
                .map_err(|()| resource())?;
            arguments
                .0
                .try_reserve_exact(anchor.application.arguments().len())
                .map_err(|_| resource())?;
            for argument in anchor.application.arguments() {
                arguments
                    .0
                    .push(context.argument(argument, &mut builder.type_work)?);
            }
            let application = crate::interface::InterfaceApplication::new_kinded(
                anchor.application.interface(),
                arguments.into_boxed_slice(),
            );
            builder.authenticate_method_evidence(
                node,
                relocation.owner,
                relocation.requirement,
                anchor.method,
                application,
                role,
                relocation.occurrence,
            )?;
        }
        if !addresses.is_empty() {
            return Err(BuildError::InvalidPayload.into());
        }
    }
    builder
        .type_work
        .charge(roots.len())
        .map_err(|()| resource())?;
    let mut copied_roots = Vec::new();
    copied_roots
        .try_reserve_exact(roots.len())
        .map_err(|_| resource())?;
    for old in roots {
        copied_roots.push(
            remapped
                .get(old.index()?)
                .copied()
                .flatten()
                .ok_or(BuildError::InvalidPayload)?,
        );
    }
    Ok(ProviderCopiedForest {
        roots: copied_roots,
        nodes,
    })
}
struct OwnedArguments(Vec<KindedArgument>);
impl OwnedArguments {
    fn into_boxed_slice(mut self) -> Box<[KindedArgument]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}
impl Drop for OwnedArguments {
    fn drop(&mut self) {
        for argument in self.0.drain(..) {
            crate::types::discard_kinded_argument_iteratively(argument);
        }
    }
}
