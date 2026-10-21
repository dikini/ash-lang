//! Checked interface-evidence selection.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use crate::{
    interface::{
        CheckedImplementation, ConstrainedScheme, DeterminationKey, EvidenceNode,
        EvidenceSelection, EvidenceSelectionBuilder, EvidenceSlotHandle, EvidenceSubstitution,
        HeadMatchFailure, ImplId, ImplMethodId, InterfaceApplication, InterfaceConstraintBudget,
        InterfaceId, InterfaceOperationWork, InterfaceReason, LexicalEvidenceId, MethodId,
        RequirementId, authenticate_implementation_application_goal,
        match_implementation_application_head_against_canonical_goal,
        match_implementation_application_head_in_environment,
        match_provider_family_application_head_in_environment,
        same_kinded_argument_with_constraint_budget,
    },
    kind::{
        CanonicalEnvironmentFailure, KindEnvironments, KindFailure,
        canonical_body_free_argument_environments, canonical_type_variable_kind,
    },
    resolved::{
        BinderId, CheckedGlobalScheme, CheckedInterfaceFact, ImportedGlobalScheme,
        ImportedImplementationFact, ResolvedImplementation, ResolvedRegistry, ResolvedTypeVariable,
    },
    source::Span,
    types::{
        EffectRow, EffectRowVariable, IterativeTypeOwner, Kind, KindedArgument, NominalTypeId,
        Type, TypeVariableId, TypeWorkBudget, clone_kind_with_budget,
        clone_kinded_argument_with_budget, clone_type_with_budget,
        discard_kinded_argument_iteratively, discard_type_iteratively,
        map_kinded_argument_types_with_budget, same_kind_with_charge,
        substitute_kinded_argument_with, visit_owner_components_with_charge,
    },
};

#[cfg(test)]
use crate::interface::same_type_with_constraint_budget as same_semantic_type_with_constraint_budget;
#[cfg(test)]
use crate::types::extend_owner_type_children_with_charge;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SelectionFailure {
    Reason(InterfaceReason),
    TypeResource,
    ConstraintResource,
    InvalidState,
    Kind {
        context: crate::kind::KindFailureContext,
        span: Option<Span>,
    },
}

impl From<()> for SelectionFailure {
    fn from(_: ()) -> Self {
        Self::TypeResource
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SelectionError {
    failure: SelectionFailure,
    span: Option<Span>,
    declaration_span: Option<Span>,
    import_span: Option<Span>,
    causes: Vec<SelectionCause>,
}

impl SelectionError {
    pub(crate) const fn failure(&self) -> SelectionFailure {
        self.failure
    }

    pub(crate) const fn span(&self) -> Option<Span> {
        self.span
    }

    pub(crate) const fn declaration_span(&self) -> Option<Span> {
        self.declaration_span
    }

    pub(crate) const fn import_span(&self) -> Option<Span> {
        self.import_span
    }

    pub(crate) fn causes(&self) -> &[SelectionCause] {
        &self.causes
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SelectionCauseKind {
    Interface,
    Implementation,
    ImplementationMethod,
    ImplementationImport,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct SelectionCause {
    kind: SelectionCauseKind,
    span: Span,
}

impl SelectionCause {
    pub(crate) const fn kind(self) -> SelectionCauseKind {
        self.kind
    }

    pub(crate) const fn span(self) -> Span {
        self.span
    }
}

#[derive(Debug)]
struct MethodEntry {
    id: MethodId,
    type_parameters: Box<[(TypeVariableId, Kind)]>,
    value_type: Type,
    span: Span,
}

impl Drop for MethodEntry {
    fn drop(&mut self) {
        discard_type_iteratively(std::mem::replace(&mut self.value_type, Type::Unit));
    }
}

#[derive(Debug)]
struct InterfaceEntry {
    id: InterfaceId,
    sealed_layout: bool,
    parameters: Box<[(TypeVariableId, Kind)]>,
    determination: Option<DeterminationKey>,
    methods: Box<[MethodEntry]>,
    method_ids: Box<[MethodId]>,
    span: Span,
}

#[derive(Debug)]
struct SchemeEntry {
    scheme: ConstrainedScheme,
    declaration_span: Span,
}

#[derive(Debug)]
struct RequirementEntry {
    id: RequirementId,
    application: InterfaceApplication,
    span: Span,
}

#[derive(Debug)]
struct ImplementationEntry {
    id: ImplId,
    application: InterfaceApplication,
    parameters: Box<[TypeVariableId]>,
    prerequisites: Box<[RequirementEntry]>,
    methods: Box<[ImplMethodId]>,
    span: Span,
    method_spans: Vec<Span>,
    import_spans: Box<[Span]>,
}

#[derive(Debug)]
struct PendingObligation {
    lexical_head: Option<usize>,
    checked_method: Option<MethodId>,
    application: InterfaceApplication,
    method_arguments: Box<[Type]>,
    checked_value_type: Option<Type>,
    method_rigidity: Option<MethodRigidityCondition>,
    slot: EvidenceSlotHandle,
    span: Span,
    declaration_span: Option<Span>,
    import_span: Option<Span>,
}

/// One source-order improvement transaction prepared from the pre-pass key
/// snapshot. The elaborator applies these tuples while it still owns inference.
#[derive(Debug)]
pub(crate) struct ImprovementTask {
    key: Box<[KindedArgument]>,
    expected_dependents: Box<[KindedArgument]>,
    actual_dependents: Box<[KindedArgument]>,
    obligation_span: Span,
    source_span: Span,
}

type ImprovementTaskParts = (
    Box<[KindedArgument]>,
    Box<[KindedArgument]>,
    Box<[KindedArgument]>,
    Span,
    Span,
);

impl ImprovementTask {
    #[cfg(test)]
    pub(crate) fn for_test(
        key: Box<[KindedArgument]>,
        expected_dependents: Box<[KindedArgument]>,
        actual_dependents: Box<[KindedArgument]>,
        obligation_span: Span,
        source_span: Span,
    ) -> Self {
        Self {
            key,
            expected_dependents,
            actual_dependents,
            obligation_span,
            source_span,
        }
    }

    pub(crate) fn into_parts(mut self) -> ImprovementTaskParts {
        (
            std::mem::take(&mut self.key),
            std::mem::take(&mut self.expected_dependents),
            std::mem::take(&mut self.actual_dependents),
            self.obligation_span,
            self.source_span,
        )
    }
}

impl Drop for ImprovementTask {
    fn drop(&mut self) {
        for ty in std::mem::take(&mut self.key).into_vec() {
            discard_kinded_argument_iteratively(ty);
        }
        for ty in std::mem::take(&mut self.expected_dependents).into_vec() {
            discard_kinded_argument_iteratively(ty);
        }
        for ty in std::mem::take(&mut self.actual_dependents).into_vec() {
            discard_kinded_argument_iteratively(ty);
        }
    }
}

/// Exact pending prefix captured before a nested obligation suffix is staged.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct PendingObligationMarker {
    pending_len: usize,
    determined_count: usize,
}

impl PendingObligationMarker {
    /// The completed ordinary suffix includes this saved source suffix.
    pub(crate) fn covers(self, nested: Self) -> bool {
        self.pending_len <= nested.pending_len && self.determined_count <= nested.determined_count
    }
    #[cfg(test)]
    const fn for_test(pending_len: usize, determined_count: usize) -> Self {
        Self {
            pending_len,
            determined_count,
        }
    }
}

/// Eligibility fixed before any improvement transaction mutates inference.
#[derive(Debug)]
pub(crate) struct DeterminationSnapshot {
    marker: PendingObligationMarker,
    eligible: Box<[bool]>,
    tasks: Vec<ImprovementTask>,
}

impl DeterminationSnapshot {
    pub(crate) fn take_tasks(&mut self) -> Vec<ImprovementTask> {
        std::mem::take(&mut self.tasks)
    }
}

/// Eligibility for only the causally matching failed-body rigidity root.
#[derive(Debug)]
pub(crate) struct MethodRigidityDeterminationSnapshot {
    target: MethodRigidityTarget,
    matching_index: Option<usize>,
    determined: bool,
    eligible: bool,
    task: Option<ImprovementTask>,
}

impl MethodRigidityDeterminationSnapshot {
    pub(crate) fn take_task(&mut self) -> Option<ImprovementTask> {
        self.task.take()
    }
}

/// Diagnostic location retained until selection determines whether a same-method
/// occurrence is an exact-current recursive dispatch.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct MethodRigiditySite {
    occurrence_span: Span,
    application_span: Option<Span>,
    argument_span: Option<Span>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum MethodRigidityMatchRank {
    // Declaration order is causal priority: the smallest matching rank wins.
    Application,
    Argument,
    Occurrence,
}

impl MethodRigiditySite {
    pub(crate) const fn occurrence(occurrence_span: Span) -> Self {
        Self {
            occurrence_span,
            application_span: None,
            argument_span: None,
        }
    }

    pub(crate) const fn application(
        occurrence_span: Span,
        application_span: Span,
        argument_span: Span,
    ) -> Self {
        Self {
            occurrence_span,
            application_span: Some(application_span),
            argument_span: Some(argument_span),
        }
    }

    pub(crate) const fn occurrence_span(self) -> Span {
        self.occurrence_span
    }

    pub(crate) const fn application_span(self) -> Option<Span> {
        self.application_span
    }

    pub(crate) const fn argument_span(self) -> Option<Span> {
        self.argument_span
    }

    fn failure_match_rank(self, span: Span) -> Option<MethodRigidityMatchRank> {
        if self.application_span == Some(span) {
            Some(MethodRigidityMatchRank::Application)
        } else if self.argument_span == Some(span) {
            Some(MethodRigidityMatchRank::Argument)
        } else if self.application_span.is_none()
            && self.argument_span.is_none()
            && self.occurrence_span == span
        {
            Some(MethodRigidityMatchRank::Occurrence)
        } else {
            None
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct MethodRigidityTarget {
    marker: PendingObligationMarker,
    failure_span: Span,
}

impl MethodRigidityTarget {
    pub(crate) const fn new(marker: PendingObligationMarker, failure_span: Span) -> Self {
        Self {
            marker,
            failure_span,
        }
    }

    #[cfg(test)]
    pub(crate) const fn failure_span(self) -> Span {
        self.failure_span
    }
}

/// Same-method rigid arguments that become relevant only after exact-current
/// evidence wins selection.
#[derive(Debug)]
pub(crate) struct MethodRigidityCondition {
    rigid_arguments: Box<[Type]>,
    site: MethodRigiditySite,
}

#[derive(Debug)]
pub(crate) struct MethodObligationMetadata {
    checked_method: MethodId,
    method_arguments: Box<[Type]>,
    checked_value_type: Option<Type>,
    method_rigidity: Option<MethodRigidityCondition>,
}

impl MethodObligationMetadata {
    pub(crate) const fn new(
        checked_method: MethodId,
        method_arguments: Box<[Type]>,
        method_rigidity: Option<MethodRigidityCondition>,
    ) -> Self {
        Self {
            checked_method,
            method_arguments,
            checked_value_type: None,
            method_rigidity,
        }
    }

    pub(crate) fn with_checked_value_type(mut self, checked_value_type: Type) -> Self {
        if let Some(displaced) = self.checked_value_type.replace(checked_value_type) {
            discard_type_iteratively(displaced);
        }
        self
    }

    fn into_parts(
        mut self,
    ) -> (
        MethodId,
        Box<[Type]>,
        Option<Type>,
        Option<MethodRigidityCondition>,
    ) {
        (
            self.checked_method,
            std::mem::take(&mut self.method_arguments),
            self.checked_value_type.take(),
            self.method_rigidity.take(),
        )
    }
}

impl Drop for MethodObligationMetadata {
    fn drop(&mut self) {
        for argument in std::mem::take(&mut self.method_arguments).into_vec() {
            discard_type_iteratively(argument);
        }
        if let Some(checked_value_type) = self.checked_value_type.take() {
            discard_type_iteratively(checked_value_type);
        }
    }
}

impl MethodRigidityCondition {
    pub(crate) const fn new(rigid_arguments: Box<[Type]>, site: MethodRigiditySite) -> Self {
        Self {
            rigid_arguments,
            site,
        }
    }
}

impl Drop for MethodRigidityCondition {
    fn drop(&mut self) {
        for argument in std::mem::take(&mut self.rigid_arguments).into_vec() {
            discard_type_iteratively(argument);
        }
    }
}

#[derive(Debug)]
struct SelectedMethodRigidity {
    selected_index: usize,
    condition: MethodRigidityCondition,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct MethodRigidityCheck<'a> {
    method_arguments: &'a [Type],
    rigid_arguments: &'a [Type],
    site: MethodRigiditySite,
}

impl<'a> MethodRigidityCheck<'a> {
    #[cfg(test)]
    pub(crate) const fn for_test(
        method_arguments: &'a [Type],
        rigid_arguments: &'a [Type],
        site: MethodRigiditySite,
    ) -> Self {
        Self {
            method_arguments,
            rigid_arguments,
            site,
        }
    }

    pub(crate) const fn method_arguments(self) -> &'a [Type] {
        self.method_arguments
    }

    pub(crate) const fn rigid_arguments(self) -> &'a [Type] {
        self.rigid_arguments
    }

    pub(crate) const fn site(self) -> MethodRigiditySite {
        self.site
    }
}

#[derive(Debug)]
pub(crate) struct SelectionSite {
    slot: EvidenceSlotHandle,
    span: Span,
    declaration_span: Option<Span>,
    import_span: Option<Span>,
}

impl SelectionSite {
    pub(crate) const fn contextual(
        slot: EvidenceSlotHandle,
        span: Span,
        declaration_span: Span,
        import_span: Option<Span>,
    ) -> Self {
        Self {
            slot,
            span,
            declaration_span: Some(declaration_span),
            import_span,
        }
    }

    #[cfg(test)]
    const fn plain(slot: EvidenceSlotHandle, span: Span) -> Self {
        Self {
            slot,
            span,
            declaration_span: None,
            import_span: None,
        }
    }
}

impl Drop for PendingObligation {
    fn drop(&mut self) {
        for argument in std::mem::take(&mut self.method_arguments).into_vec() {
            discard_type_iteratively(argument);
        }
        if let Some(ty) = self.checked_value_type.take() {
            discard_type_iteratively(ty);
        }
    }
}

#[derive(Debug)]
struct SelectedOccurrence {
    checked_method: Option<MethodId>,
    checked_application: InterfaceApplication,
    method_arguments: Box<[Type]>,
    checked_value_type: Option<Type>,
    selection: Option<EvidenceSelection>,
    slot: Option<EvidenceSlotHandle>,
}

impl Drop for SelectedOccurrence {
    fn drop(&mut self) {
        for argument in std::mem::take(&mut self.method_arguments).into_vec() {
            discard_type_iteratively(argument);
        }
        if let Some(ty) = self.checked_value_type.take() {
            discard_type_iteratively(ty);
        }
    }
}

/// Fully zonked occurrence facts staged before checked-module publication.
#[derive(Debug, Default)]
pub(crate) struct PendingEvidencePublication {
    occurrences: Vec<SelectedOccurrence>,
    slot_ids: HashMap<usize, Option<MethodId>>,
}

/// One compiler batch whose original source slots have all passed preflight.
///
/// Dropping this token publishes nothing. The compiler must preflight any
/// associated instance-plan batch before committing either batch, and must not
/// fill these private one-shot slots between preparation and commit.
#[derive(Debug)]
pub(crate) struct PreflightedEvidencePublication {
    publication: PendingEvidencePublication,
}

/// Borrowed closed source facts; obtaining this view never fills a slot.
pub(crate) struct PendingOccurrence<'a> {
    pub(crate) application: &'a InterfaceApplication,
    pub(crate) method: Option<MethodId>,
    pub(crate) method_arguments: &'a [Type],
    pub(crate) value_type: Option<&'a Type>,
    pub(crate) selection: &'a EvidenceSelection,
}

#[cfg(test)]
thread_local! {
    static APPEND_RESERVATION_REFUSAL: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
}
#[cfg(test)]
pub(crate) struct AppendReservationRefusalForTest;
#[cfg(test)]
impl Drop for AppendReservationRefusalForTest {
    fn drop(&mut self) {
        APPEND_RESERVATION_REFUSAL.with(|site| site.set(None));
    }
}
#[cfg(test)]
pub(crate) fn refuse_append_reservation_after_for_test(
    successful_appends: usize,
) -> AppendReservationRefusalForTest {
    APPEND_RESERVATION_REFUSAL.with(|site| {
        assert!(site.get().is_none());
        site.set(Some(successful_appends));
    });
    AppendReservationRefusalForTest
}
#[cfg(test)]
impl AppendReservationRefusalForTest {
    pub(crate) fn was_consumed(&self) -> bool {
        APPEND_RESERVATION_REFUSAL.with(|site| site.get().is_none())
    }
}

impl PendingEvidencePublication {
    /// Joins independently checked batches without filling any source slot.
    /// The receiver is unchanged on refusal; publication still preflights the
    /// complete combined batch immediately before the sole commit.
    pub(crate) fn append(
        &mut self,
        mut incoming: Self,
        budget: &mut InterfaceConstraintBudget,
    ) -> Result<(), SelectionFailure> {
        let count = incoming.occurrences.len();
        budget
            .charge(
                count
                    .checked_mul(2)
                    .ok_or(SelectionFailure::ConstraintResource)?,
            )
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        if count != incoming.slot_ids.len() {
            return Err(SelectionFailure::InvalidState);
        }
        for occurrence in &incoming.occurrences {
            let slot = occurrence
                .slot
                .as_ref()
                .ok_or(SelectionFailure::InvalidState)?;
            if self.slot_ids.contains_key(&slot.storage_id())
                || incoming.slot_ids.remove(&slot.storage_id()) != Some(occurrence.checked_method)
            {
                return Err(SelectionFailure::InvalidState);
            }
        }
        // Test-only deterministic refusal at this recoverable reservation site;
        // it is separate from work-limit failures and general allocator behavior.
        #[cfg(test)]
        if APPEND_RESERVATION_REFUSAL.with(|site| match site.get() {
            Some(0) => {
                site.set(None);
                true
            }
            Some(remaining) => {
                site.set(Some(remaining - 1));
                false
            }
            None => false,
        }) {
            return Err(SelectionFailure::ConstraintResource);
        }
        self.occurrences
            .try_reserve(count)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.slot_ids
            .try_reserve(count)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        for occurrence in &incoming.occurrences {
            self.slot_ids.insert(
                occurrence
                    .slot
                    .as_ref()
                    .expect("append checks every slot")
                    .storage_id(),
                occurrence.checked_method,
            );
        }
        self.occurrences.append(&mut incoming.occurrences);
        Ok(())
    }

    pub(crate) fn occurrence(
        &self,
        slot: usize,
        method: Option<MethodId>,
        budget: &mut TypeWorkBudget,
    ) -> Result<PendingOccurrence<'_>, SelectionFailure> {
        budget
            .charge(self.occurrences.len())
            .map_err(|()| SelectionFailure::TypeResource)?;
        let occurrence = self
            .occurrences
            .iter()
            .find(|occurrence| {
                occurrence
                    .slot
                    .as_ref()
                    .is_some_and(|candidate| candidate.storage_id() == slot)
            })
            .ok_or(SelectionFailure::InvalidState)?;
        if occurrence.checked_method != method
            || self.slot_ids.get(&slot) != Some(&method)
            || !occurrence
                .slot
                .as_ref()
                .ok_or(SelectionFailure::InvalidState)?
                .is_empty()
        {
            return Err(SelectionFailure::InvalidState);
        }
        Ok(PendingOccurrence {
            application: &occurrence.checked_application,
            method: occurrence.checked_method,
            method_arguments: &occurrence.method_arguments,
            value_type: occurrence.checked_value_type.as_ref(),
            selection: occurrence
                .selection
                .as_ref()
                .ok_or(SelectionFailure::InvalidState)?,
        })
    }

    pub(crate) fn capture_selection(
        &self,
        slot: usize,
        method: Option<MethodId>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(&EvidenceSelection, usize), SelectionFailure> {
        let occurrence = self.occurrence(slot, method, budget)?;
        Ok((occurrence.selection, occurrence.method_arguments.len()))
    }

    /// True absence is distinct from a malformed route for an existing slot.
    pub(crate) fn capture_selection_if_present(
        &self,
        slot: usize,
        method: Option<MethodId>,
        budget: &mut TypeWorkBudget,
    ) -> Result<Option<(&EvidenceSelection, usize)>, SelectionFailure> {
        budget
            .charge(
                self.occurrences
                    .len()
                    .checked_add(1)
                    .ok_or(SelectionFailure::TypeResource)?,
            )
            .map_err(|()| SelectionFailure::TypeResource)?;
        let indexed = self.slot_ids.contains_key(&slot);
        let mut occurrences = self.occurrences.iter().filter(|occurrence| {
            occurrence
                .slot
                .as_ref()
                .is_some_and(|candidate| candidate.storage_id() == slot)
        });
        if occurrences.next().is_none() {
            return if indexed {
                Err(SelectionFailure::InvalidState)
            } else {
                Ok(None)
            };
        }
        if !indexed || occurrences.next().is_some() {
            return Err(SelectionFailure::InvalidState);
        }
        self.capture_selection(slot, method, budget).map(Some)
    }

    /// Relocate private occurrence metadata without publishing any slots.
    /// This compatibility path rewrites type components while retaining row tails.
    #[cfg(test)]
    pub(crate) fn relocate_types<R>(
        &mut self,
        rewrite: R,
        constraints: &mut InterfaceConstraintBudget,
        types: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure>
    where
        R: FnMut(&Type, &mut TypeWorkBudget) -> Result<Type, SelectionFailure>,
    {
        self.relocate_occurrence_types(
            rewrite,
            None::<fn(&EffectRow, &mut TypeWorkBudget) -> Result<EffectRow, SelectionFailure>>,
            constraints,
            types,
        )
    }

    /// Apply one simultaneous owner substitution to all staged occurrence facts.
    /// Both callbacks must implement the same substitution, including nested
    /// type arguments, row tails, and lacks conditions. Original source slots,
    /// selected implementations, prerequisites, and methods remain authoritative.
    pub(crate) fn relocate_types_and_rows<R, Q>(
        &mut self,
        rewrite: R,
        rewrite_row: Q,
        constraints: &mut InterfaceConstraintBudget,
        types: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure>
    where
        R: FnMut(&Type, &mut TypeWorkBudget) -> Result<Type, SelectionFailure>,
        Q: FnMut(&EffectRow, &mut TypeWorkBudget) -> Result<EffectRow, SelectionFailure>,
    {
        self.relocate_occurrence_types(rewrite, Some(rewrite_row), constraints, types)
    }

    /// Relocate private occurrence metadata without publishing any slots.
    fn relocate_occurrence_types<R, Q>(
        &mut self,
        mut rewrite: R,
        mut rewrite_row: Option<Q>,
        constraints: &mut InterfaceConstraintBudget,
        types: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure>
    where
        R: FnMut(&Type, &mut TypeWorkBudget) -> Result<Type, SelectionFailure>,
        Q: FnMut(&EffectRow, &mut TypeWorkBudget) -> Result<EffectRow, SelectionFailure>,
    {
        fn application<R, Q>(
            interface: InterfaceId,
            source: &[KindedArgument],
            rewrite: &mut R,
            rewrite_row: &mut Option<Q>,
            types: &mut TypeWorkBudget,
        ) -> Result<InterfaceApplication, SelectionFailure>
        where
            R: FnMut(&Type, &mut TypeWorkBudget) -> Result<Type, SelectionFailure>,
            Q: FnMut(&EffectRow, &mut TypeWorkBudget) -> Result<EffectRow, SelectionFailure>,
        {
            types
                .charge(source.len())
                .map_err(|()| SelectionFailure::TypeResource)?;
            let mut arguments = EvidenceTypeBuffer(Vec::new());
            arguments
                .0
                .try_reserve_exact(source.len())
                .map_err(|_| SelectionFailure::TypeResource)?;
            for argument in source {
                let relocated = match (argument, rewrite_row.as_mut()) {
                    (KindedArgument::TypeArg(ty), _) => {
                        KindedArgument::TypeArg(rewrite(ty, types)?)
                    }
                    (KindedArgument::RowArg(row), Some(rewrite_row)) => {
                        KindedArgument::RowArg(rewrite_row(row, types)?)
                    }
                    (KindedArgument::RowArg(_), None) => map_kinded_argument_types_with_budget(
                        argument,
                        rewrite,
                        types,
                        &mut |_| (),
                    )?,
                };
                arguments.0.push(relocated);
            }
            Ok(InterfaceApplication::new_kinded(
                interface,
                arguments.into_boxed_slice(),
            ))
        }
        for occurrence in &mut self.occurrences {
            types
                .charge(1)
                .map_err(|()| SelectionFailure::TypeResource)?;
            occurrence.checked_application = application(
                occurrence.checked_application.interface(),
                occurrence.checked_application.arguments(),
                &mut rewrite,
                &mut rewrite_row,
                types,
            )?;
            for argument in &mut occurrence.method_arguments {
                let relocated = rewrite(argument, types)?;
                discard_type_iteratively(std::mem::replace(argument, relocated));
            }
            if let Some(ty) = &mut occurrence.checked_value_type {
                let relocated = rewrite(ty, types)?;
                discard_type_iteratively(std::mem::replace(ty, relocated));
            }
            let source = occurrence
                .selection
                .as_ref()
                .ok_or(SelectionFailure::InvalidState)?;
            let mut builder = crate::interface::EvidenceSelectionBuilder::new();
            constraints
                .charge(
                    source
                        .node_count()
                        .checked_mul(2)
                        .ok_or(SelectionFailure::ConstraintResource)?,
                )
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            let mut pending = Vec::new();
            pending
                .try_reserve(source.node_count())
                .map_err(|_| SelectionFailure::ConstraintResource)?;
            pending.push((source.root(), false));
            let mut remapped = HashMap::new();
            remapped
                .try_reserve(source.node_count())
                .map_err(|_| SelectionFailure::ConstraintResource)?;
            while let Some((node, exit)) = pending.pop() {
                constraints
                    .charge(1)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                if remapped.contains_key(&node) {
                    continue;
                }
                let selected = source.node(node).ok_or(SelectionFailure::InvalidState)?;
                let prerequisites = match selected {
                    crate::interface::EvidenceNode::Implementation { prerequisites, .. }
                    | crate::interface::EvidenceNode::ProviderFamily { prerequisites, .. } => {
                        Some(prerequisites)
                    }
                    _ => None,
                };
                if !exit && let Some(prerequisites) = prerequisites {
                    constraints
                        .charge(prerequisites.len() + 1)
                        .map_err(|()| SelectionFailure::ConstraintResource)?;
                    pending
                        .try_reserve(prerequisites.len() + 1)
                        .map_err(|_| SelectionFailure::ConstraintResource)?;
                    pending.push((node, true));
                    pending.extend(prerequisites.iter().rev().map(|child| (*child, false)));
                    continue;
                }
                let relocated = match selected {
                    crate::interface::EvidenceNode::ProviderFamily {
                        source,
                        definition,
                        parameter,
                        application: goal,
                        prerequisites,
                        methods,
                    } => {
                        constraints
                            .charge(prerequisites.len())
                            .map_err(|()| SelectionFailure::ConstraintResource)?;
                        let mut children = Vec::new();
                        children
                            .try_reserve_exact(prerequisites.len())
                            .map_err(|_| SelectionFailure::ConstraintResource)?;
                        for child in prerequisites {
                            children
                                .push(*remapped.get(child).ok_or(SelectionFailure::InvalidState)?);
                        }
                        let goal = application(
                            goal.interface(),
                            goal.arguments(),
                            &mut rewrite,
                            &mut rewrite_row,
                            types,
                        )?;
                        builder.push_provider_family(
                            source,
                            definition,
                            parameter,
                            goal,
                            &children,
                            methods,
                            constraints,
                        )
                    }
                    crate::interface::EvidenceNode::NativeLayout { producer } => {
                        builder.push_native_layout(producer, constraints)
                    }
                    crate::interface::EvidenceNode::Lexical { source, methods } => {
                        builder.push_lexical(source, methods, constraints)
                    }
                    crate::interface::EvidenceNode::Abstract {
                        requirement,
                        methods,
                    } => builder.push_abstract(requirement, methods, constraints),
                    crate::interface::EvidenceNode::Implementation {
                        implementation,
                        substitution,
                        prerequisites,
                        methods,
                    } => {
                        types
                            .charge(substitution.len())
                            .map_err(|()| SelectionFailure::TypeResource)?;
                        let mut substitutions = Vec::new();
                        substitutions
                            .try_reserve_exact(substitution.len())
                            .map_err(|_| SelectionFailure::TypeResource)?;
                        for replacement in substitution {
                            substitutions.push(crate::interface::EvidenceSubstitution::new(
                                replacement.parameter(),
                                rewrite(replacement.argument(), types)?,
                            ));
                        }
                        constraints
                            .charge(prerequisites.len())
                            .map_err(|()| SelectionFailure::ConstraintResource)?;
                        let mut children = Vec::new();
                        children
                            .try_reserve_exact(prerequisites.len())
                            .map_err(|_| SelectionFailure::ConstraintResource)?;
                        for child in prerequisites {
                            children
                                .push(*remapped.get(child).ok_or(SelectionFailure::InvalidState)?);
                        }
                        builder.push_implementation(
                            implementation,
                            substitutions.into_boxed_slice(),
                            &children,
                            methods,
                            constraints,
                        )
                    }
                }
                .map_err(|()| SelectionFailure::ConstraintResource)?;
                remapped.insert(node, relocated);
            }
            let root = *remapped
                .get(&source.root())
                .ok_or(SelectionFailure::InvalidState)?;
            let goal = application(
                source.interface(),
                source.arguments(),
                &mut rewrite,
                &mut rewrite_row,
                types,
            )?;
            occurrence.selection = Some(
                builder
                    .finish(root, goal)
                    .map_err(|()| SelectionFailure::InvalidState)?,
            );
        }
        Ok(())
    }

    pub(crate) fn contains_expected(
        &self,
        slot: &crate::interface::EvidenceSlot,
        checked_method: Option<MethodId>,
    ) -> bool {
        self.slot_ids.get(&slot.storage_id()) == Some(&checked_method)
    }

    fn preflight(&mut self) -> Result<(), SelectionFailure> {
        if self.occurrences.len() != self.slot_ids.len() {
            return Err(SelectionFailure::InvalidState);
        }
        for occurrence in &self.occurrences {
            let slot = occurrence
                .slot
                .as_ref()
                .ok_or(SelectionFailure::InvalidState)?;
            let slot_id = slot.storage_id();
            if occurrence.selection.is_none()
                || occurrence.checked_method.is_some() != occurrence.checked_value_type.is_some()
                || occurrence.checked_method.is_none() && !occurrence.method_arguments.is_empty()
                || !slot.is_empty()
                || self.slot_ids.remove(&slot_id) != Some(occurrence.checked_method)
            {
                return Err(SelectionFailure::InvalidState);
            }
        }
        if self.slot_ids.is_empty() {
            Ok(())
        } else {
            Err(SelectionFailure::InvalidState)
        }
    }

    /// Preflights the whole batch without filling any source occurrence.
    /// The consuming token permits a joint plan/evidence publication boundary.
    pub(crate) fn prepare_publication(
        mut self,
    ) -> Result<PreflightedEvidencePublication, SelectionFailure> {
        self.preflight()?;
        Ok(PreflightedEvidencePublication { publication: self })
    }

    #[cfg(test)]
    pub(crate) fn publish(self) -> Result<(), SelectionFailure> {
        self.prepare_publication()?.commit();
        Ok(())
    }
}

impl PreflightedEvidencePublication {
    /// Commits the already preflighted batch without allocation, work charges,
    /// or another fallible check. Only this compiler batch may fill its slots.
    pub(crate) fn commit(mut self) {
        while let Some(mut occurrence) = self.publication.occurrences.pop() {
            let interface = occurrence.checked_application.interface();
            let checked_application = std::mem::replace(
                &mut occurrence.checked_application,
                InterfaceApplication::new_kinded(interface, Box::new([])),
            );
            let checked_method = occurrence.checked_method.take();
            let method_arguments = std::mem::take(&mut occurrence.method_arguments);
            let checked_value_type = occurrence.checked_value_type.take();
            let selection = occurrence
                .selection
                .take()
                .expect("publication preflight authenticates every selection");
            occurrence
                .slot
                .take()
                .expect("publication preflight authenticates every slot")
                .fill_preflighted(
                    checked_method,
                    checked_application,
                    method_arguments,
                    checked_value_type,
                    selection,
                );
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct SelectionMethod<'a> {
    interface: InterfaceId,
    interface_parameters: &'a [(TypeVariableId, Kind)],
    type_parameters: &'a [(TypeVariableId, Kind)],
    value_type: &'a Type,
    declaration_span: Span,
}

impl<'a> SelectionMethod<'a> {
    pub(crate) const fn interface(self) -> InterfaceId {
        self.interface
    }

    pub(crate) const fn interface_parameters(self) -> &'a [(TypeVariableId, Kind)] {
        self.interface_parameters
    }

    pub(crate) const fn value_type(self) -> &'a Type {
        self.value_type
    }

    pub(crate) const fn type_parameters(self) -> &'a [(TypeVariableId, Kind)] {
        self.type_parameters
    }

    pub(crate) const fn declaration_span(self) -> Span {
        self.declaration_span
    }
}

/// The owned fact registry, dynamic evidence scope, and pending slot queue.
#[derive(Debug, Default)]
pub(crate) struct EvidenceSelector {
    interfaces: Vec<InterfaceEntry>,
    interface_indices: HashMap<InterfaceId, usize>,
    method_indices: HashMap<MethodId, (usize, usize)>,
    schemes: Vec<SchemeEntry>,
    scheme_indices: HashMap<BinderId, usize>,
    implementations: Vec<ImplementationEntry>,
    implementation_indices: HashMap<ImplId, usize>,
    implementation_candidates: HashMap<InterfaceId, Vec<usize>>,
    abstracts: Vec<RequirementEntry>,
    current: Option<ImplId>,
    lexical_sources: Vec<LexicalSource>,
    lexical_head: Option<usize>,
    pending: Vec<PendingObligation>,
    pending_determined_count: usize,
    pending_method_rigidity_count: usize,
    selected: Vec<SelectedOccurrence>,
    method_rigidities: Vec<SelectedMethodRigidity>,
}

#[derive(Debug)]
struct ScopedProviderFamily {
    definition: crate::resolved::ResourceDefinitionId,
    parameter: TypeVariableId,
    requirements: Box<[RequirementEntry]>,
}

#[derive(Debug)]
struct LexicalSource {
    family: Option<ScopedProviderFamily>,
    id: LexicalEvidenceId,
    parent: Option<usize>,
    application: InterfaceApplication,
    span: Span,
}

struct ImplementationCandidateAuthentication<'a> {
    parameter_records: &'a [ResolvedTypeVariable],
    interfaces: &'a [InterfaceId],
    argument_counts: &'a [usize],
    arguments: &'a [&'a KindedArgument],
    span: Span,
}

impl EvidenceSelector {
    pub(crate) fn new() -> Self {
        Self {
            interfaces: Vec::new(),
            interface_indices: HashMap::new(),
            method_indices: HashMap::new(),
            schemes: Vec::new(),
            scheme_indices: HashMap::new(),
            implementations: Vec::new(),
            implementation_indices: HashMap::new(),
            implementation_candidates: HashMap::new(),
            abstracts: Vec::new(),
            current: None,
            lexical_sources: Vec::new(),
            lexical_head: None,
            pending: Vec::new(),
            pending_determined_count: 0,
            pending_method_rigidity_count: 0,
            selected: Vec::new(),
            method_rigidities: Vec::new(),
        }
    }

    pub(crate) fn add_interface_fact(
        &mut self,
        registry: &ResolvedRegistry,
        fact: &CheckedInterfaceFact,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        self.add_interface_fact_parts(registry, fact, constraint_work, type_work)
    }

    pub(crate) fn add_imported_interface_fact(
        &mut self,
        registry: &ResolvedRegistry,
        fact: &CheckedInterfaceFact,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        self.add_interface_fact_parts(registry, fact, constraint_work, type_work)
    }

    fn add_interface_fact_parts(
        &mut self,
        registry: &ResolvedRegistry,
        fact: &CheckedInterfaceFact,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        if let Some(api) = crate::resolved::ResourceApi::for_module(fact.id.module())
            && !api.interface(fact)
        {
            return Err(SelectionFailure::InvalidState);
        }
        if fact.parameters.is_empty() {
            return Err(SelectionFailure::InvalidState);
        }
        // One retained row is allocated. Checked and summary authentication
        // establish its declaration owner; same-module source ordinals in strict
        // local order establish qualification, uniqueness, and declaration order
        // without a second index.
        constraint_work
            .charge(fact.parameters.len())
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        type_work
            .charge(fact.parameters.len())
            .map_err(|()| SelectionFailure::TypeResource)?;
        let mut parameters = Vec::new();
        parameters
            .try_reserve_exact(fact.parameters.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        let mut previous_parameter = None;
        for parameter in &fact.parameters {
            if parameter.id.module() != Some(fact.id.module())
                || previous_parameter.is_some_and(|previous| parameter.id.local() <= previous)
            {
                return Err(SelectionFailure::InvalidState);
            }
            previous_parameter = Some(parameter.id.local());
            let canonical =
                canonical_type_variable_kind(registry, parameter.id, fact.span, constraint_work)
                    .map_err(map_ingress_kind_failure)?;
            if !same_kind_with_charge(canonical, &parameter.kind, || constraint_work.charge(1))
                .map_err(|()| SelectionFailure::ConstraintResource)?
            {
                return Err(SelectionFailure::InvalidState);
            }
            parameters.push((
                parameter.id,
                clone_kind_with_budget(canonical, type_work)
                    .map_err(|()| SelectionFailure::TypeResource)?,
            ));
        }
        constraint_work
            .charge(fact.methods.len())
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        if self.interface_indices.contains_key(&fact.id) {
            return Err(SelectionFailure::InvalidState);
        }
        let mut incoming_methods = HashSet::new();
        incoming_methods
            .try_reserve(fact.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        for method in &fact.methods {
            if self.method_indices.contains_key(&method.id) || !incoming_methods.insert(method.id) {
                return Err(SelectionFailure::InvalidState);
            }
        }
        let mut methods = Vec::new();
        let mut method_ids = Vec::new();
        methods
            .try_reserve(fact.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        method_ids
            .try_reserve(fact.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        for method in &fact.methods {
            method
                .authenticate_inherited_parameters(
                    crate::resolved::OwnerId::Interface(fact.id),
                    &fact.parameters,
                    type_work,
                )
                .map_err(|failure| match failure {
                    crate::resolved::ResolvedBuildFailure::TypeResource => {
                        SelectionFailure::TypeResource
                    }
                    _ => SelectionFailure::InvalidState,
                })?;
            let method_parameters = method.authoritative_type_parameters();
            let method_parameter_records = method_parameters
                .len()
                .checked_mul(2)
                .ok_or(SelectionFailure::ConstraintResource)?;
            // One retained parameter record and one temporary duplicate-index
            // entry are allocated for every authenticated method binder.
            constraint_work
                .charge(method_parameter_records)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            type_work
                .charge(method_parameters.len())
                .map_err(|()| SelectionFailure::TypeResource)?;
            let mut type_parameters = Vec::new();
            let mut seen = HashSet::new();
            type_parameters
                .try_reserve(method_parameters.len())
                .map_err(|_| SelectionFailure::ConstraintResource)?;
            seen.try_reserve(method_parameters.len())
                .map_err(|_| SelectionFailure::ConstraintResource)?;
            for parameter in method_parameters {
                if parameter.id.module() != Some(fact.id.module())
                    || previous_parameter.is_some_and(|previous| parameter.id.local() <= previous)
                    || !seen.insert(parameter.id)
                {
                    return Err(SelectionFailure::InvalidState);
                }
                let canonical = canonical_type_variable_kind(
                    registry,
                    parameter.id,
                    method.span,
                    constraint_work,
                )
                .map_err(map_ingress_kind_failure)?;
                if !same_kind_with_charge(canonical, &parameter.kind, || constraint_work.charge(1))
                    .map_err(|()| SelectionFailure::ConstraintResource)?
                {
                    return Err(SelectionFailure::InvalidState);
                }
                type_parameters.push((
                    parameter.id,
                    clone_kind_with_budget(canonical, type_work)
                        .map_err(|()| SelectionFailure::TypeResource)?,
                ));
            }
            methods.push(MethodEntry {
                id: method.id,
                type_parameters: type_parameters.into_boxed_slice(),
                // One type preflight owns both traversal and retained-cell
                // charges; no separate count-only worklist is needed.
                value_type: clone_type_with_budget(&method.value_type, &mut |cells| {
                    constraint_work
                        .charge(cells)
                        .map_err(|()| SelectionFailure::ConstraintResource)?;
                    type_work
                        .charge(cells)
                        .map_err(|()| SelectionFailure::TypeResource)
                })?,
                span: method.span,
            });
            method_ids.push(method.id);
        }
        let determination = fact
            .determination()
            .map(|determination| determination.clone_with_budget(constraint_work))
            .transpose()
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        self.interfaces
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.interface_indices
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.method_indices
            .try_reserve(fact.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        let interface_index = self.interfaces.len();
        for (method_index, method) in methods.iter().enumerate() {
            let _ = self
                .method_indices
                .insert(method.id, (interface_index, method_index));
        }
        let _ = self.interface_indices.insert(fact.id, interface_index);
        self.interfaces.push(InterfaceEntry {
            id: fact.id,
            sealed_layout: registry.foreign_layout(fact.id).is_some(),
            parameters: parameters.into_boxed_slice(),
            determination,
            methods: methods.into_boxed_slice(),
            method_ids: method_ids.into_boxed_slice(),
            span: fact.span,
        });
        Ok(())
    }

    pub(crate) fn add_scheme(
        &mut self,
        fact: &CheckedGlobalScheme,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        self.add_scheme_parts(
            fact.binder,
            &fact.scheme,
            fact.origin.primary_span(),
            constraint_work,
            type_work,
        )
    }

    pub(crate) fn add_imported_scheme(
        &mut self,
        fact: &ImportedGlobalScheme,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        self.add_scheme_parts(
            fact.binder,
            &fact.scheme,
            fact.origin.primary_span(),
            constraint_work,
            type_work,
        )
    }

    pub(crate) fn add_completed_provider_scheme(
        &mut self,
        fact: crate::resolved::ProviderGlobalFact<'_>,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        self.add_scheme_parts(
            fact.binder(),
            fact.scheme(),
            fact.origin().primary_span(),
            constraint_work,
            type_work,
        )
    }

    fn add_scheme_parts(
        &mut self,
        binder: BinderId,
        scheme: &ConstrainedScheme,
        declaration_span: Span,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        if self.scheme_indices.contains_key(&binder) {
            return Err(SelectionFailure::InvalidState);
        }
        constraint_work
            .charge(
                scheme
                    .type_parameters
                    .len()
                    .saturating_add(scheme.requirements.len())
                    .saturating_add(1),
            )
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        constraint_work
            .charge_type(&scheme.value_type)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        for requirement in &scheme.requirements {
            for argument in requirement.arguments() {
                constraint_work
                    .charge_argument(argument)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
            }
        }
        let scheme = scheme
            .clone_with_budget(type_work)
            .map_err(|()| SelectionFailure::TypeResource)?;
        self.schemes
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.scheme_indices
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        let scheme_index = self.schemes.len();
        if self.scheme_indices.insert(binder, scheme_index).is_some() {
            return Err(SelectionFailure::InvalidState);
        }
        self.schemes.push(SchemeEntry {
            scheme,
            declaration_span,
        });
        Ok(())
    }

    pub(crate) fn add_implementation_fact(
        &mut self,
        registry: &ResolvedRegistry,
        imported: &ImportedImplementationFact,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        self.add_completed_implementation_parts(
            registry,
            &imported.fact,
            imported.authorization().hops().len(),
            imported
                .authorization()
                .hops()
                .iter()
                .map(|hop| hop.import_span),
            constraint_work,
            type_work,
        )
    }

    pub(crate) fn add_completed_local_implementation_fact(
        &mut self,
        registry: &ResolvedRegistry,
        fact: &crate::resolved::CheckedImplementationFact,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        self.add_completed_implementation_parts(
            registry,
            fact,
            0,
            std::iter::empty(),
            constraint_work,
            type_work,
        )
    }

    fn add_completed_implementation_parts(
        &mut self,
        registry: &ResolvedRegistry,
        fact: &crate::resolved::CheckedImplementationFact,
        import_span_count: usize,
        route_spans: impl Iterator<Item = Span>,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        if fact.interface().module().is_builtin_resource()
            || registry.foreign_layout(fact.interface()).is_some()
        {
            return Err(SelectionFailure::InvalidState);
        }
        if self.implementation_indices.contains_key(&fact.id) {
            return Err(SelectionFailure::InvalidState);
        }
        let relation_count = fact
            .prerequisites
            .len()
            .checked_add(1)
            .ok_or(SelectionFailure::ConstraintResource)?;
        let total_argument_count = fact
            .arguments()
            .len()
            .checked_add(
                fact.prerequisites
                    .iter()
                    .map(|prerequisite| prerequisite.arguments().len())
                    .try_fold(0usize, |sum, count| sum.checked_add(count))
                    .ok_or(SelectionFailure::ConstraintResource)?,
            )
            .ok_or(SelectionFailure::ConstraintResource)?;
        constraint_work
            .charge(
                relation_count
                    .checked_mul(2)
                    .and_then(|work| work.checked_add(total_argument_count))
                    .ok_or(SelectionFailure::ConstraintResource)?,
            )
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut candidate_interfaces = Vec::new();
        let mut candidate_argument_counts = Vec::new();
        let mut candidate_arguments = Vec::new();
        candidate_interfaces
            .try_reserve_exact(relation_count)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        candidate_argument_counts
            .try_reserve_exact(relation_count)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        candidate_arguments
            .try_reserve_exact(total_argument_count)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        candidate_interfaces.push(fact.interface());
        candidate_argument_counts.push(fact.arguments().len());
        candidate_arguments.extend(fact.arguments());
        for prerequisite in &fact.prerequisites {
            candidate_interfaces.push(prerequisite.interface());
            candidate_argument_counts.push(prerequisite.arguments().len());
            candidate_arguments.extend(prerequisite.arguments());
        }
        let parameters = self.authenticate_implementation_candidate(
            registry,
            ImplementationCandidateAuthentication {
                parameter_records: &fact.head_parameters,
                interfaces: &candidate_interfaces,
                argument_counts: &candidate_argument_counts,
                arguments: &candidate_arguments,
                span: fact.span,
            },
            constraint_work,
        )?;
        constraint_work
            .charge(
                fact.head_parameters
                    .len()
                    .saturating_add(fact.prerequisites.len())
                    .saturating_add(fact.methods.len().saturating_mul(2))
                    .saturating_add(import_span_count)
                    .saturating_add(1),
            )
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        for argument in fact.arguments() {
            constraint_work
                .charge_argument(argument)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
        }
        let mut prerequisites = Vec::new();
        let mut methods = Vec::new();
        let mut method_spans = Vec::new();
        let mut import_spans = Vec::new();
        prerequisites
            .try_reserve(fact.prerequisites.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        methods
            .try_reserve(fact.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        method_spans
            .try_reserve(fact.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        import_spans
            .try_reserve_exact(import_span_count)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        let staged_candidate_bucket = self.reserve_implementation_publication(fact.interface())?;
        for prerequisite in &fact.prerequisites {
            for argument in prerequisite.arguments() {
                constraint_work
                    .charge_argument(argument)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
            }
            prerequisites.push(RequirementEntry {
                id: prerequisite.id,
                application: prerequisite
                    .application()
                    .clone_with_budget(type_work)
                    .map_err(|()| SelectionFailure::TypeResource)?,
                span: prerequisite.span,
            });
        }
        methods.extend(fact.methods.iter().map(|method| method.id));
        method_spans.extend(fact.methods.iter().map(|method| method.span));
        import_spans.extend(route_spans);
        let entry = ImplementationEntry {
            id: fact.id,
            application: fact
                .application()
                .clone_with_budget(type_work)
                .map_err(|()| SelectionFailure::TypeResource)?,
            parameters: parameters.into_boxed_slice(),
            prerequisites: prerequisites.into_boxed_slice(),
            methods: methods.into_boxed_slice(),
            span: fact.span,
            method_spans,
            import_spans: import_spans.into_boxed_slice(),
        };
        self.publish_implementation(entry, staged_candidate_bucket)?;
        Ok(())
    }

    pub(crate) fn add_local_implementation(
        &mut self,
        registry: &ResolvedRegistry,
        resolved: &ResolvedImplementation,
        checked: &CheckedImplementation,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        constraint_work
            .charge(resolved.prerequisites.len().saturating_add(1))
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        if resolved.id != checked.id
            || checked.interface().module().is_builtin_resource()
            || registry.foreign_layout(checked.interface()).is_some()
            || resolved.head.interface.id != checked.interface()
            || resolved.head.arguments.len() != checked.arguments().len()
            || !resolved.prerequisite_only_parameters.is_empty()
            || checked.methods.len() != resolved.method_groups.len()
        {
            return Err(SelectionFailure::InvalidState);
        }
        for (resolved_argument, checked_argument) in
            resolved.head.arguments.iter().zip(checked.arguments())
        {
            if !same_kinded_argument_with_constraint_budget(
                &resolved_argument.ty,
                checked_argument,
                constraint_work,
            )
            .map_err(|()| SelectionFailure::ConstraintResource)?
            {
                return Err(SelectionFailure::InvalidState);
            }
        }
        if self.implementation_indices.contains_key(&checked.id) {
            return Err(SelectionFailure::InvalidState);
        }
        let relation_count = resolved
            .prerequisites
            .len()
            .checked_add(1)
            .ok_or(SelectionFailure::ConstraintResource)?;
        let total_argument_count = resolved
            .head
            .arguments
            .len()
            .checked_add(
                resolved
                    .prerequisites
                    .iter()
                    .map(|prerequisite| prerequisite.application.arguments.len())
                    .try_fold(0usize, |sum, count| sum.checked_add(count))
                    .ok_or(SelectionFailure::ConstraintResource)?,
            )
            .ok_or(SelectionFailure::ConstraintResource)?;
        constraint_work
            .charge(
                relation_count
                    .checked_mul(2)
                    .and_then(|work| work.checked_add(total_argument_count))
                    .ok_or(SelectionFailure::ConstraintResource)?,
            )
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut candidate_interfaces = Vec::new();
        let mut candidate_argument_counts = Vec::new();
        let mut candidate_arguments = Vec::new();
        candidate_interfaces
            .try_reserve_exact(relation_count)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        candidate_argument_counts
            .try_reserve_exact(relation_count)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        candidate_arguments
            .try_reserve_exact(total_argument_count)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        candidate_interfaces.push(resolved.head.interface.id);
        candidate_argument_counts.push(resolved.head.arguments.len());
        candidate_arguments.extend(resolved.head.arguments.iter().map(|argument| &argument.ty));
        for prerequisite in &resolved.prerequisites {
            candidate_interfaces.push(prerequisite.application.interface.id);
            candidate_argument_counts.push(prerequisite.application.arguments.len());
            candidate_arguments.extend(
                prerequisite
                    .application
                    .arguments
                    .iter()
                    .map(|argument| &argument.ty),
            );
        }
        let parameters = self.authenticate_implementation_candidate(
            registry,
            ImplementationCandidateAuthentication {
                parameter_records: &resolved.head_parameters,
                interfaces: &candidate_interfaces,
                argument_counts: &candidate_argument_counts,
                arguments: &candidate_arguments,
                span: resolved.span,
            },
            constraint_work,
        )?;
        constraint_work
            .charge(
                resolved
                    .head_parameters
                    .len()
                    .saturating_add(checked.methods.len().saturating_mul(2)),
            )
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut method_spans = Vec::new();
        method_spans
            .try_reserve(checked.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        for method in &checked.methods {
            let source = resolved
                .method_groups
                .get(method.source_group)
                .ok_or(SelectionFailure::InvalidState)?;
            if source.identity != Some(method.id)
                || source.method != Some(method.method)
                || source.binder.id != method.binder
                || method.id.implementation() != checked.id
                || method.id.method() != method.method
            {
                return Err(SelectionFailure::InvalidState);
            }
            method_spans.push(source.span);
        }
        for argument in &resolved.head.arguments {
            constraint_work
                .charge_argument(&argument.ty)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
        }
        let mut prerequisites = Vec::new();
        let mut methods = Vec::new();
        prerequisites
            .try_reserve(resolved.prerequisites.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        methods
            .try_reserve(checked.methods.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        let staged_candidate_bucket =
            self.reserve_implementation_publication(checked.interface())?;
        for prerequisite in &resolved.prerequisites {
            for argument in &prerequisite.application.arguments {
                constraint_work
                    .charge_argument(&argument.ty)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
            }
            let application_arguments =
                clone_local_prerequisite_arguments(&prerequisite.application.arguments, type_work)?;
            prerequisites.push(RequirementEntry {
                id: prerequisite.id,
                application: InterfaceApplication::new_kinded(
                    prerequisite.application.interface.id,
                    application_arguments.into_boxed_slice(),
                ),
                span: prerequisite.application.span,
            });
        }
        methods.extend(checked.methods.iter().map(|method| method.id));
        let entry = ImplementationEntry {
            id: checked.id,
            application: checked
                .application()
                .clone_with_budget(type_work)
                .map_err(|()| SelectionFailure::TypeResource)?,
            parameters: parameters.into_boxed_slice(),
            prerequisites: prerequisites.into_boxed_slice(),
            methods: methods.into_boxed_slice(),
            span: resolved.span,
            method_spans,
            import_spans: Box::new([]),
        };
        self.publish_implementation(entry, staged_candidate_bucket)?;
        Ok(())
    }

    /// Reserves every selector destination before retained implementation Types
    /// are cloned. A new candidate bucket stays local until publication.
    fn reserve_implementation_publication(
        &mut self,
        interface: InterfaceId,
    ) -> Result<Option<Vec<usize>>, SelectionFailure> {
        self.implementations
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.implementation_indices
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        if let Some(candidates) = self.implementation_candidates.get_mut(&interface) {
            candidates
                .try_reserve(1)
                .map_err(|_| SelectionFailure::ConstraintResource)?;
            return Ok(None);
        }
        self.implementation_candidates
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        let mut candidates = Vec::new();
        candidates
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        Ok(Some(candidates))
    }

    /// Publishes a fully authenticated and retained implementation without any
    /// remaining fallible allocation or validation.
    fn publish_implementation(
        &mut self,
        entry: ImplementationEntry,
        staged_candidate_bucket: Option<Vec<usize>>,
    ) -> Result<(), SelectionFailure> {
        let implementation_index = self.implementations.len();
        let interface = entry.application.interface();
        let implementation = entry.id;
        if self.implementation_indices.contains_key(&implementation) {
            return Err(SelectionFailure::InvalidState);
        }
        if staged_candidate_bucket.is_some()
            == self.implementation_candidates.contains_key(&interface)
        {
            return Err(SelectionFailure::InvalidState);
        }
        if staged_candidate_bucket.is_none() {
            self.implementation_candidates
                .get_mut(&interface)
                .ok_or(SelectionFailure::InvalidState)?
                .push(implementation_index);
        }
        self.implementations.push(entry);
        let displaced = self
            .implementation_indices
            .insert(implementation, implementation_index);
        debug_assert!(displaced.is_none());
        if let Some(mut candidates) = staged_candidate_bucket {
            candidates.push(implementation_index);
            let displaced = self.implementation_candidates.insert(interface, candidates);
            debug_assert!(displaced.is_none());
        }
        Ok(())
    }

    pub(crate) fn method(&self, id: MethodId) -> Option<SelectionMethod<'_>> {
        let (interface_index, method_index) = *self.method_indices.get(&id)?;
        let interface = self.interfaces.get(interface_index)?;
        let method = interface.methods.get(method_index)?;
        Some(SelectionMethod {
            interface: interface.id,
            interface_parameters: &interface.parameters,
            type_parameters: &method.type_parameters,
            value_type: &method.value_type,
            declaration_span: method.span,
        })
    }

    pub(crate) fn scheme(&self, binder: BinderId) -> Option<&ConstrainedScheme> {
        let index = *self.scheme_indices.get(&binder)?;
        self.schemes.get(index).map(|entry| &entry.scheme)
    }

    pub(crate) fn scheme_declaration_span(&self, binder: BinderId) -> Option<Span> {
        let index = *self.scheme_indices.get(&binder)?;
        let entry = self.schemes.get(index)?;
        Some(entry.declaration_span)
    }

    pub(crate) fn clear_scope(&mut self) {
        self.abstracts.clear();
        self.current = None;
        self.lexical_head = None;
    }

    pub(crate) const fn lexical_head(&self) -> Option<usize> {
        self.lexical_head
    }

    pub(crate) fn restore_lexical_head(&mut self, head: Option<usize>) {
        self.lexical_head = head;
    }

    #[allow(
        clippy::type_complexity,
        reason = "borrows canonical method order, optional key positions, and declaration span"
    )]
    pub(crate) fn lexical_interface(
        &self,
        interface: InterfaceId,
    ) -> Option<(&[MethodId], Option<&[usize]>, Span)> {
        let entry = self.interface_entry(interface).ok()?;
        Some((
            &entry.method_ids,
            entry.determination.as_ref().map(|key| key.positions()),
            entry.span,
        ))
    }

    pub(crate) fn check_lexical_key(
        &self,
        application: &InterfaceApplication,
        constraint_work: &mut InterfaceConstraintBudget,
    ) -> Result<Option<(InterfaceReason, Span)>, SelectionFailure> {
        let interface = self.interface_entry(application.interface())?;
        let mut head = self.lexical_head;
        while let Some(index) = head {
            constraint_work
                .charge(1)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            let source = self
                .lexical_sources
                .get(index)
                .ok_or(SelectionFailure::InvalidState)?;
            head = source.parent;
            if source.family.is_some() || source.application.interface() != application.interface()
            {
                continue;
            }
            let same_key = if let Some(key) = &interface.determination {
                let mut equal = true;
                for &position in key.positions() {
                    let old = source
                        .application
                        .arguments()
                        .get(position)
                        .ok_or(SelectionFailure::InvalidState)?;
                    let new = application
                        .arguments()
                        .get(position)
                        .ok_or(SelectionFailure::InvalidState)?;
                    equal &= same_kinded_argument_with_constraint_budget(old, new, constraint_work)
                        .map_err(|()| SelectionFailure::ConstraintResource)?;
                }
                equal
            } else {
                same_applications_with_constraint_budget(
                    &source.application,
                    application,
                    constraint_work,
                )?
            };
            if same_key {
                let reason = if same_applications_with_constraint_budget(
                    &source.application,
                    application,
                    constraint_work,
                )? {
                    InterfaceReason::EvidenceDuplicate
                } else {
                    InterfaceReason::EvidenceDeterminationConflict
                };
                return Ok(Some((reason, source.span)));
            }
        }
        Ok(None)
    }

    pub(crate) fn add_lexical_source(
        &mut self,
        id: LexicalEvidenceId,
        application: InterfaceApplication,
        span: Span,
        constraint_work: &mut InterfaceConstraintBudget,
    ) -> Result<(), SelectionFailure> {
        if self.interface_entry(application.interface())?.sealed_layout {
            return Err(SelectionFailure::InvalidState);
        }
        constraint_work
            .charge(2)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        for argument in application.arguments() {
            constraint_work
                .charge_argument(argument)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
        }
        self.lexical_sources
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        let index = self.lexical_sources.len();
        self.lexical_sources.push(LexicalSource {
            family: None,
            id,
            parent: self.lexical_head,
            application,
            span,
        });
        self.lexical_head = Some(index);
        Ok(())
    }

    pub(crate) fn method_rigidity_count(&self) -> usize {
        self.method_rigidities.len()
    }

    pub(crate) fn method_rigidity(&self, index: usize) -> Option<MethodRigidityCheck<'_>> {
        let selected = self.method_rigidities.get(index)?;
        let occurrence = self.selected.get(selected.selected_index)?;
        Some(MethodRigidityCheck {
            method_arguments: &occurrence.method_arguments,
            rigid_arguments: &selected.condition.rigid_arguments,
            site: selected.condition.site,
        })
    }

    pub(crate) fn clear_method_rigidities(&mut self) {
        self.method_rigidities.clear();
    }

    pub(crate) fn enter_global_scope(
        &mut self,
        binder: BinderId,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        let scheme = self.scheme(binder).ok_or(SelectionFailure::InvalidState)?;
        let mut abstracts = Vec::new();
        constraint_work
            .charge(scheme.requirements.len())
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        abstracts
            .try_reserve(scheme.requirements.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        for requirement in &scheme.requirements {
            constraint_work
                .charge(1)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            for argument in requirement.arguments() {
                constraint_work
                    .charge_argument(argument)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
            }
            abstracts.push(RequirementEntry {
                id: requirement.id,
                application: requirement
                    .application()
                    .clone_with_budget(type_work)
                    .map_err(|()| SelectionFailure::TypeResource)?,
                span: requirement.span,
            });
        }
        self.abstracts = abstracts;
        self.current = None;
        Ok(())
    }

    pub(crate) fn enter_family_scope(
        &mut self,
        definition: crate::resolved::ResourceDefinitionId,
        requirements: &[crate::interface::CheckedRequirement],
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        constraint_work
            .charge(requirements.len())
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut abstracts = Vec::new();
        abstracts
            .try_reserve_exact(requirements.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        for (ordinal, requirement) in requirements.iter().enumerate() {
            if requirement.id.owner()
                != crate::interface::RequirementOwner::ResourceFamily(definition)
                || usize::try_from(requirement.id.declaration()).ok() != Some(ordinal)
            {
                return Err(SelectionFailure::InvalidState);
            }
            for argument in requirement.arguments() {
                constraint_work
                    .charge_argument(argument)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
            }
            abstracts.push(RequirementEntry {
                id: requirement.id,
                application: requirement
                    .application()
                    .clone_with_budget(type_work)
                    .map_err(|()| SelectionFailure::TypeResource)?,
                span: requirement.span,
            });
        }
        self.abstracts = abstracts;
        self.current = None;
        Ok(())
    }

    #[allow(clippy::too_many_arguments)] // Original family identity and complete substituted header remain separate.
    pub(crate) fn add_scoped_family(
        &mut self,
        id: LexicalEvidenceId,
        definition: crate::resolved::ResourceDefinitionId,
        parameter: TypeVariableId,
        application: InterfaceApplication,
        requirements: &[crate::interface::CheckedRequirement],
        span: Span,
        constraints: &mut InterfaceConstraintBudget,
        types: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        if self.interface_entry(application.interface())?.sealed_layout {
            return Err(SelectionFailure::InvalidState);
        }
        constraints
            .charge(
                requirements
                    .len()
                    .checked_add(2)
                    .ok_or(SelectionFailure::ConstraintResource)?,
            )
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut copied = Vec::new();
        copied
            .try_reserve_exact(requirements.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        for (ordinal, requirement) in requirements.iter().enumerate() {
            if requirement.id.owner()
                != crate::interface::RequirementOwner::ResourceFamily(definition)
                || usize::try_from(requirement.id.declaration()).ok() != Some(ordinal)
            {
                return Err(SelectionFailure::InvalidState);
            }
            for argument in requirement.arguments() {
                constraints
                    .charge_argument(argument)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
            }
            copied.push(RequirementEntry {
                id: requirement.id,
                application: requirement
                    .application()
                    .clone_with_budget(types)
                    .map_err(|()| SelectionFailure::TypeResource)?,
                span: requirement.span,
            });
        }
        for argument in application.arguments() {
            constraints
                .charge_argument(argument)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
        }
        self.lexical_sources
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        let index = self.lexical_sources.len();
        self.lexical_sources.push(LexicalSource {
            id,
            parent: self.lexical_head,
            application,
            span,
            family: Some(ScopedProviderFamily {
                definition,
                parameter,
                requirements: copied.into_boxed_slice(),
            }),
        });
        self.lexical_head = Some(index);
        Ok(())
    }

    pub(crate) fn enter_implementation_scope(
        &mut self,
        implementation: ImplId,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        let implementation_index = *self
            .implementation_indices
            .get(&implementation)
            .ok_or(SelectionFailure::InvalidState)?;
        let implementation = self
            .implementations
            .get(implementation_index)
            .ok_or(SelectionFailure::InvalidState)?;
        let mut abstracts = Vec::new();
        constraint_work
            .charge(implementation.prerequisites.len())
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        abstracts
            .try_reserve(implementation.prerequisites.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        for prerequisite in &implementation.prerequisites {
            constraint_work
                .charge(1)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            for argument in prerequisite.application.arguments() {
                constraint_work
                    .charge_argument(argument)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
            }
            abstracts.push(RequirementEntry {
                id: prerequisite.id,
                application: prerequisite
                    .application
                    .clone_with_budget(type_work)
                    .map_err(|()| SelectionFailure::TypeResource)?,
                span: prerequisite.span,
            });
        }
        self.abstracts = abstracts;
        self.current = Some(implementation.id);
        Ok(())
    }

    #[cfg(test)]
    pub(crate) fn push_abstract(
        &mut self,
        id: RequirementId,
        interface: InterfaceId,
        argument: Type,
        constraint_work: &mut InterfaceConstraintBudget,
    ) -> Result<(), SelectionFailure> {
        let argument = IterativeTypeOwner::new(argument);
        constraint_work
            .charge(1)
            .and_then(|()| constraint_work.charge_type(&argument))
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let span = self.interface_entry(interface)?.span;
        self.abstracts
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.abstracts.push(RequirementEntry {
            id,
            application: InterfaceApplication::new_kinded(
                interface,
                Box::new([KindedArgument::TypeArg(argument.into_inner())]),
            ),
            span,
        });
        Ok(())
    }

    pub(crate) const fn pending_marker(&self) -> PendingObligationMarker {
        PendingObligationMarker {
            pending_len: self.pending.len(),
            determined_count: self.pending_determined_count,
        }
    }

    fn interface_is_determined(&self, interface: InterfaceId) -> bool {
        self.interface_indices
            .get(&interface)
            .and_then(|index| self.interfaces.get(*index))
            .is_some_and(|entry| entry.determination.is_some())
    }

    fn pending_suffix_counts(
        &self,
        marker: PendingObligationMarker,
    ) -> Result<(usize, usize), SelectionFailure> {
        if marker.determined_count > marker.pending_len
            || self.pending_determined_count > self.pending.len()
        {
            return Err(SelectionFailure::InvalidState);
        }
        let pending_count = self
            .pending
            .len()
            .checked_sub(marker.pending_len)
            .ok_or(SelectionFailure::InvalidState)?;
        let determined_count = self
            .pending_determined_count
            .checked_sub(marker.determined_count)
            .ok_or(SelectionFailure::InvalidState)?;
        if determined_count > pending_count {
            return Err(SelectionFailure::InvalidState);
        }
        Ok((pending_count, determined_count))
    }

    #[cfg(test)]
    pub(crate) fn push_obligation(
        &mut self,
        interface: InterfaceId,
        argument: Type,
        slot: EvidenceSlotHandle,
        span: Span,
        constraint_work: &mut InterfaceConstraintBudget,
    ) -> Result<(), SelectionFailure> {
        self.push_owned_obligation(
            InterfaceApplication::new_kinded(
                interface,
                Box::new([KindedArgument::TypeArg(argument)]),
            ),
            SelectionSite::plain(slot, span),
            constraint_work,
        )
    }

    pub(crate) fn push_owned_obligation(
        &mut self,
        application: InterfaceApplication,
        site: SelectionSite,
        constraint_work: &mut InterfaceConstraintBudget,
    ) -> Result<(), SelectionFailure> {
        let pending_determined_count = if self.interface_is_determined(application.interface()) {
            self.pending_determined_count
                .checked_add(1)
                .ok_or(SelectionFailure::ConstraintResource)?
        } else {
            self.pending_determined_count
        };
        constraint_work
            .charge(1 + usize::from(self.lexical_head.is_some()))
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        for argument in application.arguments() {
            constraint_work
                .charge_argument(argument)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
        }
        self.pending
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.pending.push(PendingObligation {
            checked_method: None,
            lexical_head: self.lexical_head,
            application,
            method_arguments: Box::new([]),
            checked_value_type: None,
            method_rigidity: None,
            slot: site.slot,
            span: site.span,
            declaration_span: site.declaration_span,
            import_span: site.import_span,
        });
        self.pending_determined_count = pending_determined_count;
        Ok(())
    }

    pub(crate) fn push_cloned_obligation(
        &mut self,
        application: &InterfaceApplication,
        metadata: MethodObligationMetadata,
        site: SelectionSite,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionFailure> {
        if metadata.method_rigidity.as_ref().is_some_and(|rigidity| {
            rigidity.rigid_arguments.len() != metadata.method_arguments.len()
        }) {
            return Err(SelectionFailure::InvalidState);
        }
        let pending_method_rigidity_count = if metadata.method_rigidity.is_some() {
            self.pending_method_rigidity_count
                .checked_add(1)
                .ok_or(SelectionFailure::ConstraintResource)?
        } else {
            self.pending_method_rigidity_count
        };
        let pending_determined_count = if self.interface_is_determined(application.interface()) {
            self.pending_determined_count
                .checked_add(1)
                .ok_or(SelectionFailure::ConstraintResource)?
        } else {
            self.pending_determined_count
        };
        let rigidity_work = match &metadata.method_rigidity {
            Some(rigidity) => rigidity
                .rigid_arguments
                .len()
                .checked_add(1)
                .ok_or(SelectionFailure::ConstraintResource)?,
            None => 0,
        };
        let retained_work = metadata
            .method_arguments
            .len()
            .checked_add(2)
            .and_then(|work| work.checked_add(rigidity_work))
            .and_then(|work| work.checked_add(usize::from(metadata.checked_value_type.is_some())))
            .and_then(|work| work.checked_add(usize::from(self.lexical_head.is_some())))
            .ok_or(SelectionFailure::ConstraintResource)?;
        constraint_work
            .charge(retained_work)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        for argument in application.arguments() {
            constraint_work
                .charge_argument(argument)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
        }
        for method_argument in &metadata.method_arguments {
            constraint_work
                .charge_type(method_argument)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
        }
        if let Some(checked_value_type) = &metadata.checked_value_type {
            constraint_work
                .charge_type(checked_value_type)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
        }
        let application = application
            .clone_with_budget(type_work)
            .map_err(|()| SelectionFailure::TypeResource)?;
        self.pending
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        let (checked_method, method_arguments, checked_value_type, method_rigidity) =
            metadata.into_parts();
        self.pending.push(PendingObligation {
            checked_method: Some(checked_method),
            lexical_head: self.lexical_head,
            application,
            method_arguments,
            checked_value_type,
            method_rigidity,
            slot: site.slot,
            span: site.span,
            declaration_span: site.declaration_span,
            import_span: site.import_span,
        });
        self.pending_determined_count = pending_determined_count;
        self.pending_method_rigidity_count = pending_method_rigidity_count;
        Ok(())
    }

    pub(crate) fn prepare_determination_snapshot<F>(
        &self,
        registry: &ResolvedRegistry,
        marker: PendingObligationMarker,
        mut zonk: F,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<DeterminationSnapshot, SelectionFailure>
    where
        F: FnMut(KindedArgument, &mut TypeWorkBudget) -> Result<KindedArgument, SelectionFailure>,
    {
        let (pending_count, determined_count) = self.pending_suffix_counts(marker)?;
        if determined_count == 0 {
            return Ok(DeterminationSnapshot {
                marker,
                eligible: Box::new([]),
                tasks: Vec::new(),
            });
        }
        constraint_work
            .charge(
                pending_count
                    .checked_mul(2)
                    .ok_or(SelectionFailure::ConstraintResource)?,
            )
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut eligible = Vec::new();
        let mut tasks = Vec::new();
        eligible
            .try_reserve_exact(pending_count)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        tasks
            .try_reserve(pending_count)
            .map_err(|_| SelectionFailure::ConstraintResource)?;

        for obligation in &self.pending[marker.pending_len..] {
            constraint_work
                .charge(1)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            let interface = self.interface_entry(obligation.application.interface())?;
            if interface.determination.is_none() {
                eligible.push(true);
                continue;
            }
            let (key_is_complete, task) = self.prepare_obligation_improvement(
                registry,
                interface,
                obligation,
                &mut zonk,
                constraint_work,
                type_work,
            )?;
            eligible.push(key_is_complete);
            if let Some(task) = task {
                tasks.push(task);
            }
        }
        Ok(DeterminationSnapshot {
            marker,
            eligible: eligible.into_boxed_slice(),
            tasks,
        })
    }

    pub(crate) fn prepare_method_rigidity_determination<F>(
        &self,
        registry: &ResolvedRegistry,
        target: MethodRigidityTarget,
        mut zonk: F,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<MethodRigidityDeterminationSnapshot, SelectionFailure>
    where
        F: FnMut(KindedArgument, &mut TypeWorkBudget) -> Result<KindedArgument, SelectionFailure>,
    {
        let (pending_count, _) = self.pending_suffix_counts(target.marker)?;
        if !self.method_rigidities.is_empty() {
            return Err(SelectionFailure::InvalidState);
        }
        if self.pending_method_rigidity_count == 0 {
            return Ok(MethodRigidityDeterminationSnapshot {
                target,
                matching_index: None,
                determined: false,
                eligible: true,
                task: None,
            });
        }
        constraint_work
            .charge(pending_count)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let matching_index = self.matching_method_rigidity_index(target)?;
        let Some(matching_index) = matching_index else {
            return Ok(MethodRigidityDeterminationSnapshot {
                target,
                matching_index: None,
                determined: false,
                eligible: true,
                task: None,
            });
        };
        let obligation = self
            .pending
            .get(matching_index)
            .ok_or(SelectionFailure::InvalidState)?;
        let interface = self.interface_entry(obligation.application.interface())?;
        if interface.determination.is_none() {
            return Ok(MethodRigidityDeterminationSnapshot {
                target,
                matching_index: Some(matching_index),
                determined: false,
                eligible: true,
                task: None,
            });
        }
        let (eligible, task) = self.prepare_obligation_improvement(
            registry,
            interface,
            obligation,
            &mut zonk,
            constraint_work,
            type_work,
        )?;
        Ok(MethodRigidityDeterminationSnapshot {
            target,
            matching_index: Some(matching_index),
            determined: true,
            eligible,
            task,
        })
    }

    fn prepare_obligation_improvement<F>(
        &self,
        registry: &ResolvedRegistry,
        interface: &InterfaceEntry,
        obligation: &PendingObligation,
        zonk: &mut F,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(bool, Option<ImprovementTask>), SelectionFailure>
    where
        F: FnMut(KindedArgument, &mut TypeWorkBudget) -> Result<KindedArgument, SelectionFailure>,
    {
        let determination = interface
            .determination
            .as_ref()
            .ok_or(SelectionFailure::InvalidState)?;
        authenticate_determination_positions(
            determination.positions(),
            obligation.application.arguments().len(),
            constraint_work,
        )?;
        let key = clone_zonked_positions(
            obligation.application.arguments(),
            determination.positions(),
            zonk,
            constraint_work,
            type_work,
        )?;
        let key_is_complete = key.0.iter().try_fold(true, |complete, ty| {
            if !complete {
                return Ok(false);
            }
            type_is_inference_free(ty, constraint_work)
        })?;
        if !key_is_complete {
            return Ok((false, None));
        }
        let Some((expected_dependents, source_span)) = self.improvement_source(
            registry,
            interface,
            &key.0,
            obligation.lexical_head,
            constraint_work,
            type_work,
        )?
        else {
            return Ok((true, None));
        };
        let actual_dependents = clone_dependent_positions(
            obligation.application.arguments(),
            determination.positions(),
            type_work,
        )?;
        if expected_dependents.0.len() != actual_dependents.0.len()
            || expected_dependents.0.is_empty()
        {
            return Err(SelectionFailure::InvalidState);
        }
        constraint_work
            .charge(1)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        Ok((
            true,
            Some(ImprovementTask {
                key: key.into_boxed_slice(),
                expected_dependents: expected_dependents.into_boxed_slice(),
                actual_dependents: actual_dependents.into_boxed_slice(),
                obligation_span: obligation.span,
                source_span,
            }),
        ))
    }

    fn improvement_source(
        &self,
        registry: &ResolvedRegistry,
        interface: &InterfaceEntry,
        key: &[KindedArgument],
        lexical_head: Option<usize>,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<Option<(EvidenceTypeBuffer, Span)>, SelectionFailure> {
        let determination = interface
            .determination
            .as_ref()
            .ok_or(SelectionFailure::InvalidState)?;
        for requirement in &self.abstracts {
            constraint_work
                .charge(1)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            if requirement.application.interface() != interface.id {
                continue;
            }
            let requirement_key = position_references(
                requirement.application.arguments(),
                determination.positions(),
                constraint_work,
            )?;
            if same_type_slices(&requirement_key, key, constraint_work)? {
                return clone_dependent_positions(
                    requirement.application.arguments(),
                    determination.positions(),
                    type_work,
                )
                .map(|dependents| Some((dependents, requirement.span)));
            }
        }

        if let Some(current) = self.current {
            constraint_work
                .charge(1)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            let implementation = self
                .implementation_indices
                .get(&current)
                .and_then(|index| self.implementations.get(*index))
                .ok_or(SelectionFailure::InvalidState)?;
            if implementation.application.interface() == interface.id {
                let current_key = position_references(
                    implementation.application.arguments(),
                    determination.positions(),
                    constraint_work,
                )?;
                if same_type_slices(&current_key, key, constraint_work)? {
                    return clone_dependent_positions(
                        implementation.application.arguments(),
                        determination.positions(),
                        type_work,
                    )
                    .map(|dependents| Some((dependents, implementation.span)));
                }
            }
        }

        let mut head = lexical_head;
        while let Some(index) = head {
            constraint_work
                .charge(1)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            let source = self
                .lexical_sources
                .get(index)
                .ok_or(SelectionFailure::InvalidState)?;
            head = source.parent;
            if source.family.is_some() || source.application.interface() != interface.id {
                continue;
            }
            let source_key = position_references(
                source.application.arguments(),
                determination.positions(),
                constraint_work,
            )?;
            if same_type_slices(&source_key, key, constraint_work)? {
                return clone_dependent_positions(
                    source.application.arguments(),
                    determination.positions(),
                    type_work,
                )
                .map(|dependents| Some((dependents, source.span)));
            }
        }
        let key_references = type_references(key, constraint_work)?;
        let canonical_goal = authenticate_implementation_application_goal(
            registry,
            InterfaceOperationWork::new(interface.span, constraint_work, type_work),
            &key_references,
        )
        .map_err(map_head_failure)?;
        let mut matched = None;
        let candidates = self
            .implementation_candidates
            .get(&interface.id)
            .map(Vec::as_slice)
            .unwrap_or_default();
        for &candidate_index in candidates {
            charge_candidate_inspection(constraint_work)?;
            let implementation = self
                .implementations
                .get(candidate_index)
                .ok_or(SelectionFailure::InvalidState)?;
            if Some(implementation.id) == self.current {
                continue;
            }
            let candidate_key = position_references(
                implementation.application.arguments(),
                determination.positions(),
                constraint_work,
            )?;
            let Some(substitution) = match_implementation_application_head_against_canonical_goal(
                registry,
                InterfaceOperationWork::new(implementation.span, constraint_work, type_work),
                &implementation.parameters,
                &candidate_key,
                &canonical_goal,
            )
            .map_err(map_head_failure)?
            else {
                continue;
            };
            if matched.is_some() {
                return Err(SelectionFailure::InvalidState);
            }
            let replacements = replacement_map(&substitution, type_work)?;
            let dependents = substitute_dependent_positions(
                implementation.application.arguments(),
                determination.positions(),
                replacements.as_map(),
                type_work,
            )?;
            matched = Some((dependents, implementation.span));
        }
        Ok(matched)
    }

    pub(crate) fn close_with_snapshot_and_registry<F>(
        &mut self,
        registry: &ResolvedRegistry,
        marker: PendingObligationMarker,
        snapshot: &DeterminationSnapshot,
        zonk: F,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionError>
    where
        F: FnMut(KindedArgument, &mut TypeWorkBudget) -> Result<KindedArgument, SelectionFailure>,
    {
        self.close_with_authority(
            registry,
            marker,
            Some(snapshot),
            zonk,
            constraint_work,
            type_work,
        )
    }

    #[cfg(test)]
    pub(crate) fn close_with_registry<F>(
        &mut self,
        registry: &ResolvedRegistry,
        marker: PendingObligationMarker,
        mut zonk: F,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionError>
    where
        F: FnMut(KindedArgument, &mut TypeWorkBudget) -> Result<KindedArgument, SelectionFailure>,
    {
        let mut snapshot = self
            .prepare_determination_snapshot(registry, marker, &mut zonk, constraint_work, type_work)
            .map_err(|failure| SelectionError {
                failure,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })?;
        if !snapshot.tasks.is_empty() {
            return Err(SelectionError {
                failure: SelectionFailure::InvalidState,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            });
        }
        snapshot.tasks.clear();
        self.close_with_authority(
            registry,
            marker,
            Some(&snapshot),
            &mut zonk,
            constraint_work,
            type_work,
        )
    }

    #[cfg(test)]
    pub(crate) fn close_method_rigidity_with_registry<F>(
        &mut self,
        registry: &ResolvedRegistry,
        target: MethodRigidityTarget,
        mut zonk: F,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<bool, SelectionError>
    where
        F: FnMut(KindedArgument, &mut TypeWorkBudget) -> Result<KindedArgument, SelectionFailure>,
    {
        let mut snapshot = self
            .prepare_method_rigidity_determination(
                registry,
                target,
                &mut zonk,
                constraint_work,
                type_work,
            )
            .map_err(|failure| SelectionError {
                failure,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })?;
        if snapshot.take_task().is_some() {
            return Err(SelectionError {
                failure: SelectionFailure::InvalidState,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            });
        }
        self.close_method_rigidity_with_snapshot_and_registry(
            registry,
            target,
            &snapshot,
            zonk,
            constraint_work,
            type_work,
        )
    }

    pub(crate) fn close_method_rigidity_with_snapshot_and_registry<F>(
        &mut self,
        registry: &ResolvedRegistry,
        target: MethodRigidityTarget,
        snapshot: &MethodRigidityDeterminationSnapshot,
        mut zonk: F,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<bool, SelectionError>
    where
        F: FnMut(KindedArgument, &mut TypeWorkBudget) -> Result<KindedArgument, SelectionFailure>,
    {
        let invalid = || SelectionError {
            failure: SelectionFailure::InvalidState,
            span: None,
            declaration_span: None,
            import_span: None,
            causes: Vec::new(),
        };
        if self.pending_suffix_counts(target.marker).is_err()
            || !self.method_rigidities.is_empty()
            || snapshot.target != target
        {
            return Err(invalid());
        }
        if self.pending_method_rigidity_count == 0 {
            return if snapshot.matching_index.is_none() {
                Ok(false)
            } else {
                Err(invalid())
            };
        }
        let Some(matching_index) = snapshot.matching_index else {
            return Ok(false);
        };
        let obligation = self.pending.get(matching_index).ok_or_else(invalid)?;
        let obligation_interface = obligation.application.interface();
        if snapshot.determined && !snapshot.eligible {
            return Err(SelectionError {
                failure: SelectionFailure::Reason(InterfaceReason::Ambiguous),
                span: Some(obligation.span),
                declaration_span: obligation.declaration_span,
                import_span: obligation.import_span,
                causes: Vec::new(),
            });
        }
        let condition = obligation.method_rigidity.as_ref().ok_or_else(invalid)?;
        if condition.rigid_arguments.len() != obligation.method_arguments.len() {
            return Err(invalid());
        }
        let shifted_records = self
            .pending
            .len()
            .checked_sub(matching_index)
            .and_then(|count| count.checked_sub(1))
            .ok_or_else(invalid)?;
        let retained_work = shifted_records.checked_add(2).ok_or(SelectionError {
            failure: SelectionFailure::ConstraintResource,
            span: None,
            declaration_span: None,
            import_span: None,
            causes: Vec::new(),
        })?;
        constraint_work
            .charge(retained_work)
            .map_err(|()| SelectionError {
                failure: SelectionFailure::ConstraintResource,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })?;
        self.selected.try_reserve(1).map_err(|_| SelectionError {
            failure: SelectionFailure::ConstraintResource,
            span: None,
            declaration_span: None,
            import_span: None,
            causes: Vec::new(),
        })?;
        self.method_rigidities
            .try_reserve(1)
            .map_err(|_| SelectionError {
                failure: SelectionFailure::ConstraintResource,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })?;
        let span = obligation.span;
        let declaration_span = obligation.declaration_span;
        let import_span = obligation.import_span;
        let application = obligation
            .application
            .clone_with_budget(type_work)
            .map_err(|()| SelectionError {
                failure: SelectionFailure::TypeResource,
                span: Some(span),
                declaration_span,
                import_span,
                causes: Vec::new(),
            })?;
        let application =
            zonk_application(application, &mut zonk, type_work).map_err(|failure| {
                SelectionError {
                    failure,
                    span: Some(span),
                    declaration_span,
                    import_span,
                    causes: Vec::new(),
                }
            })?;
        let mut causes = Vec::new();
        let (checked_application, selection) = match self.select_owned(
            registry,
            application,
            obligation.lexical_head,
            &mut causes,
            constraint_work,
            type_work,
        ) {
            Ok(selection) => selection,
            Err(failure) => {
                let causes = if matches!(failure, SelectionFailure::Reason(_)) {
                    causes
                } else {
                    Vec::new()
                };
                return Err(SelectionError {
                    failure,
                    span: Some(span),
                    declaration_span,
                    import_span,
                    causes,
                });
            }
        };
        let selected_index = self.selected.len();
        let exact_current = self.current.is_some_and(|current| {
            matches!(
                selection.node(selection.root()),
                Some(EvidenceNode::Implementation { implementation, .. })
                    if implementation == current
            )
        });
        let pending_method_rigidity_count = self
            .pending_method_rigidity_count
            .checked_sub(1)
            .ok_or_else(invalid)?;
        let pending_determined_count = if self.interface_is_determined(obligation_interface) {
            self.pending_determined_count
                .checked_sub(1)
                .ok_or_else(invalid)?
        } else {
            self.pending_determined_count
        };
        let selected_condition = if exact_current {
            Some(
                self.pending
                    .get_mut(matching_index)
                    .and_then(|obligation| obligation.method_rigidity.take())
                    .ok_or_else(invalid)?,
            )
        } else {
            None
        };
        let mut obligation = self.pending.remove(matching_index);
        self.pending_determined_count = pending_determined_count;
        self.pending_method_rigidity_count = pending_method_rigidity_count;
        if let Some(condition) = selected_condition {
            self.method_rigidities.push(SelectedMethodRigidity {
                selected_index,
                condition,
            });
        }
        self.selected.push(SelectedOccurrence {
            checked_method: obligation.checked_method,
            checked_application,
            method_arguments: std::mem::take(&mut obligation.method_arguments),
            checked_value_type: obligation.checked_value_type.take(),
            selection: Some(selection),
            slot: Some(obligation.slot.clone()),
        });
        Ok(true)
    }

    fn matching_method_rigidity_index(
        &self,
        target: MethodRigidityTarget,
    ) -> Result<Option<usize>, SelectionFailure> {
        self.pending_suffix_counts(target.marker)?;
        let mut best = None;
        let mut duplicate = false;
        for (offset, obligation) in self.pending[target.marker.pending_len..].iter().enumerate() {
            let Some(rank) = obligation
                .method_rigidity
                .as_ref()
                .and_then(|condition| condition.site.failure_match_rank(target.failure_span))
            else {
                continue;
            };
            let index = target
                .marker
                .pending_len
                .checked_add(offset)
                .ok_or(SelectionFailure::ConstraintResource)?;
            match best {
                None => {
                    best = Some((rank, index));
                    duplicate = false;
                }
                Some((best_rank, _)) if rank < best_rank => {
                    best = Some((rank, index));
                    duplicate = false;
                }
                Some((best_rank, _)) if rank == best_rank => duplicate = true,
                Some(_) => {}
            }
        }
        if duplicate {
            Err(SelectionFailure::InvalidState)
        } else {
            Ok(best.map(|(_, index)| index))
        }
    }

    #[cfg(test)]
    pub(crate) fn close<F>(
        &mut self,
        marker: PendingObligationMarker,
        mut zonk: F,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionError>
    where
        F: FnMut(KindedArgument, &mut TypeWorkBudget) -> Result<KindedArgument, SelectionFailure>,
    {
        let registry = self.canonical_registry_for_test();
        self.close_with_authority(
            &registry,
            marker,
            None,
            &mut zonk,
            constraint_work,
            type_work,
        )?;
        let publication = self
            .prepare_publication(&mut zonk, constraint_work, type_work)
            .map_err(|failure| SelectionError {
                failure,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })?;
        publication.publish().map_err(|failure| SelectionError {
            failure,
            span: None,
            declaration_span: None,
            import_span: None,
            causes: Vec::new(),
        })
    }

    fn close_with_authority<F>(
        &mut self,
        registry: &ResolvedRegistry,
        marker: PendingObligationMarker,
        snapshot: Option<&DeterminationSnapshot>,
        mut zonk: F,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(), SelectionError>
    where
        F: FnMut(KindedArgument, &mut TypeWorkBudget) -> Result<KindedArgument, SelectionFailure>,
    {
        if !self.method_rigidities.is_empty() {
            return Err(SelectionError {
                failure: SelectionFailure::InvalidState,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            });
        }
        let (pending_count, _) =
            self.pending_suffix_counts(marker)
                .map_err(|failure| SelectionError {
                    failure,
                    span: None,
                    declaration_span: None,
                    import_span: None,
                    causes: Vec::new(),
                })?;
        if let Some(snapshot) = snapshot
            && (snapshot.marker != marker
                || !snapshot.eligible.is_empty() && snapshot.eligible.len() != pending_count)
        {
            return Err(SelectionError {
                failure: SelectionFailure::InvalidState,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            });
        }
        let conditional_count = self.pending[marker.pending_len..]
            .iter()
            .filter(|obligation| obligation.method_rigidity.is_some())
            .count();
        // One pending-record unit prices each selected output before either
        // retained output buffer reserves or the pending suffix moves.
        constraint_work
            .charge(
                pending_count
                    .checked_add(conditional_count)
                    .ok_or(SelectionError {
                        failure: SelectionFailure::ConstraintResource,
                        span: None,
                        declaration_span: None,
                        import_span: None,
                        causes: Vec::new(),
                    })?,
            )
            .map_err(|()| SelectionError {
                failure: SelectionFailure::ConstraintResource,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })?;
        self.method_rigidities
            .try_reserve(conditional_count)
            .map_err(|_| SelectionError {
                failure: SelectionFailure::ConstraintResource,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })?;
        self.selected
            .try_reserve(pending_count)
            .map_err(|_| SelectionError {
                failure: SelectionFailure::ConstraintResource,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })?;
        self.pending[marker.pending_len..].reverse();
        let mut source_offset = 0usize;
        while self.pending.len() > marker.pending_len {
            let pending_determined_count = if self.pending.last().is_some_and(|obligation| {
                self.interface_is_determined(obligation.application.interface())
            }) {
                self.pending_determined_count
                    .checked_sub(1)
                    .ok_or(SelectionError {
                        failure: SelectionFailure::InvalidState,
                        span: None,
                        declaration_span: None,
                        import_span: None,
                        causes: Vec::new(),
                    })?
            } else {
                self.pending_determined_count
            };
            let mut obligation = self.pending.pop().ok_or(SelectionError {
                failure: SelectionFailure::InvalidState,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })?;
            self.pending_determined_count = pending_determined_count;
            if obligation.method_rigidity.is_some() {
                self.pending_method_rigidity_count = self
                    .pending_method_rigidity_count
                    .checked_sub(1)
                    .ok_or(SelectionError {
                        failure: SelectionFailure::InvalidState,
                        span: Some(obligation.span),
                        declaration_span: obligation.declaration_span,
                        import_span: obligation.import_span,
                        causes: Vec::new(),
                    })?;
            }
            let interface = obligation.application.interface();
            if snapshot.is_some_and(|snapshot| !snapshot.eligible.is_empty()) {
                let interface_entry =
                    self.interface_entry(interface)
                        .map_err(|failure| SelectionError {
                            failure,
                            span: Some(obligation.span),
                            declaration_span: obligation.declaration_span,
                            import_span: obligation.import_span,
                            causes: Vec::new(),
                        })?;
                if interface_entry.determination.is_some() {
                    let eligible = snapshot
                        .and_then(|snapshot| snapshot.eligible.get(source_offset))
                        .copied()
                        .unwrap_or(false);
                    if !eligible {
                        let mut causes = Vec::new();
                        retain_selection_cause(
                            &mut causes,
                            SelectionCauseKind::Interface,
                            interface_entry.span,
                            constraint_work,
                        )
                        .map_err(|failure| SelectionError {
                            failure,
                            span: Some(obligation.span),
                            declaration_span: obligation.declaration_span,
                            import_span: obligation.import_span,
                            causes: Vec::new(),
                        })?;
                        return Err(SelectionError {
                            failure: SelectionFailure::Reason(InterfaceReason::Ambiguous),
                            span: Some(obligation.span),
                            declaration_span: obligation.declaration_span,
                            import_span: obligation.import_span,
                            causes,
                        });
                    }
                }
            }
            source_offset = source_offset.checked_add(1).ok_or(SelectionError {
                failure: SelectionFailure::ConstraintResource,
                span: Some(obligation.span),
                declaration_span: obligation.declaration_span,
                import_span: obligation.import_span,
                causes: Vec::new(),
            })?;
            let application = std::mem::replace(
                &mut obligation.application,
                InterfaceApplication::new_kinded(interface, Box::new([])),
            );
            let application =
                zonk_application(application, &mut zonk, type_work).map_err(|failure| {
                    SelectionError {
                        failure,
                        span: Some(obligation.span),
                        declaration_span: obligation.declaration_span,
                        import_span: obligation.import_span,
                        causes: Vec::new(),
                    }
                })?;
            let mut causes = Vec::new();
            let (checked_application, selection) = match self.select_owned(
                registry,
                application,
                obligation.lexical_head,
                &mut causes,
                constraint_work,
                type_work,
            ) {
                Ok(selection) => selection,
                Err(failure) => {
                    let causes = if matches!(failure, SelectionFailure::Reason(_)) {
                        causes
                    } else {
                        Vec::new()
                    };
                    return Err(SelectionError {
                        failure,
                        span: Some(obligation.span),
                        declaration_span: obligation.declaration_span,
                        import_span: obligation.import_span,
                        causes,
                    });
                }
            };
            let selected_index = self.selected.len();
            let exact_current = self.current.is_some_and(|current| {
                matches!(
                    selection.node(selection.root()),
                    Some(EvidenceNode::Implementation { implementation, .. })
                        if implementation == current
                )
            });
            if exact_current && let Some(condition) = obligation.method_rigidity.take() {
                if condition.rigid_arguments.len() != obligation.method_arguments.len() {
                    return Err(SelectionError {
                        failure: SelectionFailure::InvalidState,
                        span: Some(obligation.span),
                        declaration_span: obligation.declaration_span,
                        import_span: obligation.import_span,
                        causes: Vec::new(),
                    });
                }
                self.method_rigidities.push(SelectedMethodRigidity {
                    selected_index,
                    condition,
                });
            }
            self.selected.push(SelectedOccurrence {
                checked_method: obligation.checked_method,
                checked_application,
                method_arguments: std::mem::take(&mut obligation.method_arguments),
                checked_value_type: obligation.checked_value_type.take(),
                selection: Some(selection),
                slot: Some(obligation.slot.clone()),
            });
        }
        if source_offset != pending_count
            || self.pending_determined_count != marker.determined_count
        {
            return Err(SelectionError {
                failure: SelectionFailure::InvalidState,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            });
        }
        Ok(())
    }

    pub(crate) fn capture_slot_present(
        &self,
        slot: usize,
        budget: &mut TypeWorkBudget,
    ) -> Result<bool, SelectionFailure> {
        budget
            .charge(
                self.selected
                    .len()
                    .checked_add(self.pending.len())
                    .ok_or(SelectionFailure::TypeResource)?,
            )
            .map_err(|()| SelectionFailure::TypeResource)?;
        Ok(self.selected.iter().any(|occurrence| {
            occurrence
                .slot
                .as_ref()
                .is_some_and(|candidate| candidate.storage_id() == slot)
        }) || self
            .pending
            .iter()
            .any(|pending| pending.slot.storage_id() == slot))
    }

    /// Copies only immutable selected-plan handles. No body traversal or new
    /// selection occurs; each node remains independently authenticated later.
    pub(crate) fn selected_family_plans(
        &self,
        source: LexicalEvidenceId,
        work: &mut TypeWorkBudget,
    ) -> Result<Vec<(EvidenceSelection, crate::interface::EvidenceNodeId)>, SelectionFailure> {
        work.charge(self.selected.len())
            .map_err(|()| SelectionFailure::TypeResource)?;
        let mut plans = Vec::new();
        for occurrence in &self.selected {
            let selection = occurrence
                .selection
                .as_ref()
                .ok_or(SelectionFailure::InvalidState)?;
            work.charge(selection.node_count())
                .map_err(|()| SelectionFailure::TypeResource)?;
            for index in 0..selection.node_count() {
                let node = crate::interface::EvidenceNodeId::new(index);
                if matches!(selection.node(node), Some(EvidenceNode::ProviderFamily { source: candidate, .. }) if candidate == source)
                {
                    work.charge(1)
                        .map_err(|()| SelectionFailure::TypeResource)?;
                    plans
                        .try_reserve(1)
                        .map_err(|_| SelectionFailure::TypeResource)?;
                    plans.push((selection.clone(), node));
                }
            }
        }
        Ok(plans)
    }

    /// Borrow an already selected immutable plan for one exact typed source
    /// occurrence. This does not close obligations or select any implementation.
    pub(crate) fn capture_selected(
        &self,
        slot: usize,
        method: Option<MethodId>,
        budget: &mut TypeWorkBudget,
    ) -> Result<(&EvidenceSelection, usize), SelectionFailure> {
        budget
            .charge(
                self.selected
                    .len()
                    .checked_add(self.pending.len())
                    .and_then(|n| n.checked_add(self.method_rigidities.len()))
                    .ok_or(SelectionFailure::TypeResource)?,
            )
            .map_err(|()| SelectionFailure::TypeResource)?;
        if self
            .pending
            .iter()
            .any(|pending| pending.slot.storage_id() == slot)
        {
            return Err(SelectionFailure::InvalidState);
        }
        let mut matches = self.selected.iter().enumerate().filter(|(_, occurrence)| {
            occurrence
                .slot
                .as_ref()
                .is_some_and(|candidate| candidate.storage_id() == slot)
        });
        let (index, occurrence) = matches.next().ok_or(SelectionFailure::InvalidState)?;
        if matches.next().is_some()
            || occurrence.checked_method != method
            || !occurrence
                .slot
                .as_ref()
                .ok_or(SelectionFailure::InvalidState)?
                .is_empty()
            || self
                .method_rigidities
                .iter()
                .any(|rigidity| rigidity.selected_index == index)
        {
            return Err(SelectionFailure::InvalidState);
        }
        Ok((
            occurrence
                .selection
                .as_ref()
                .ok_or(SelectionFailure::InvalidState)?,
            occurrence.method_arguments.len(),
        ))
    }

    pub(crate) fn prepare_publication<F>(
        &mut self,
        mut zonk: F,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<PendingEvidencePublication, SelectionFailure>
    where
        F: FnMut(KindedArgument, &mut TypeWorkBudget) -> Result<KindedArgument, SelectionFailure>,
    {
        if !self.pending.is_empty()
            || self.pending_determined_count != 0
            || self.pending_method_rigidity_count != 0
            || !self.method_rigidities.is_empty()
        {
            return Err(SelectionFailure::InvalidState);
        }
        let method_argument_count = self.selected.iter().try_fold(0usize, |total, selected| {
            total.checked_add(selected.method_arguments.len())
        });
        let checked_value_type_count = self
            .selected
            .iter()
            .filter(|selected| selected.checked_value_type.is_some())
            .count();
        let checked_method_count = self
            .selected
            .iter()
            .filter(|selected| selected.checked_method.is_some())
            .count();
        let retained_work = method_argument_count
            .and_then(|count| {
                self.selected
                    .len()
                    .checked_mul(2)
                    .and_then(|fixed| count.checked_add(fixed))
            })
            .and_then(|count| count.checked_add(checked_value_type_count))
            .and_then(|count| count.checked_add(checked_method_count))
            .ok_or(SelectionFailure::ConstraintResource)?;
        constraint_work
            .charge(retained_work)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut occurrences = Vec::new();
        let mut slot_ids = HashMap::new();
        occurrences
            .try_reserve(self.selected.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        slot_ids
            .try_reserve(self.selected.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        for mut selected in self.selected.drain(..) {
            let interface = selected.checked_application.interface();
            let application = std::mem::replace(
                &mut selected.checked_application,
                InterfaceApplication::new_kinded(interface, Box::new([])),
            );
            let checked_application = zonk_application(application, &mut zonk, type_work)?;
            let selection = selected
                .selection
                .as_ref()
                .ok_or(SelectionFailure::InvalidState)?;
            if selection.interface() != checked_application.interface()
                || selection.arguments().len() != checked_application.arguments().len()
                || !selection
                    .arguments()
                    .iter()
                    .zip(checked_application.arguments())
                    .try_fold(true, |same, (left, right)| {
                        if !same {
                            return Ok(false);
                        }
                        same_kinded_argument_with_constraint_budget(left, right, constraint_work)
                    })
                    .map_err(|()| SelectionFailure::ConstraintResource)?
            {
                return Err(SelectionFailure::InvalidState);
            }
            let mut method_arguments = Vec::new();
            type_work
                .charge(selected.method_arguments.len())
                .map_err(|()| SelectionFailure::TypeResource)?;
            method_arguments
                .try_reserve(selected.method_arguments.len())
                .map_err(|_| SelectionFailure::TypeResource)?;
            for argument in std::mem::take(&mut selected.method_arguments).into_vec() {
                match zonk_type(argument, &mut zonk, type_work) {
                    Ok(argument) => method_arguments.push(argument),
                    Err(failure) => {
                        for argument in method_arguments {
                            discard_type_iteratively(argument);
                        }
                        return Err(failure);
                    }
                }
            }
            let checked_value_type = match selected.checked_value_type.take() {
                Some(checked_value_type) => {
                    match zonk_type(checked_value_type, &mut zonk, type_work) {
                        Ok(checked_value_type) => Some(checked_value_type),
                        Err(failure) => {
                            for argument in method_arguments {
                                discard_type_iteratively(argument);
                            }
                            return Err(failure);
                        }
                    }
                }
                None => None,
            };
            let Some(slot) = selected.slot.take() else {
                for argument in method_arguments {
                    discard_type_iteratively(argument);
                }
                if let Some(checked_value_type) = checked_value_type {
                    discard_type_iteratively(checked_value_type);
                }
                return Err(SelectionFailure::InvalidState);
            };
            let slot_id = slot.storage_id();
            if !slot.is_empty() || slot_ids.insert(slot_id, selected.checked_method).is_some() {
                for argument in method_arguments {
                    discard_type_iteratively(argument);
                }
                if let Some(checked_value_type) = checked_value_type {
                    discard_type_iteratively(checked_value_type);
                }
                return Err(SelectionFailure::InvalidState);
            }
            occurrences.push(SelectedOccurrence {
                checked_method: selected.checked_method,
                checked_application,
                method_arguments: method_arguments.into_boxed_slice(),
                checked_value_type,
                selection: selected.selection.take(),
                slot: Some(slot),
            });
        }
        Ok(PendingEvidencePublication {
            occurrences,
            slot_ids,
        })
    }

    #[cfg(test)]
    pub(crate) fn select(
        &self,
        interface: InterfaceId,
        argument: &Type,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<EvidenceSelection, SelectionFailure> {
        let argument = clone_type_with_budget(argument, type_work)
            .map_err(|()| SelectionFailure::TypeResource)?;
        let registry = self.canonical_registry_for_test();
        let mut causes = Vec::new();
        let (checked_application, selection) = self.select_owned(
            &registry,
            InterfaceApplication::from_type_arguments_with_budget(
                interface,
                Box::new([argument]),
                type_work,
            )
            .map_err(|()| SelectionFailure::TypeResource)?,
            self.lexical_head,
            &mut causes,
            constraint_work,
            type_work,
        )?;
        drop(checked_application);
        Ok(selection)
    }

    #[cfg(test)]
    fn select_owned_for_test(
        &self,
        interface: InterfaceId,
        argument: Type,
        causes: &mut Vec<SelectionCause>,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(Type, EvidenceSelection), SelectionFailure> {
        let registry = self.canonical_registry_for_test();
        let (application, selection) = self.select_owned(
            &registry,
            InterfaceApplication::from_type_arguments_with_budget(
                interface,
                Box::new([argument]),
                type_work,
            )
            .map_err(|()| SelectionFailure::TypeResource)?,
            self.lexical_head,
            causes,
            constraint_work,
            type_work,
        )?;
        let (_, arguments) = application.into_parts();
        let mut arguments = arguments.into_vec();
        if arguments.len() != 1 {
            for argument in arguments {
                discard_kinded_argument_iteratively(argument);
            }
            return Err(SelectionFailure::InvalidState);
        }
        let argument = arguments.pop().ok_or(SelectionFailure::InvalidState)?;
        match argument {
            KindedArgument::TypeArg(ty) => Ok((ty, selection)),
            other => {
                discard_kinded_argument_iteratively(other);
                Err(SelectionFailure::InvalidState)
            }
        }
    }

    fn select_owned(
        &self,
        registry: &ResolvedRegistry,
        application: InterfaceApplication,
        lexical_head: Option<usize>,
        causes: &mut Vec<SelectionCause>,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<(InterfaceApplication, EvidenceSelection), SelectionFailure> {
        causes.clear();
        if application
            .arguments()
            .iter()
            .any(|argument| matches!(argument, KindedArgument::TypeArg(Type::Inference(_))))
        {
            let interface_entry = self.interface_entry(application.interface())?;
            retain_selection_cause(
                causes,
                SelectionCauseKind::Interface,
                interface_entry.span,
                constraint_work,
            )?;
            return Err(SelectionFailure::Reason(InterfaceReason::Ambiguous));
        }
        if application
            .arguments()
            .iter()
            .any(|argument| matches!(argument, KindedArgument::TypeArg(Type::Forall(_, _))))
        {
            return Err(SelectionFailure::InvalidState);
        }
        let mut builder = EvidenceSelectionBuilder::new();
        let checked_application = application;
        let work_application = checked_application
            .clone_with_budget(type_work)
            .map_err(|()| SelectionFailure::TypeResource)?;
        let mut work = SelectionWork::new(
            Goal {
                application: work_application,
            },
            0,
            constraint_work,
        )?;
        let mut results = Vec::new();
        let mut active = std::collections::HashSet::new();
        while let Some(task) = work.pop() {
            match task {
                SelectionTask::Select { goal, cause_marker } => {
                    if cause_marker > causes.len() {
                        return Err(SelectionFailure::InvalidState);
                    }
                    causes.truncate(cause_marker);
                    let interface = goal.application.interface();
                    let interface_entry = self.interface_entry(interface)?;
                    retain_selection_cause(
                        causes,
                        SelectionCauseKind::Interface,
                        interface_entry.span,
                        constraint_work,
                    )?;
                    let key = goal_key(&goal.application, constraint_work)?;
                    constraint_work
                        .charge(goal.application.arguments().len())
                        .map_err(|()| SelectionFailure::ConstraintResource)?;
                    let mut goal_roots = Vec::new();
                    goal_roots
                        .try_reserve_exact(goal.application.arguments().len())
                        .map_err(|_| SelectionFailure::ConstraintResource)?;
                    goal_roots.extend(goal.application.arguments());
                    let goal_environments = canonical_body_free_argument_environments(
                        registry,
                        &[],
                        &goal_roots,
                        interface_entry.span,
                        constraint_work,
                        type_work,
                    )
                    .map_err(map_ingress_environment_failure)?;
                    let interface_methods = interface_entry.method_ids.as_ref();
                    let mut abstract_match = None;
                    for requirement in &self.abstracts {
                        constraint_work
                            .charge(1)
                            .map_err(|()| SelectionFailure::ConstraintResource)?;
                        if same_applications_with_constraint_budget(
                            &requirement.application,
                            &goal.application,
                            constraint_work,
                        )? {
                            abstract_match = Some(requirement.id);
                            break;
                        }
                    }
                    if let Some(requirement) = abstract_match {
                        reserve_selection_result(&mut results, constraint_work)?;
                        let node = builder
                            .push_abstract(requirement, interface_methods, constraint_work)
                            .map_err(|()| SelectionFailure::ConstraintResource)?;
                        results.push(node);
                        continue;
                    }

                    if let Some(current) = self.current {
                        constraint_work
                            .charge(1)
                            .map_err(|()| SelectionFailure::ConstraintResource)?;
                        let implementation_index = *self
                            .implementation_indices
                            .get(&current)
                            .ok_or(SelectionFailure::InvalidState)?;
                        let implementation = self
                            .implementations
                            .get(implementation_index)
                            .ok_or(SelectionFailure::InvalidState)?;
                        if same_applications_with_constraint_budget(
                            &implementation.application,
                            &goal.application,
                            constraint_work,
                        )? {
                            reserve_selection_result(&mut results, constraint_work)?;
                            let substitution = self
                                .match_head(
                                    registry,
                                    &goal_environments,
                                    implementation,
                                    &goal.application,
                                    constraint_work,
                                    type_work,
                                )
                                .map_err(map_head_failure)?
                                .ok_or(SelectionFailure::InvalidState)?;
                            let mut prerequisites = Vec::new();
                            constraint_work
                                .charge(implementation.prerequisites.len())
                                .map_err(|()| SelectionFailure::ConstraintResource)?;
                            prerequisites
                                .try_reserve(implementation.prerequisites.len())
                                .map_err(|_| SelectionFailure::ConstraintResource)?;
                            for prerequisite in &implementation.prerequisites {
                                constraint_work
                                    .charge(1)
                                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                                prerequisites.push(
                                    builder
                                        .push_abstract(
                                            prerequisite.id,
                                            self.interface_methods(
                                                prerequisite.application.interface(),
                                            )?,
                                            constraint_work,
                                        )
                                        .map_err(|()| SelectionFailure::ConstraintResource)?,
                                );
                            }
                            let node = builder
                                .push_implementation(
                                    implementation.id,
                                    substitution,
                                    &prerequisites,
                                    &implementation.methods,
                                    constraint_work,
                                )
                                .map_err(|()| SelectionFailure::ConstraintResource)?;
                            results.push(node);
                            continue;
                        }
                    }

                    let mut head = lexical_head;
                    let mut lexical_match = None;
                    while let Some(index) = head {
                        constraint_work
                            .charge(1)
                            .map_err(|()| SelectionFailure::ConstraintResource)?;
                        let source = self
                            .lexical_sources
                            .get(index)
                            .ok_or(SelectionFailure::InvalidState)?;
                        head = source.parent;
                        if source.family.is_none()
                            && same_applications_with_constraint_budget(
                                &source.application,
                                &goal.application,
                                constraint_work,
                            )?
                        {
                            lexical_match = Some(source.id);
                            break;
                        }
                    }
                    if let Some(source) = lexical_match {
                        reserve_selection_result(&mut results, constraint_work)?;
                        let node = builder
                            .push_lexical(source, interface_methods, constraint_work)
                            .map_err(|()| SelectionFailure::ConstraintResource)?;
                        results.push(node);
                        continue;
                    }
                    // Abstract requirements and exact scoped evidence retain
                    // their established precedence. Only the authenticated
                    // foreign policy derives a closed scalar Layout goal.
                    if let Some(layout) = registry.foreign_layout(interface) {
                        constraint_work
                            .charge(3)
                            .map_err(|()| SelectionFailure::ConstraintResource)?;
                        let [KindedArgument::TypeArg(payload)] = goal.application.arguments()
                        else {
                            return Err(SelectionFailure::InvalidState);
                        };
                        let dictionary = layout
                            .dictionary_for_payload(payload)
                            .ok_or(SelectionFailure::Reason(InterfaceReason::Unsatisfied))?;
                        reserve_selection_result(&mut results, constraint_work)?;
                        let node = builder
                            .push_native_layout(dictionary.producer(), constraint_work)
                            .map_err(|()| SelectionFailure::ConstraintResource)?;
                        results.push(node);
                        continue;
                    }
                    charge_goal_key(&key, constraint_work)?;
                    if active.contains(&key) {
                        return Err(SelectionFailure::Reason(InterfaceReason::Cycle));
                    }
                    charge_goal_key(&key, constraint_work)?;
                    active
                        .try_reserve(1)
                        .map_err(|_| SelectionFailure::ConstraintResource)?;
                    let key = Arc::new(key);
                    active.insert(Arc::clone(&key));

                    // Families are lexical templates, selected only for this exact
                    // demanded goal. Their ordered requirements use the ordinary
                    // selection stack and share its cycle/work accounting.
                    let mut head = lexical_head;
                    let mut family_match = None;
                    while let Some(index) = head {
                        constraint_work
                            .charge(1)
                            .map_err(|()| SelectionFailure::ConstraintResource)?;
                        let source = self
                            .lexical_sources
                            .get(index)
                            .ok_or(SelectionFailure::InvalidState)?;
                        head = source.parent;
                        let Some(family) = &source.family else {
                            continue;
                        };
                        if source.application.interface() != interface {
                            continue;
                        }
                        let count = source
                            .application
                            .arguments()
                            .len()
                            .checked_add(goal.application.arguments().len())
                            .ok_or(SelectionFailure::ConstraintResource)?;
                        constraint_work
                            .charge(count)
                            .map_err(|()| SelectionFailure::ConstraintResource)?;
                        let mut candidate = Vec::new();
                        let mut actual = Vec::new();
                        candidate
                            .try_reserve_exact(source.application.arguments().len())
                            .map_err(|_| SelectionFailure::ConstraintResource)?;
                        actual
                            .try_reserve_exact(goal.application.arguments().len())
                            .map_err(|_| SelectionFailure::ConstraintResource)?;
                        candidate.extend(source.application.arguments());
                        actual.extend(goal.application.arguments());
                        if let Some(substitution) =
                            match_provider_family_application_head_in_environment(
                                registry,
                                InterfaceOperationWork::new(
                                    source.span,
                                    constraint_work,
                                    type_work,
                                ),
                                &goal_environments,
                                family.parameter,
                                &candidate,
                                &actual,
                            )
                            .map_err(map_head_failure)?
                        {
                            family_match = Some((index, substitution));
                            break;
                        }
                    }
                    if let Some((source_index, substitution)) = family_match {
                        let source = self
                            .lexical_sources
                            .get(source_index)
                            .ok_or(SelectionFailure::InvalidState)?;
                        let family = source
                            .family
                            .as_ref()
                            .ok_or(SelectionFailure::InvalidState)?;
                        let replacements = replacement_map(&substitution, type_work)?;
                        let result_start = results.len();
                        let application = goal
                            .application
                            .clone_with_budget(type_work)
                            .map_err(|()| SelectionFailure::TypeResource)?;
                        let cause_marker = causes.len();
                        work.push(
                            SelectionTask::FinishFamily {
                                key,
                                source_index,
                                application,
                                result_start,
                            },
                            constraint_work,
                        )?;
                        for prerequisite in family.requirements.iter().rev() {
                            type_work
                                .charge(prerequisite.application.arguments().len())
                                .map_err(|()| SelectionFailure::TypeResource)?;
                            let mut arguments = EvidenceTypeBuffer(Vec::new());
                            arguments
                                .0
                                .try_reserve_exact(prerequisite.application.arguments().len())
                                .map_err(|_| SelectionFailure::TypeResource)?;
                            for argument in prerequisite.application.arguments() {
                                arguments.0.push(
                                    substitute_kinded_argument_with(
                                        argument,
                                        replacements.as_map(),
                                        &HashMap::new(),
                                        |cells| type_work.charge(cells),
                                    )
                                    .map_err(|()| SelectionFailure::TypeResource)?
                                    .map_err(|_| SelectionFailure::InvalidState)?,
                                );
                            }
                            let goal = Goal {
                                application: InterfaceApplication::new_kinded(
                                    prerequisite.application.interface(),
                                    arguments.into_boxed_slice(),
                                ),
                            };
                            charge_prerequisite_goal(&goal.application, constraint_work)?;
                            work.push(
                                SelectionTask::Select { goal, cause_marker },
                                constraint_work,
                            )?;
                        }
                        continue;
                    }

                    let mut selected = None;
                    let candidates = self
                        .implementation_candidates
                        .get(&interface)
                        .map(Vec::as_slice)
                        .unwrap_or_default();
                    for &candidate_index in candidates {
                        charge_candidate_inspection(constraint_work)?;
                        let implementation = self
                            .implementations
                            .get(candidate_index)
                            .ok_or(SelectionFailure::InvalidState)?;
                        if Some(implementation.id) == self.current {
                            continue;
                        }
                        let substitution = self
                            .match_head(
                                registry,
                                &goal_environments,
                                implementation,
                                &goal.application,
                                constraint_work,
                                type_work,
                            )
                            .map_err(map_head_failure)?;
                        if let Some(substitution) = substitution {
                            selected = Some((candidate_index, substitution));
                            break;
                        }
                    }
                    let Some((candidate_index, substitution)) = selected else {
                        charge_goal_key(&key, constraint_work)?;
                        if !active.remove(&key) {
                            return Err(SelectionFailure::InvalidState);
                        }
                        return Err(SelectionFailure::Reason(InterfaceReason::Unsatisfied));
                    };
                    let implementation = &self.implementations[candidate_index];
                    for &import_span in &implementation.import_spans {
                        retain_selection_cause(
                            causes,
                            SelectionCauseKind::ImplementationImport,
                            import_span,
                            constraint_work,
                        )?;
                    }
                    retain_selection_cause(
                        causes,
                        SelectionCauseKind::Implementation,
                        implementation.span,
                        constraint_work,
                    )?;
                    for &method_span in &implementation.method_spans {
                        retain_selection_cause(
                            causes,
                            SelectionCauseKind::ImplementationMethod,
                            method_span,
                            constraint_work,
                        )?;
                    }
                    let prerequisite_cause_marker = causes.len();
                    let replacements = replacement_map(&substitution, type_work)?;
                    let result_start = results.len();
                    work.push(
                        SelectionTask::Finish {
                            key,
                            candidate_index,
                            substitution,
                            result_start,
                        },
                        constraint_work,
                    )?;
                    for prerequisite in implementation.prerequisites.iter().rev() {
                        type_work
                            .charge(prerequisite.application.arguments().len())
                            .map_err(|()| SelectionFailure::TypeResource)?;
                        let mut arguments = EvidenceTypeBuffer(Vec::new());
                        arguments
                            .0
                            .try_reserve_exact(prerequisite.application.arguments().len())
                            .map_err(|_| SelectionFailure::TypeResource)?;
                        for argument in prerequisite.application.arguments() {
                            arguments.0.push(
                                substitute_kinded_argument_with(
                                    argument,
                                    replacements.as_map(),
                                    &HashMap::new(),
                                    |cells| type_work.charge(cells),
                                )
                                .map_err(|()| SelectionFailure::TypeResource)?
                                .map_err(|_| SelectionFailure::InvalidState)?,
                            );
                        }
                        let goal = Goal {
                            application: InterfaceApplication::new_kinded(
                                prerequisite.application.interface(),
                                arguments.into_boxed_slice(),
                            ),
                        };
                        charge_prerequisite_goal(&goal.application, constraint_work)?;
                        work.push(
                            SelectionTask::Select {
                                goal,
                                cause_marker: prerequisite_cause_marker,
                            },
                            constraint_work,
                        )?;
                    }
                    drop(goal);
                }
                SelectionTask::FinishFamily {
                    key,
                    source_index,
                    application,
                    result_start,
                } => {
                    charge_goal_key(&key, constraint_work)?;
                    if !active.remove(&key) || result_start > results.len() {
                        return Err(SelectionFailure::InvalidState);
                    }
                    let source = self
                        .lexical_sources
                        .get(source_index)
                        .ok_or(SelectionFailure::InvalidState)?;
                    let family = source
                        .family
                        .as_ref()
                        .ok_or(SelectionFailure::InvalidState)?;
                    if results.len() - result_start != family.requirements.len() {
                        return Err(SelectionFailure::InvalidState);
                    }
                    reserve_selection_result(&mut results, constraint_work)?;
                    let node = builder
                        .push_provider_family(
                            source.id,
                            family.definition,
                            family.parameter,
                            application,
                            &results[result_start..],
                            self.interface_methods(source.application.interface())?,
                            constraint_work,
                        )
                        .map_err(|()| SelectionFailure::ConstraintResource)?;
                    results.truncate(result_start);
                    results.push(node);
                }
                SelectionTask::Finish {
                    key,
                    candidate_index,
                    substitution,
                    result_start,
                } => {
                    charge_goal_key(&key, constraint_work)?;
                    if !active.remove(&key) || result_start > results.len() {
                        return Err(SelectionFailure::InvalidState);
                    }
                    let implementation = self
                        .implementations
                        .get(candidate_index)
                        .ok_or(SelectionFailure::InvalidState)?;
                    let result_count = results.len() - result_start;
                    if result_count != implementation.prerequisites.len() {
                        return Err(SelectionFailure::InvalidState);
                    }
                    reserve_selection_result(&mut results, constraint_work)?;
                    let prerequisites = &results[result_start..];
                    let node = builder
                        .push_implementation(
                            implementation.id,
                            substitution,
                            prerequisites,
                            &implementation.methods,
                            constraint_work,
                        )
                        .map_err(|()| SelectionFailure::ConstraintResource)?;
                    results.truncate(result_start);
                    results.push(node);
                }
            }
        }
        if !active.is_empty() || results.len() != 1 {
            return Err(SelectionFailure::InvalidState);
        }
        constraint_work
            .charge(1)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        for argument in checked_application.arguments() {
            constraint_work
                .charge_argument(argument)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
        }
        let selection_application = checked_application
            .clone_with_budget(type_work)
            .map_err(|()| SelectionFailure::TypeResource)?;
        let selection = match builder.finish(results[0], selection_application) {
            Ok(selection) => selection,
            Err(()) => return Err(SelectionFailure::InvalidState),
        };
        Ok((checked_application, selection))
    }

    fn interface_entry(&self, interface: InterfaceId) -> Result<&InterfaceEntry, SelectionFailure> {
        self.interface_indices
            .get(&interface)
            .and_then(|index| self.interfaces.get(*index))
            .ok_or(SelectionFailure::InvalidState)
    }

    fn match_head(
        &self,
        registry: &ResolvedRegistry,
        goal_environments: &KindEnvironments<'_>,
        implementation: &ImplementationEntry,
        goal: &InterfaceApplication,
        constraint_work: &mut InterfaceConstraintBudget,
        type_work: &mut TypeWorkBudget,
    ) -> Result<Option<Box<[EvidenceSubstitution]>>, HeadMatchFailure> {
        if implementation.application.interface() != goal.interface()
            || implementation.application.arguments().len() != goal.arguments().len()
        {
            return Ok(None);
        }
        constraint_work
            .charge(
                implementation
                    .application
                    .arguments()
                    .len()
                    .checked_add(goal.arguments().len())
                    .ok_or(HeadMatchFailure::ConstraintResource)?,
            )
            .map_err(|()| HeadMatchFailure::ConstraintResource)?;
        let mut candidate_arguments = Vec::new();
        let mut goal_arguments = Vec::new();
        candidate_arguments
            .try_reserve_exact(implementation.application.arguments().len())
            .map_err(|_| HeadMatchFailure::ConstraintResource)?;
        goal_arguments
            .try_reserve_exact(goal.arguments().len())
            .map_err(|_| HeadMatchFailure::ConstraintResource)?;
        candidate_arguments.extend(implementation.application.arguments());
        goal_arguments.extend(goal.arguments());
        match_implementation_application_head_in_environment(
            registry,
            InterfaceOperationWork::new(implementation.span, constraint_work, type_work),
            goal_environments,
            &implementation.parameters,
            &candidate_arguments,
            &goal_arguments,
        )
    }

    fn authenticate_implementation_candidate<'a>(
        &self,
        registry: &'a ResolvedRegistry,
        candidate: ImplementationCandidateAuthentication<'a>,
        constraint_work: &mut InterfaceConstraintBudget,
    ) -> Result<Vec<TypeVariableId>, SelectionFailure> {
        let ImplementationCandidateAuthentication {
            parameter_records,
            interfaces,
            argument_counts,
            arguments,
            span,
        } = candidate;
        let authentication_parameter_records = parameter_records
            .len()
            .checked_mul(2)
            .ok_or(SelectionFailure::ConstraintResource)?;
        // The returned parameter row and the temporary duplicate index are
        // separate owners and coexist throughout candidate authentication.
        constraint_work
            .charge(authentication_parameter_records)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut parameters = Vec::new();
        let mut parameter_set = HashSet::new();
        parameters
            .try_reserve(parameter_records.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        parameter_set
            .try_reserve(parameter_records.len())
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        for parameter in parameter_records {
            constraint_work
                .charge(1)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            if !parameter_set.insert(parameter.id) {
                return Err(SelectionFailure::InvalidState);
            }
            canonical_type_variable_kind(registry, parameter.id, span, constraint_work)
                .map_err(map_ingress_kind_failure)?;
            parameters.push(parameter.id);
        }

        if interfaces.is_empty() || interfaces.len() != argument_counts.len() {
            return Err(SelectionFailure::InvalidState);
        }
        let total_argument_count = argument_counts
            .iter()
            .copied()
            .try_fold(0usize, |sum, count| sum.checked_add(count))
            .ok_or(SelectionFailure::ConstraintResource)?;
        if total_argument_count != arguments.len() {
            return Err(SelectionFailure::InvalidState);
        }
        constraint_work
            .charge(interfaces.len())
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        for (interface, argument_count) in interfaces.iter().zip(argument_counts) {
            constraint_work
                .charge(1)
                .map_err(|()| SelectionFailure::ConstraintResource)?;
            if self.interface_entry(*interface)?.parameters.len() != *argument_count {
                return Err(SelectionFailure::InvalidState);
            }
        }
        validate_candidate_scope(&parameter_set, arguments, constraint_work)?;
        Ok(parameters)
    }

    fn interface_methods(&self, interface: InterfaceId) -> Result<&[MethodId], SelectionFailure> {
        self.interface_entry(interface)
            .map(|entry| entry.method_ids.as_ref())
    }

    #[cfg(test)]
    fn add_interface_raw(
        &mut self,
        id: InterfaceId,
        parameter: TypeVariableId,
        methods: Vec<(MethodId, Type)>,
    ) {
        self.add_interface_parameters_raw(id, vec![parameter], methods);
    }

    #[cfg(test)]
    fn add_interface_parameters_raw(
        &mut self,
        id: InterfaceId,
        parameters: Vec<TypeVariableId>,
        methods: Vec<(MethodId, Type)>,
    ) {
        self.add_interface_parameters_with_determination_raw(id, parameters, None, methods);
    }

    #[cfg(test)]
    fn add_interface_parameters_with_determination_raw(
        &mut self,
        id: InterfaceId,
        parameters: Vec<TypeVariableId>,
        determination: Option<DeterminationKey>,
        methods: Vec<(MethodId, Type)>,
    ) {
        let file = crate::source::SourceFile::new("selection-fixture.ash", "x")
            .expect("selection fixture source");
        let span = file
            .span(crate::source::ByteRange::new(0, 1).expect("selection fixture range"))
            .expect("selection fixture span");
        let method_ids = methods.iter().map(|(id, _)| *id).collect();
        let methods: Vec<MethodEntry> = methods
            .into_iter()
            .map(|(id, value_type)| MethodEntry {
                id,
                type_parameters: Box::new([]),
                value_type,
                span,
            })
            .collect();
        let interface_index = self.interfaces.len();
        for (method_index, method) in methods.iter().enumerate() {
            assert!(
                self.method_indices
                    .insert(method.id, (interface_index, method_index))
                    .is_none()
            );
        }
        assert!(self.interface_indices.insert(id, interface_index).is_none());
        self.interfaces.push(InterfaceEntry {
            id,
            sealed_layout: false,
            parameters: parameters
                .into_iter()
                .map(|parameter| (parameter, Kind::Type))
                .collect::<Vec<_>>()
                .into_boxed_slice(),
            determination,
            methods: methods.into_boxed_slice(),
            method_ids,
            span,
        });
    }

    #[cfg(test)]
    fn canonical_registry_for_test(&self) -> ResolvedRegistry {
        let mut binders = HashMap::new();
        let mut nominal_arities = HashMap::new();
        let mut roots = Vec::new();
        for interface in &self.interfaces {
            for (parameter, kind) in &interface.parameters {
                binders
                    .entry(*parameter)
                    .or_insert_with(|| (kind.clone(), interface.span));
            }
        }
        for implementation in &self.implementations {
            extend_owner_type_children_with_charge(
                implementation.application.arguments().iter(),
                &mut roots,
                &mut |_| Ok::<(), ()>(()),
            )
            .unwrap();
            for parameter in &implementation.parameters {
                binders
                    .entry(*parameter)
                    .or_insert((Kind::Type, implementation.span));
            }
            extend_owner_type_children_with_charge(
                implementation
                    .prerequisites
                    .iter()
                    .flat_map(|prerequisite| prerequisite.application.arguments()),
                &mut roots,
                &mut |_| Ok::<(), ()>(()),
            )
            .unwrap();
        }
        extend_owner_type_children_with_charge(
            self.abstracts
                .iter()
                .flat_map(|a| a.application.arguments()),
            &mut roots,
            &mut |_| Ok::<(), ()>(()),
        )
        .unwrap();
        extend_owner_type_children_with_charge(
            self.pending.iter().flat_map(|a| a.application.arguments()),
            &mut roots,
            &mut |_| Ok::<(), ()>(()),
        )
        .unwrap();
        let mut pending = roots;
        while let Some(ty) = pending.pop() {
            let mut function = ty;
            let mut arity = 0usize;
            while let Type::Application(next, _) = function {
                arity = arity
                    .checked_add(1)
                    .expect("a test fixture application arity should fit usize");
                function = next;
            }
            if let Type::Nominal(id) = function {
                nominal_arities
                    .entry(*id)
                    .and_modify(|known: &mut usize| *known = (*known).max(arity))
                    .or_insert(arity);
            }
            match ty {
                Type::Application(function, argument) | Type::Function(function, argument) => {
                    pending.push(argument);
                    pending.push(function);
                }
                Type::EffectfulFunction(domain, codomain) => {
                    extend_owner_type_children_with_charge(
                        codomain
                            .effects()
                            .known()
                            .iter()
                            .chain(
                                codomain
                                    .effects()
                                    .tail()
                                    .into_iter()
                                    .flat_map(|tail| tail.lacks()),
                            )
                            .flat_map(|instance| instance.arguments()),
                        &mut pending,
                        &mut |_| Ok::<(), ()>(()),
                    )
                    .unwrap();
                    pending.push(codomain.value());
                    pending.push(domain);
                }
                Type::ResourceApply(_, arguments) | Type::ForeignOwnerApply(_, arguments) => {
                    extend_owner_type_children_with_charge(
                        arguments.iter(),
                        &mut pending,
                        &mut |_| Ok::<(), ()>(()),
                    )
                    .unwrap();
                }
                Type::Tuple(elements) => pending.extend(elements.iter().rev()),
                Type::Forall(_, body) => pending.push(body),
                Type::Bytes
                | Type::String
                | Type::Int
                | Type::Bool
                | Type::Unit
                | Type::Nominal(_)
                | Type::Variable(_)
                | Type::Inference(_) => {}
            }
        }
        let fallback_span = self
            .interfaces
            .first()
            .map(|interface| interface.span)
            .or_else(|| {
                self.implementations
                    .first()
                    .map(|implementation| implementation.span)
            })
            .or_else(|| self.pending.first().map(|obligation| obligation.span))
            .expect(
                "a selection fixture should retain an interface, implementation, or obligation",
            );
        let mut used_ids = binders
            .keys()
            .copied()
            .collect::<std::collections::HashSet<_>>();
        let mut next_generated = u32::MAX;
        let mut nominal_parameters = Vec::new();
        let mut nominals = Vec::new();
        for (id, arity) in nominal_arities {
            let mut parameters = Vec::new();
            for _ in 0..arity {
                let parameter = loop {
                    let candidate = TypeVariableId::generated(next_generated);
                    next_generated = next_generated
                        .checked_sub(1)
                        .expect("the test nominal parameter inventory should fit");
                    if used_ids.insert(candidate) {
                        break candidate;
                    }
                };
                parameters.push(crate::resolved::ResolvedTypeVariable {
                    id: parameter,
                    spelling: "A".to_owned(),
                    kind: Kind::Type,
                    origin: crate::source::Origin::Source(fallback_span),
                });
            }
            nominals.push(crate::resolved::ResolvedNominalType {
                representation_provenance: None,
                declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                representation: None,
                id,
                spelling: "Nominal".to_owned(),
                constructors: Box::new([]),
                origin: crate::source::Origin::Source(fallback_span),
            });
            nominal_parameters.push((id, parameters));
        }
        ResolvedRegistry::new(nominals, Vec::new())
            .with_type_parameters(nominal_parameters)
            .with_additional_type_variables(binders.into_iter().map(|(id, (kind, span))| {
                crate::resolved::ResolvedTypeVariable {
                    id,
                    spelling: "T".to_owned(),
                    kind,
                    origin: crate::source::Origin::Source(span),
                }
            }))
    }

    #[cfg(test)]
    fn add_implementation_raw(&mut self, implementation: ImplementationEntry) {
        let index = self.implementations.len();
        assert!(
            self.implementation_indices
                .insert(implementation.id, index)
                .is_none()
        );
        self.implementation_candidates
            .entry(implementation.application.interface())
            .or_default()
            .push(index);
        self.implementations.push(implementation);
    }
}

pub(crate) fn map_head_failure(failure: HeadMatchFailure) -> SelectionFailure {
    match failure {
        HeadMatchFailure::InvalidState => SelectionFailure::InvalidState,
        HeadMatchFailure::Kind(context) => SelectionFailure::Kind {
            context,
            span: None,
        },
        HeadMatchFailure::ConstraintResource => SelectionFailure::ConstraintResource,
        HeadMatchFailure::TypeResource => SelectionFailure::TypeResource,
    }
}

fn map_ingress_environment_failure(failure: CanonicalEnvironmentFailure) -> SelectionFailure {
    match failure {
        CanonicalEnvironmentFailure::ConstraintResource => SelectionFailure::ConstraintResource,
        CanonicalEnvironmentFailure::TypeResource => SelectionFailure::TypeResource,
        CanonicalEnvironmentFailure::InvalidState => SelectionFailure::InvalidState,
        CanonicalEnvironmentFailure::Kind(context) => SelectionFailure::Kind {
            context,
            span: None,
        },
    }
}

fn map_ingress_kind_failure(failure: KindFailure) -> SelectionFailure {
    match failure {
        KindFailure::Resource(_) => SelectionFailure::ConstraintResource,
        failure => failure
            .internal_context()
            .map_or(SelectionFailure::InvalidState, |context| {
                SelectionFailure::Kind {
                    context,
                    span: None,
                }
            }),
    }
}

fn validate_candidate_scope(
    allowed: &HashSet<TypeVariableId>,
    roots: &[&KindedArgument],
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<(), SelectionFailure> {
    constraint_work
        .charge(roots.len())
        .map_err(|()| SelectionFailure::ConstraintResource)?;
    let mut pending = Vec::new();
    pending
        .try_reserve(roots.len())
        .map_err(|_| SelectionFailure::ConstraintResource)?;
    let mut invalid_scope = false;
    visit_owner_components_with_charge(
        roots.iter().copied(),
        &mut |cells| constraint_work.charge(cells),
        |ty, _| {
            pending.try_reserve(1).map_err(|_| ())?;
            pending.push(ty);
            Ok(())
        },
        |tail, _| {
            invalid_scope |=
                !matches!(tail.variable(), EffectRowVariable::Rigid(id) if allowed.contains(&id));
            Ok(())
        },
    )
    .map_err(|()| SelectionFailure::ConstraintResource)?;
    if invalid_scope {
        return Err(SelectionFailure::InvalidState);
    }
    while let Some(ty) = pending.pop() {
        constraint_work
            .charge(1)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        match ty {
            Type::Variable(variable) => {
                constraint_work
                    .charge(1)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                if !allowed.contains(variable) {
                    return Err(SelectionFailure::InvalidState);
                }
            }
            Type::Application(function, argument) | Type::Function(function, argument) => {
                constraint_work
                    .charge(2)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| SelectionFailure::ConstraintResource)?;
                pending.push(argument);
                pending.push(function);
            }
            Type::ResourceApply(_, arguments) | Type::ForeignOwnerApply(_, arguments) => {
                visit_owner_components_with_charge(
                    arguments.iter(),
                    &mut |cells| constraint_work.charge(cells),
                    |ty, _| {
                        pending.try_reserve(1).map_err(|_| ())?;
                        pending.push(ty);
                        Ok(())
                    },
                    |tail, _| {
            invalid_scope |= !matches!(tail.variable(), EffectRowVariable::Rigid(id) if allowed.contains(&id));
            Ok(())
        },
                )
                .map_err(|()| SelectionFailure::ConstraintResource)?;
                if invalid_scope {
                    return Err(SelectionFailure::InvalidState);
                }
            }
            Type::EffectfulFunction(domain, codomain) => {
                if let Some(variable) = codomain.tail_variable() {
                    match variable {
                        EffectRowVariable::Rigid(variable) if allowed.contains(&variable) => {}
                        EffectRowVariable::Rigid(_) | EffectRowVariable::Inference(_) => {
                            return Err(SelectionFailure::InvalidState);
                        }
                    }
                }
                let children = codomain.effect_argument_count().saturating_add(2);
                constraint_work
                    .charge(children)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                pending
                    .try_reserve(children)
                    .map_err(|_| SelectionFailure::ConstraintResource)?;
                visit_owner_components_with_charge(
                    codomain
                        .effects()
                        .known()
                        .iter()
                        .chain(
                            codomain
                                .effects()
                                .tail()
                                .into_iter()
                                .flat_map(|tail| tail.lacks()),
                        )
                        .flat_map(|instance| instance.arguments()),
                    &mut |cells| constraint_work.charge(cells),
                    |ty, _| {
                        pending.try_reserve(1).map_err(|_| ())?;
                        pending.push(ty);
                        Ok(())
                    },
                    |tail, _| {
            invalid_scope |= !matches!(tail.variable(), EffectRowVariable::Rigid(id) if allowed.contains(&id));
            Ok(())
        },
                )
                .map_err(|()| SelectionFailure::ConstraintResource)?;
                if invalid_scope {
                    return Err(SelectionFailure::InvalidState);
                }
                pending.push(&codomain.value);
                pending.push(domain);
            }
            Type::Tuple(elements) if elements.len() >= 2 => {
                constraint_work
                    .charge(elements.len())
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                pending
                    .try_reserve(elements.len())
                    .map_err(|_| SelectionFailure::ConstraintResource)?;
                pending.extend(elements.iter().rev());
            }
            Type::Tuple(_) | Type::Inference(_) | Type::Forall(_, _) => {
                return Err(SelectionFailure::InvalidState);
            }
            Type::Bytes | Type::String | Type::Int | Type::Bool | Type::Unit | Type::Nominal(_) => {
            }
        }
    }
    Ok(())
}

#[derive(Debug)]
struct ReplacementMap {
    values: HashMap<TypeVariableId, Type>,
}

struct EvidenceTypeBuffer(Vec<KindedArgument>);

impl EvidenceTypeBuffer {
    fn into_boxed_slice(mut self) -> Box<[KindedArgument]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for EvidenceTypeBuffer {
    fn drop(&mut self) {
        while let Some(ty) = self.0.pop() {
            discard_kinded_argument_iteratively(ty);
        }
    }
}

fn clone_local_prerequisite_arguments(
    arguments: &[crate::resolved::ResolvedOwnerArgument],
    type_work: &mut TypeWorkBudget,
) -> Result<EvidenceTypeBuffer, SelectionFailure> {
    type_work
        .charge(arguments.len())
        .map_err(|()| SelectionFailure::TypeResource)?;
    let mut cloned = EvidenceTypeBuffer(Vec::new());
    cloned
        .0
        .try_reserve_exact(arguments.len())
        .map_err(|_| SelectionFailure::TypeResource)?;
    for argument in arguments {
        cloned.0.push(
            clone_kinded_argument_with_budget(&argument.ty, type_work)
                .map_err(|()| SelectionFailure::TypeResource)?,
        );
    }
    Ok(cloned)
}

fn zonk_type<F>(ty: Type, zonk: &mut F, work: &mut TypeWorkBudget) -> Result<Type, SelectionFailure>
where
    F: FnMut(KindedArgument, &mut TypeWorkBudget) -> Result<KindedArgument, SelectionFailure>,
{
    match zonk(KindedArgument::TypeArg(ty), work)? {
        KindedArgument::TypeArg(ty) => Ok(ty),
        other => {
            discard_kinded_argument_iteratively(other);
            Err(SelectionFailure::InvalidState)
        }
    }
}

fn zonk_application<F>(
    application: InterfaceApplication,
    zonk: &mut F,
    type_work: &mut TypeWorkBudget,
) -> Result<InterfaceApplication, SelectionFailure>
where
    F: FnMut(KindedArgument, &mut TypeWorkBudget) -> Result<KindedArgument, SelectionFailure>,
{
    let (interface, arguments) = application.into_parts();
    type_work
        .charge(arguments.len())
        .map_err(|()| SelectionFailure::TypeResource)?;
    let mut pending = EvidenceTypeBuffer(arguments.into_vec());
    let mut checked = EvidenceTypeBuffer(Vec::new());
    checked
        .0
        .try_reserve(pending.0.len())
        .map_err(|_| SelectionFailure::TypeResource)?;
    pending.0.reverse();
    while let Some(argument) = pending.0.pop() {
        checked.0.push(zonk(argument, type_work)?);
    }
    Ok(InterfaceApplication::new_kinded(
        interface,
        checked.into_boxed_slice(),
    ))
}

fn authenticate_determination_positions(
    positions: &[usize],
    argument_count: usize,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<(), SelectionFailure> {
    if positions.is_empty() || positions.len() >= argument_count {
        return Err(SelectionFailure::InvalidState);
    }
    let mut previous = None;
    for &position in positions {
        constraint_work
            .charge(1)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        if position >= argument_count || previous.is_some_and(|previous| previous >= position) {
            return Err(SelectionFailure::InvalidState);
        }
        previous = Some(position);
    }
    Ok(())
}

fn clone_zonked_positions<F>(
    arguments: &[KindedArgument],
    positions: &[usize],
    zonk: &mut F,
    constraint_work: &mut InterfaceConstraintBudget,
    type_work: &mut TypeWorkBudget,
) -> Result<EvidenceTypeBuffer, SelectionFailure>
where
    F: FnMut(KindedArgument, &mut TypeWorkBudget) -> Result<KindedArgument, SelectionFailure>,
{
    type_work
        .charge(positions.len())
        .map_err(|()| SelectionFailure::TypeResource)?;
    let mut key = EvidenceTypeBuffer(Vec::new());
    key.0
        .try_reserve_exact(positions.len())
        .map_err(|_| SelectionFailure::TypeResource)?;
    for &position in positions {
        constraint_work
            .charge(1)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let argument = arguments
            .get(position)
            .ok_or(SelectionFailure::InvalidState)?;
        let cloned = clone_kinded_argument_with_budget(argument, type_work)
            .map_err(|()| SelectionFailure::TypeResource)?;
        key.0.push(zonk(cloned, type_work)?);
    }
    Ok(key)
}

fn position_references<'a>(
    arguments: &'a [KindedArgument],
    positions: &[usize],
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<Vec<&'a KindedArgument>, SelectionFailure> {
    constraint_work
        .charge(positions.len())
        .map_err(|()| SelectionFailure::ConstraintResource)?;
    let mut selected = Vec::new();
    selected
        .try_reserve_exact(positions.len())
        .map_err(|_| SelectionFailure::ConstraintResource)?;
    for &position in positions {
        selected.push(
            arguments
                .get(position)
                .ok_or(SelectionFailure::InvalidState)?,
        );
    }
    Ok(selected)
}

fn type_references<'a>(
    types: &'a [KindedArgument],
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<Vec<&'a KindedArgument>, SelectionFailure> {
    constraint_work
        .charge(types.len())
        .map_err(|()| SelectionFailure::ConstraintResource)?;
    let mut references = Vec::new();
    references
        .try_reserve_exact(types.len())
        .map_err(|_| SelectionFailure::ConstraintResource)?;
    references.extend(types);
    Ok(references)
}

fn clone_dependent_positions(
    arguments: &[KindedArgument],
    key_positions: &[usize],
    type_work: &mut TypeWorkBudget,
) -> Result<EvidenceTypeBuffer, SelectionFailure> {
    let dependent_count = arguments
        .len()
        .checked_sub(key_positions.len())
        .ok_or(SelectionFailure::InvalidState)?;
    type_work
        .charge(dependent_count)
        .map_err(|()| SelectionFailure::TypeResource)?;
    let mut dependents = EvidenceTypeBuffer(Vec::new());
    dependents
        .0
        .try_reserve_exact(dependent_count)
        .map_err(|_| SelectionFailure::TypeResource)?;
    let mut key_index = 0;
    for (position, argument) in arguments.iter().enumerate() {
        if key_positions.get(key_index) == Some(&position) {
            key_index += 1;
        } else {
            dependents.0.push(
                clone_kinded_argument_with_budget(argument, type_work)
                    .map_err(|()| SelectionFailure::TypeResource)?,
            );
        }
    }
    if key_index != key_positions.len() || dependents.0.len() != dependent_count {
        return Err(SelectionFailure::InvalidState);
    }
    Ok(dependents)
}

fn substitute_dependent_positions(
    arguments: &[KindedArgument],
    key_positions: &[usize],
    replacements: &HashMap<TypeVariableId, Type>,
    type_work: &mut TypeWorkBudget,
) -> Result<EvidenceTypeBuffer, SelectionFailure> {
    let dependent_count = arguments
        .len()
        .checked_sub(key_positions.len())
        .ok_or(SelectionFailure::InvalidState)?;
    type_work
        .charge(dependent_count)
        .map_err(|()| SelectionFailure::TypeResource)?;
    let mut dependents = EvidenceTypeBuffer(Vec::new());
    dependents
        .0
        .try_reserve_exact(dependent_count)
        .map_err(|_| SelectionFailure::TypeResource)?;
    let mut key_index = 0;
    for (position, argument) in arguments.iter().enumerate() {
        if key_positions.get(key_index) == Some(&position) {
            key_index += 1;
        } else {
            dependents.0.push(
                substitute_kinded_argument_with(argument, replacements, &HashMap::new(), |cells| {
                    type_work.charge(cells)
                })
                .map_err(|()| SelectionFailure::TypeResource)?
                .map_err(|_| SelectionFailure::InvalidState)?,
            );
        }
    }
    if key_index != key_positions.len() || dependents.0.len() != dependent_count {
        return Err(SelectionFailure::InvalidState);
    }
    Ok(dependents)
}

fn same_type_slices(
    left: &[&KindedArgument],
    right: &[KindedArgument],
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<bool, SelectionFailure> {
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left, right) in left.iter().zip(right) {
        if !same_kinded_argument_with_constraint_budget(left, right, constraint_work)
            .map_err(|()| SelectionFailure::ConstraintResource)?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn type_is_inference_free(
    root: &KindedArgument,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<bool, SelectionFailure> {
    constraint_work
        .charge(1)
        .map_err(|()| SelectionFailure::ConstraintResource)?;
    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| SelectionFailure::ConstraintResource)?;
    let mut row_inference = false;
    visit_owner_components_with_charge(
        std::iter::once(root),
        &mut |cells| constraint_work.charge(cells),
        |ty, _| {
            pending.try_reserve(1).map_err(|_| ())?;
            pending.push(ty);
            Ok(())
        },
        |tail, _| {
            row_inference |= matches!(tail.variable(), EffectRowVariable::Inference(_));
            Ok(())
        },
    )
    .map_err(|()| SelectionFailure::ConstraintResource)?;
    if row_inference {
        return Ok(false);
    }
    while let Some(ty) = pending.pop() {
        constraint_work
            .charge(1)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        match ty {
            Type::Inference(_) => return Ok(false),
            Type::ResourceApply(_, arguments) | Type::ForeignOwnerApply(_, arguments) => {
                visit_owner_components_with_charge(
                    arguments.iter(),
                    &mut |cells| constraint_work.charge(cells),
                    |ty, _| {
                        pending.try_reserve(1).map_err(|_| ())?;
                        pending.push(ty);
                        Ok(())
                    },
                    |tail, _| {
                        row_inference |= matches!(tail.variable(), EffectRowVariable::Inference(_));
                        Ok(())
                    },
                )
                .map_err(|()| SelectionFailure::ConstraintResource)?;
                if row_inference {
                    return Ok(false);
                }
            }
            Type::Tuple(elements) => {
                constraint_work
                    .charge(elements.len())
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                pending
                    .try_reserve(elements.len())
                    .map_err(|_| SelectionFailure::ConstraintResource)?;
                pending.extend(elements.iter().rev());
            }
            Type::Application(function, argument) | Type::Function(function, argument) => {
                constraint_work
                    .charge(2)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                pending
                    .try_reserve(2)
                    .map_err(|_| SelectionFailure::ConstraintResource)?;
                pending.push(argument);
                pending.push(function);
            }
            Type::EffectfulFunction(domain, codomain) => {
                if matches!(
                    codomain.tail_variable(),
                    Some(EffectRowVariable::Inference(_))
                ) {
                    return Ok(false);
                }
                let children = codomain.effect_argument_count().saturating_add(2);
                constraint_work
                    .charge(children)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                pending
                    .try_reserve(children)
                    .map_err(|_| SelectionFailure::ConstraintResource)?;
                visit_owner_components_with_charge(
                    codomain
                        .effects()
                        .known()
                        .iter()
                        .chain(
                            codomain
                                .effects()
                                .tail()
                                .into_iter()
                                .flat_map(|tail| tail.lacks()),
                        )
                        .flat_map(|instance| instance.arguments()),
                    &mut |cells| constraint_work.charge(cells),
                    |ty, _| {
                        pending.try_reserve(1).map_err(|_| ())?;
                        pending.push(ty);
                        Ok(())
                    },
                    |tail, _| {
                        row_inference |= matches!(tail.variable(), EffectRowVariable::Inference(_));
                        Ok(())
                    },
                )
                .map_err(|()| SelectionFailure::ConstraintResource)?;
                if row_inference {
                    return Ok(false);
                }
                pending.push(&codomain.value);
                pending.push(domain);
            }
            Type::Forall(_, _) => return Err(SelectionFailure::InvalidState),
            Type::Bytes
            | Type::String
            | Type::Int
            | Type::Bool
            | Type::Unit
            | Type::Nominal(_)
            | Type::Variable(_) => {}
        }
    }
    Ok(true)
}

pub(crate) fn same_applications_with_constraint_budget(
    left: &InterfaceApplication,
    right: &InterfaceApplication,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<bool, SelectionFailure> {
    if left.interface() != right.interface() || left.arguments().len() != right.arguments().len() {
        return Ok(false);
    }
    for (left, right) in left.arguments().iter().zip(right.arguments()) {
        if !same_kinded_argument_with_constraint_budget(left, right, constraint_work)
            .map_err(|()| SelectionFailure::ConstraintResource)?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

impl Drop for ReplacementMap {
    fn drop(&mut self) {
        for (_, value) in self.values.drain() {
            discard_type_iteratively(value);
        }
    }
}

impl ReplacementMap {
    fn new() -> Self {
        Self {
            values: HashMap::new(),
        }
    }

    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.values.try_reserve(additional)
    }

    fn try_insert_unique(
        &mut self,
        parameter: TypeVariableId,
        argument: IterativeTypeOwner,
    ) -> Result<(), SelectionFailure> {
        if let Some(displaced) = self.values.insert(parameter, argument.into_inner()) {
            discard_type_iteratively(displaced);
            return Err(SelectionFailure::InvalidState);
        }
        Ok(())
    }

    fn as_map(&self) -> &HashMap<TypeVariableId, Type> {
        &self.values
    }
}

fn replacement_map(
    substitution: &[EvidenceSubstitution],
    type_work: &mut TypeWorkBudget,
) -> Result<ReplacementMap, SelectionFailure> {
    let mut replacements = ReplacementMap::new();
    type_work
        .charge(substitution.len())
        .map_err(|()| SelectionFailure::TypeResource)?;
    replacements
        .try_reserve(substitution.len())
        .map_err(|_| SelectionFailure::TypeResource)?;
    for binding in substitution {
        let argument = IterativeTypeOwner::new(
            clone_type_with_budget(binding.argument(), type_work)
                .map_err(|()| SelectionFailure::TypeResource)?,
        );
        replacements.try_insert_unique(binding.parameter(), argument)?;
    }
    Ok(replacements)
}

#[derive(Debug)]
struct Goal {
    application: InterfaceApplication,
}

#[derive(Debug)]
enum SelectionTask {
    FinishFamily {
        key: Arc<GoalKey>,
        source_index: usize,
        application: InterfaceApplication,
        result_start: usize,
    },
    Select {
        goal: Goal,
        cause_marker: usize,
    },
    Finish {
        key: Arc<GoalKey>,
        candidate_index: usize,
        substitution: Box<[EvidenceSubstitution]>,
        result_start: usize,
    },
}

#[derive(Debug)]
struct SelectionWork(Vec<SelectionTask>);

impl SelectionWork {
    fn new(
        goal: Goal,
        cause_marker: usize,
        constraint_work: &mut InterfaceConstraintBudget,
    ) -> Result<Self, SelectionFailure> {
        constraint_work
            .charge(1)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        let mut tasks = Vec::new();
        tasks
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        tasks.push(SelectionTask::Select { goal, cause_marker });
        Ok(Self(tasks))
    }

    fn push(
        &mut self,
        task: SelectionTask,
        constraint_work: &mut InterfaceConstraintBudget,
    ) -> Result<(), SelectionFailure> {
        constraint_work
            .charge(1)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        self.0
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        self.0.push(task);
        Ok(())
    }

    fn pop(&mut self) -> Option<SelectionTask> {
        self.0.pop()
    }
}

fn reserve_selection_result<T>(
    results: &mut Vec<T>,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<(), SelectionFailure> {
    constraint_work
        .charge(1)
        .map_err(|()| SelectionFailure::ConstraintResource)?;
    results
        .try_reserve(1)
        .map_err(|_| SelectionFailure::ConstraintResource)
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct GoalKey {
    interface: InterfaceId,
    cells: Box<[GoalCell]>,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum GoalCell {
    Argument(usize),
    Bytes,
    String,
    Int,
    Bool,
    Unit,
    Nominal(NominalTypeId),
    Application,
    Tuple(usize),
    Function,
    EffectfulFunction,
    EffectRow(usize),
    TypeArgument,
    RowArgument,
    Resource(crate::types::ResourceDefinitionId, usize),
    ForeignOwner(NominalTypeId, usize),
    Tail(EffectRowVariable, usize),
    EffectInstance(crate::types::EffectId, usize),
    Variable(TypeVariableId),
}

fn goal_key(
    application: &InterfaceApplication,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<GoalKey, SelectionFailure> {
    enum Task<'a> {
        Type(&'a Type),
        Argument(&'a KindedArgument),
        Row(&'a crate::types::EffectRow),
        Instance(&'a crate::types::EffectInstance),
        Cell(GoalCell),
    }
    let mut pending = Vec::new();
    let mut cells = Vec::new();
    constraint_work
        .charge(
            application
                .arguments()
                .len()
                .checked_mul(2)
                .ok_or(SelectionFailure::ConstraintResource)?,
        )
        .map_err(|()| SelectionFailure::ConstraintResource)?;
    pending
        .try_reserve(
            application
                .arguments()
                .len()
                .checked_mul(2)
                .ok_or(SelectionFailure::ConstraintResource)?,
        )
        .map_err(|_| SelectionFailure::ConstraintResource)?;
    for (position, argument) in application.arguments().iter().enumerate().rev() {
        pending.push(Task::Argument(argument));
        pending.push(Task::Cell(GoalCell::Argument(position)));
    }
    while let Some(task) = pending.pop() {
        constraint_work
            .charge(1)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
        pending
            .try_reserve(4)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        cells
            .try_reserve(1)
            .map_err(|_| SelectionFailure::ConstraintResource)?;
        match task {
            Task::Cell(cell) => cells.push(cell),
            Task::Argument(KindedArgument::TypeArg(ty)) => {
                constraint_work
                    .charge(1)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                cells.push(GoalCell::TypeArgument);
                pending.push(Task::Type(ty));
            }
            Task::Argument(KindedArgument::RowArg(row)) => {
                constraint_work
                    .charge(1)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                cells.push(GoalCell::RowArgument);
                pending.push(Task::Row(row));
            }
            Task::Row(row) => {
                cells.push(GoalCell::EffectRow(row.known().len()));
                let count = row
                    .known()
                    .len()
                    .checked_add(row.tail().map_or(0, |tail| tail.lacks().len()))
                    .ok_or(SelectionFailure::ConstraintResource)?;
                constraint_work
                    .charge(count)
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                pending
                    .try_reserve(
                        count
                            .checked_add(1)
                            .ok_or(SelectionFailure::ConstraintResource)?,
                    )
                    .map_err(|_| SelectionFailure::ConstraintResource)?;
                if let Some(tail) = row.tail() {
                    if matches!(tail.variable(), EffectRowVariable::Inference(_)) {
                        return Err(SelectionFailure::Reason(InterfaceReason::Ambiguous));
                    }
                    constraint_work
                        .charge(1)
                        .map_err(|()| SelectionFailure::ConstraintResource)?;
                    pending.extend(tail.lacks().iter().rev().map(Task::Instance));
                    pending.push(Task::Cell(GoalCell::Tail(
                        tail.variable(),
                        tail.lacks().len(),
                    )));
                }
                pending.extend(row.known().iter().rev().map(Task::Instance));
            }
            Task::Instance(instance) => {
                cells.push(GoalCell::EffectInstance(
                    instance.effect(),
                    instance.arguments().len(),
                ));
                constraint_work
                    .charge(instance.arguments().len())
                    .map_err(|()| SelectionFailure::ConstraintResource)?;
                pending
                    .try_reserve(instance.arguments().len())
                    .map_err(|_| SelectionFailure::ConstraintResource)?;
                pending.extend(instance.arguments().iter().rev().map(Task::Argument));
            }
            Task::Type(ty) => match ty {
                Type::Bytes => cells.push(GoalCell::Bytes),
                Type::String => cells.push(GoalCell::String),
                Type::Int => cells.push(GoalCell::Int),
                Type::Bool => cells.push(GoalCell::Bool),
                Type::Unit => cells.push(GoalCell::Unit),
                Type::Nominal(id) => cells.push(GoalCell::Nominal(*id)),
                Type::Variable(id) => cells.push(GoalCell::Variable(*id)),
                Type::Inference(_) => {
                    return Err(SelectionFailure::Reason(InterfaceReason::Ambiguous));
                }
                Type::Forall(_, _) => return Err(SelectionFailure::InvalidState),
                Type::Tuple(elements) => {
                    cells.push(GoalCell::Tuple(elements.len()));
                    constraint_work
                        .charge(elements.len())
                        .map_err(|()| SelectionFailure::ConstraintResource)?;
                    pending
                        .try_reserve(elements.len())
                        .map_err(|_| SelectionFailure::ConstraintResource)?;
                    pending.extend(elements.iter().rev().map(Task::Type));
                }
                Type::ResourceApply(id, arguments) => {
                    cells.push(GoalCell::Resource(*id, arguments.len()));
                    constraint_work
                        .charge(arguments.len())
                        .map_err(|()| SelectionFailure::ConstraintResource)?;
                    pending
                        .try_reserve(arguments.len())
                        .map_err(|_| SelectionFailure::ConstraintResource)?;
                    pending.extend(arguments.iter().rev().map(Task::Argument));
                }
                Type::ForeignOwnerApply(id, arguments) => {
                    cells.push(GoalCell::ForeignOwner(*id, arguments.len()));
                    constraint_work
                        .charge(arguments.len())
                        .map_err(|()| SelectionFailure::ConstraintResource)?;
                    pending
                        .try_reserve(arguments.len())
                        .map_err(|_| SelectionFailure::ConstraintResource)?;
                    pending.extend(arguments.iter().rev().map(Task::Argument));
                }
                Type::Application(left, right) => {
                    constraint_work
                        .charge(2)
                        .map_err(|()| SelectionFailure::ConstraintResource)?;
                    cells.push(GoalCell::Application);
                    pending.push(Task::Type(right));
                    pending.push(Task::Type(left));
                }
                Type::Function(left, right) => {
                    constraint_work
                        .charge(2)
                        .map_err(|()| SelectionFailure::ConstraintResource)?;
                    cells.push(GoalCell::Function);
                    pending.push(Task::Type(right));
                    pending.push(Task::Type(left));
                }
                Type::EffectfulFunction(domain, codomain) => {
                    constraint_work
                        .charge(if codomain.effects().is_empty() { 2 } else { 3 })
                        .map_err(|()| SelectionFailure::ConstraintResource)?;
                    if codomain.effects().is_empty() {
                        cells.push(GoalCell::Function);
                    } else {
                        cells.push(GoalCell::EffectfulFunction);
                        pending.push(Task::Row(codomain.effects()));
                    }
                    pending.push(Task::Type(codomain.value()));
                    pending.push(Task::Type(domain));
                }
            },
        }
    }
    Ok(GoalKey {
        interface: application.interface(),
        cells: cells.into_boxed_slice(),
    })
}

fn charge_goal_key(
    key: &GoalKey,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<(), SelectionFailure> {
    constraint_work
        .charge(key.cells.len().saturating_add(1))
        .map_err(|()| SelectionFailure::ConstraintResource)
}

fn charge_candidate_inspection(
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<(), SelectionFailure> {
    constraint_work
        .charge(1)
        .map_err(|()| SelectionFailure::ConstraintResource)
}

fn charge_prerequisite_goal(
    application: &InterfaceApplication,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<(), SelectionFailure> {
    constraint_work
        .charge(1)
        .map_err(|()| SelectionFailure::ConstraintResource)?;
    for argument in application.arguments() {
        constraint_work
            .charge_argument(argument)
            .map_err(|()| SelectionFailure::ConstraintResource)?;
    }
    Ok(())
}

fn retain_selection_cause(
    causes: &mut Vec<SelectionCause>,
    kind: SelectionCauseKind,
    span: Span,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<(), SelectionFailure> {
    constraint_work
        .charge(1)
        .map_err(|()| SelectionFailure::ConstraintResource)?;
    causes
        .try_reserve(1)
        .map_err(|_| SelectionFailure::ConstraintResource)?;
    causes.push(SelectionCause { kind, span });
    Ok(())
}

#[cfg(test)]
fn same_type_with_constraint_budget(
    left: &Type,
    right: &Type,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<bool, ()> {
    same_semantic_type_with_constraint_budget(left, right, constraint_work)
}

#[cfg(test)]
mod tests {
    use super::*;
    trait TestArgument {
        fn into_argument(self) -> KindedArgument;
    }
    impl TestArgument for Type {
        fn into_argument(self) -> KindedArgument {
            KindedArgument::TypeArg(self)
        }
    }
    impl TestArgument for KindedArgument {
        fn into_argument(self) -> KindedArgument {
            self
        }
    }
    fn test_application<T: TestArgument>(
        interface: InterfaceId,
        arguments: Box<[T]>,
    ) -> InterfaceApplication {
        InterfaceApplication::new_kinded(
            interface,
            arguments
                .into_vec()
                .into_iter()
                .map(TestArgument::into_argument)
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        )
    }

    #[test]
    fn ingress_kind_failure_retains_cause() {
        let source = SourceFile::new("declaration.ash", "binder").unwrap();
        let span = source.span(ByteRange::new(0, 6).unwrap()).unwrap();
        let mut environments = crate::kind::KindEnvironments::new();
        let identity = TypeVariableId::new(0);
        let kind = Kind::Type;
        environments
            .insert_declared(identity, &kind, span, &mut TypeWorkBudget::with_limit(1))
            .unwrap();
        let error = environments
            .insert_declared(identity, &kind, span, &mut TypeWorkBudget::with_limit(1))
            .unwrap_err();
        let context = error.internal_context().unwrap();
        assert_eq!(
            map_head_failure(HeadMatchFailure::Kind(context)),
            SelectionFailure::Kind {
                context,
                span: None
            }
        );
        assert_eq!(
            map_ingress_environment_failure(CanonicalEnvironmentFailure::Kind(context)),
            SelectionFailure::Kind {
                context,
                span: None
            }
        );
        assert_eq!(
            map_ingress_kind_failure(error),
            SelectionFailure::Kind {
                context,
                span: None
            }
        );
        let resource = crate::kind::KindEnvironments::new()
            .insert_declared(identity, &kind, span, &mut TypeWorkBudget::with_limit(0))
            .unwrap_err();
        assert_eq!(
            map_ingress_kind_failure(resource),
            SelectionFailure::ConstraintResource
        );
    }
    use crate::{
        interface::{
            CheckedImplMethod, CheckedRequirement, EvidenceNode, EvidenceSlot, RequirementOwner,
        },
        module::ModuleId,
        resolved::{
            Binder, BinderId, CheckedImplementationFact, CheckedImplementationMethodFact,
            CheckedInterfaceFact, CheckedInterfaceMethodFact, ImplementationAuthorization,
            ImplementationRouteHop, ResolvedImplementation, ResolvedImplementationMethodGroup,
            ResolvedInterfaceApplication, ResolvedInterfaceOccurrence, ResolvedNominalType,
            ResolvedOwnerArgument, ResolvedRequirement, ResolvedTypeProvenance,
            ResolvedTypeProvenanceNode, ResolvedTypeVariable,
        },
        source::{ByteRange, Origin, SourceFile},
    };

    fn ids() -> (InterfaceId, MethodId, RequirementId) {
        let module = ModuleId::new(1);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let requirement =
            RequirementId::new(RequirementOwner::Global(BinderId::resolved(module, 0)), 0);
        (interface, method, requirement)
    }

    fn unary_application(interface: InterfaceId, argument: Type) -> InterfaceApplication {
        test_application(interface, Box::new([KindedArgument::TypeArg(argument)]))
    }

    fn unary_argument(application: &InterfaceApplication) -> &Type {
        let [argument] = application.arguments() else {
            panic!("the unary fixture should retain exactly one interface argument");
        };
        let KindedArgument::TypeArg(argument) = argument else {
            panic!("unary fixture argument is Type");
        };
        argument
    }

    fn unary_parameter(fact: &CheckedInterfaceFact) -> &ResolvedTypeVariable {
        let [parameter] = fact.parameters.as_ref() else {
            panic!("the unary fixture should retain exactly one interface parameter");
        };
        parameter
    }

    fn interface_fact_with_kind(kind: Kind) -> CheckedInterfaceFact {
        let file = SourceFile::new("selection-kind-fixture.ash", "Interface")
            .expect("interface fixture source");
        let span = file
            .span(ByteRange::new(0, 9).expect("interface fixture range"))
            .expect("interface fixture span");
        let interface = InterfaceId::new(ModuleId::from(file.id()), 0);
        CheckedInterfaceFact::without_methods_for_test(
            interface,
            "Interface".to_owned(),
            Box::new([ResolvedTypeVariable {
                id: TypeVariableId::resolved(ModuleId::from(file.id()), 0),
                spelling: "F".to_owned(),
                kind,
                origin: Origin::Source(span),
            }]),
            Origin::Source(span),
            span,
        )
    }

    fn registry_for_interface_fact(fact: &CheckedInterfaceFact) -> ResolvedRegistry {
        let mut variables = fact.parameters.to_vec();
        for method in &fact.methods {
            variables.extend(
                method
                    .authoritative_type_parameters()
                    .iter()
                    .map(|parameter| ResolvedTypeVariable {
                        id: parameter.id,
                        spelling: parameter.spelling.clone(),
                        kind: parameter.kind.clone(),
                        origin: parameter.origin.clone(),
                    }),
            );
        }
        ResolvedRegistry::new(Vec::new(), Vec::new()).with_additional_type_variables(variables)
    }

    struct IsolatedRigidityFixture {
        selector: EvidenceSelector,
        registry: ResolvedRegistry,
        target: MethodRigidityTarget,
        missing_interface: InterfaceId,
        repeat_interface: InterfaceId,
        current: ImplId,
        missing_slot: EvidenceSlot,
        repeat_slot: EvidenceSlot,
    }

    fn isolated_rigidity_fixture() -> IsolatedRigidityFixture {
        let module = ModuleId::new(111);
        let missing_interface = InterfaceId::new(module, 0);
        let repeat_interface = InterfaceId::new(module, 1);
        let missing_method = MethodId::new(missing_interface, 0);
        let repeat_method = MethodId::new(repeat_interface, 0);
        let current = ImplId::new(module, 0);
        let source = SourceFile::new("isolated-method-rigidity.ash", "missing repeat argument")
            .expect("the isolated rigidity source should fit");
        let missing_span = source
            .span(ByteRange::new(0, 7).expect("the missing range should be ordered"))
            .expect("the missing span should fit");
        let occurrence_span = source
            .span(ByteRange::new(8, 14).expect("the repeat range should be ordered"))
            .expect("the repeat occurrence span should fit");
        let application_span = source
            .span(ByteRange::new(8, 23).expect("the application range should be ordered"))
            .expect("the application span should fit");
        let argument_span = source
            .span(ByteRange::new(15, 23).expect("the argument range should be ordered"))
            .expect("the argument span should fit");
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            missing_interface,
            TypeVariableId::resolved(module, 0),
            vec![(missing_method, Type::Unit)],
        );
        selector.add_interface_raw(
            repeat_interface,
            TypeVariableId::resolved(module, 1),
            vec![(repeat_method, Type::Unit)],
        );
        selector.add_implementation_raw(implementation(
            current,
            repeat_interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(current, repeat_method)],
        ));
        let registry = selector.canonical_registry_for_test();
        selector
            .enter_implementation_scope(
                current,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the current implementation scope should fit");
        let marker = selector.pending_marker();
        let missing_slot = EvidenceSlot::empty();
        selector
            .push_owned_obligation(
                test_application(missing_interface, Box::new([Type::Int])),
                SelectionSite::plain(missing_slot.handle(), missing_span),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the unrelated missing obligation should stage first");
        let repeat_slot = EvidenceSlot::empty();
        selector
            .push_cloned_obligation(
                &test_application(repeat_interface, Box::new([Type::Int])),
                MethodObligationMetadata::new(
                    MethodId::new(repeat_interface, 0),
                    Box::new([Type::Bool]),
                    Some(MethodRigidityCondition::new(
                        Box::new([Type::Int]),
                        MethodRigiditySite::application(
                            occurrence_span,
                            application_span,
                            argument_span,
                        ),
                    )),
                ),
                SelectionSite::plain(repeat_slot.handle(), occurrence_span),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the matching conditional obligation should stage second");
        IsolatedRigidityFixture {
            selector,
            registry,
            target: MethodRigidityTarget::new(marker, application_span),
            missing_interface,
            repeat_interface,
            current,
            missing_slot,
            repeat_slot,
        }
    }

    #[test]
    fn failed_body_rigidity_matching_has_deterministic_causal_tiers() {
        let module = ModuleId::new(112);
        let interface = InterfaceId::new(module, 0);
        let source = SourceFile::new(
            "method-rigidity-matching.ash",
            "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx",
        )
        .expect("the matching-tier source should fit");
        let span = |start, end| {
            source
                .span(ByteRange::new(start, end).expect("the matching range should be ordered"))
                .expect("the matching span should fit")
        };
        let failure = span(6, 20);
        let first_argument_match =
            MethodRigiditySite::application(span(0, 5), span(0, 25), failure);
        let second_argument_match =
            MethodRigiditySite::application(span(1, 5), span(0, 30), failure);
        let whole_application_match =
            MethodRigiditySite::application(span(6, 11), failure, span(12, 20));
        let duplicate_whole_application =
            MethodRigiditySite::application(span(7, 11), failure, span(13, 20));
        let occurrence_only = MethodRigiditySite::occurrence(failure);
        let nonmatching = MethodRigiditySite::application(span(21, 25), span(21, 35), span(26, 35));
        let selector_for = |sites: &[MethodRigiditySite]| {
            let mut selector = EvidenceSelector::new();
            for site in sites {
                selector
                    .push_cloned_obligation(
                        &unary_application(interface, Type::Int),
                        MethodObligationMetadata::new(
                            MethodId::new(interface, 0),
                            Box::new([Type::Bool]),
                            Some(MethodRigidityCondition::new(Box::new([Type::Int]), *site)),
                        ),
                        SelectionSite::plain(
                            EvidenceSlot::empty().handle(),
                            site.occurrence_span(),
                        ),
                        &mut InterfaceConstraintBudget::default(),
                        &mut TypeWorkBudget::default(),
                    )
                    .expect("the matching-tier condition should stage");
            }
            selector
        };
        let target = MethodRigidityTarget::new(PendingObligationMarker::for_test(0, 0), failure);

        assert_eq!(
            selector_for(&[nonmatching]).matching_method_rigidity_index(target),
            Ok(None)
        );
        assert_eq!(
            selector_for(&[first_argument_match]).matching_method_rigidity_index(target),
            Ok(Some(0))
        );
        assert_eq!(
            selector_for(&[occurrence_only]).matching_method_rigidity_index(target),
            Ok(Some(0))
        );
        assert_eq!(
            selector_for(&[
                first_argument_match,
                second_argument_match,
                whole_application_match,
            ])
            .matching_method_rigidity_index(target),
            Ok(Some(2)),
            "one whole-application match should outrank duplicate argument matches"
        );
        assert_eq!(
            selector_for(&[whole_application_match, duplicate_whole_application])
                .matching_method_rigidity_index(target),
            Err(SelectionFailure::InvalidState)
        );
        assert_eq!(
            selector_for(&[first_argument_match, second_argument_match])
                .matching_method_rigidity_index(target),
            Err(SelectionFailure::InvalidState)
        );
    }

    fn assert_isolated_rigidity_fixture_unmodified(fixture: &IsolatedRigidityFixture) {
        assert_eq!(fixture.selector.pending.len(), 2);
        assert_eq!(
            fixture.selector.pending[0].application.interface(),
            fixture.missing_interface
        );
        assert_eq!(
            fixture.selector.pending[1].application.interface(),
            fixture.repeat_interface
        );
        assert_eq!(fixture.selector.pending_method_rigidity_count, 1);
        assert!(fixture.selector.selected.is_empty());
        assert_eq!(fixture.selector.method_rigidity_count(), 0);
        assert!(fixture.missing_slot.selection().is_none());
        assert!(fixture.repeat_slot.selection().is_none());
    }

    #[test]
    fn isolated_method_rigidity_close_skips_earlier_unrelated_selection_failure() {
        let IsolatedRigidityFixture {
            mut selector,
            registry,
            target,
            missing_interface,
            repeat_interface: _,
            current,
            missing_slot,
            repeat_slot,
        } = isolated_rigidity_fixture();

        assert!(
            selector
                .close_method_rigidity_with_registry(
                    &registry,
                    target,
                    |ty, _| Ok(ty),
                    &mut InterfaceConstraintBudget::default(),
                    &mut TypeWorkBudget::default(),
                )
                .expect("only the matching exact-current obligation should close")
        );

        assert_eq!(selector.pending.len(), 1);
        assert_eq!(
            selector.pending[0].application.interface(),
            missing_interface
        );
        assert_eq!(selector.pending_method_rigidity_count, 0);
        assert_eq!(selector.selected.len(), 1);
        assert_eq!(selector.method_rigidity_count(), 1);
        let check = selector
            .method_rigidity(0)
            .expect("the matching occurrence should retain one rigidity relation");
        assert_eq!(check.method_arguments(), &[Type::Bool]);
        assert_eq!(check.rigid_arguments(), &[Type::Int]);
        let selection = selector.selected[0]
            .selection
            .as_ref()
            .expect("the matching occurrence should retain private selection");
        assert!(matches!(
            selection.node(selection.root()),
            Some(EvidenceNode::Implementation { implementation, .. })
                if implementation == current
        ));
        assert!(missing_slot.selection().is_none());
        assert!(repeat_slot.selection().is_none());
        assert!(matches!(
            selector.prepare_publication(
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::InvalidState)
        ));
        assert!(missing_slot.selection().is_none());
        assert!(repeat_slot.selection().is_none());
    }

    #[test]
    fn isolated_method_rigidity_close_has_exact_atomic_retry_boundaries() {
        // Complete owner arguments retain explicit scope/kind/tag records;
        // local source mirrors additionally compare the argument tags.
        // Complete-application matching adds three aligned carrier cells to
        // the prior scalar constraint path. Three application clones and one
        // zonk vector add four Type-work cells to the three Type nodes.
        const EXACT_CONSTRAINT_WORK: usize = 25 + 3 + 6;
        const EXACT_TYPE_WORK: usize = 3 + 4;

        let mut measured = isolated_rigidity_fixture();
        let mut no_condition = EvidenceSelector::new();
        assert!(
            !no_condition
                .close_method_rigidity_with_registry(
                    &measured.registry,
                    MethodRigidityTarget::new(
                        no_condition.pending_marker(),
                        measured.target.failure_span(),
                    ),
                    |ty, _| Ok(ty),
                    &mut InterfaceConstraintBudget::with_limit(0),
                    &mut TypeWorkBudget::with_limit(0),
                )
                .expect("the no-condition fast path should consume no resource")
        );
        let mut measured_constraints = InterfaceConstraintBudget::default();
        let mut measured_types = TypeWorkBudget::default();
        assert!(
            measured
                .selector
                .close_method_rigidity_with_registry(
                    &measured.registry,
                    measured.target,
                    |ty, _| Ok(ty),
                    &mut measured_constraints,
                    &mut measured_types,
                )
                .expect("the measured isolated close should select exact-current evidence")
        );
        let exact_constraints = measured_constraints.used();
        let exact_types = measured_types.used();
        assert_eq!(exact_constraints, EXACT_CONSTRAINT_WORK);
        assert_eq!(exact_types, EXACT_TYPE_WORK);

        let mut constraint_short = isolated_rigidity_fixture();
        let error = constraint_short
            .selector
            .close_method_rigidity_with_registry(
                &constraint_short.registry,
                constraint_short.target,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::with_limit(exact_constraints - 1),
                &mut TypeWorkBudget::with_limit(exact_types),
            )
            .expect_err("one-short constraint work should reject before selector mutation");
        assert_eq!(error.failure(), SelectionFailure::ConstraintResource);
        assert_isolated_rigidity_fixture_unmodified(&constraint_short);
        let mut exact_constraint_retry = InterfaceConstraintBudget::with_limit(exact_constraints);
        let mut exact_type_retry = TypeWorkBudget::with_limit(exact_types);
        assert!(
            constraint_short
                .selector
                .close_method_rigidity_with_registry(
                    &constraint_short.registry,
                    constraint_short.target,
                    |ty, _| Ok(ty),
                    &mut exact_constraint_retry,
                    &mut exact_type_retry,
                )
                .expect("the exact retry should close only the matching obligation")
        );
        assert_eq!(exact_constraint_retry.used(), exact_constraints);
        assert_eq!(exact_type_retry.used(), exact_types);

        let mut type_short = isolated_rigidity_fixture();
        let error = type_short
            .selector
            .close_method_rigidity_with_registry(
                &type_short.registry,
                type_short.target,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::with_limit(exact_constraints),
                &mut TypeWorkBudget::with_limit(exact_types - 1),
            )
            .expect_err("one-short type work should reject before selector mutation");
        assert_eq!(error.failure(), SelectionFailure::TypeResource);
        assert_isolated_rigidity_fixture_unmodified(&type_short);
        let mut exact_constraint_retry = InterfaceConstraintBudget::with_limit(exact_constraints);
        let mut exact_type_retry = TypeWorkBudget::with_limit(exact_types);
        assert!(
            type_short
                .selector
                .close_method_rigidity_with_registry(
                    &type_short.registry,
                    type_short.target,
                    |ty, _| Ok(ty),
                    &mut exact_constraint_retry,
                    &mut exact_type_retry,
                )
                .expect("the exact type retry should preserve the matching relation")
        );
        assert_eq!(exact_constraint_retry.used(), exact_constraints);
        assert_eq!(exact_type_retry.used(), exact_types);

        let mut invalid = isolated_rigidity_fixture();
        let invalid_target = MethodRigidityTarget::new(
            PendingObligationMarker::for_test(
                invalid.selector.pending.len() + 1,
                invalid.selector.pending_determined_count,
            ),
            invalid.target.failure_span(),
        );
        let error = invalid
            .selector
            .close_method_rigidity_with_registry(
                &invalid.registry,
                invalid_target,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect_err("an invalid marker should reject without selector mutation");
        assert_eq!(error.failure(), SelectionFailure::InvalidState);
        assert_isolated_rigidity_fixture_unmodified(&invalid);

        let mut duplicate = isolated_rigidity_fixture();
        let duplicate_site = duplicate.selector.pending[1]
            .method_rigidity
            .as_ref()
            .expect("the fixture should retain the matching condition")
            .site;
        let duplicate_slot = EvidenceSlot::empty();
        duplicate
            .selector
            .push_cloned_obligation(
                &unary_application(duplicate.repeat_interface, Type::Int),
                MethodObligationMetadata::new(
                    MethodId::new(duplicate.repeat_interface, 0),
                    Box::new([Type::Bool]),
                    Some(MethodRigidityCondition::new(
                        Box::new([Type::Int]),
                        duplicate_site,
                    )),
                ),
                SelectionSite::plain(duplicate_slot.handle(), duplicate_site.occurrence_span()),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the duplicate matching condition should stage");
        let error = duplicate
            .selector
            .close_method_rigidity_with_registry(
                &duplicate.registry,
                duplicate.target,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect_err("two matching source sites should reject without selection");
        assert_eq!(error.failure(), SelectionFailure::InvalidState);
        assert_eq!(duplicate.selector.pending.len(), 3);
        assert_eq!(duplicate.selector.pending_method_rigidity_count, 2);
        assert!(duplicate.selector.selected.is_empty());
        assert_eq!(duplicate.selector.method_rigidity_count(), 0);
        assert!(duplicate.missing_slot.selection().is_none());
        assert!(duplicate.repeat_slot.selection().is_none());
        assert!(duplicate_slot.selection().is_none());
    }

    #[test]
    fn isolated_method_rigidity_close_charges_the_exact_removal_shift() {
        // Complete owner arguments retain explicit scope/kind/tag records;
        // local source mirrors additionally compare the argument tags.
        const EXACT_CONSTRAINT_WORK: usize = 27 + 3 + 6;
        const EXACT_TYPE_WORK: usize = 3 + 4;

        let mut fixture = isolated_rigidity_fixture();
        let trailing_slot = EvidenceSlot::empty();
        fixture
            .selector
            .push_owned_obligation(
                unary_application(fixture.missing_interface, Type::Bool),
                SelectionSite::plain(trailing_slot.handle(), fixture.target.failure_span()),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the trailing unrelated obligation should stage");

        let error = fixture
            .selector
            .close_method_rigidity_with_registry(
                &fixture.registry,
                fixture.target,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1),
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
            )
            .expect_err("one-short shifted removal should reject without selector mutation");
        assert_eq!(error.failure(), SelectionFailure::ConstraintResource);
        assert_eq!(fixture.selector.pending.len(), 3);
        assert_eq!(
            unary_argument(&fixture.selector.pending[0].application),
            &Type::Int
        );
        assert_eq!(
            unary_argument(&fixture.selector.pending[1].application),
            &Type::Int
        );
        assert_eq!(
            unary_argument(&fixture.selector.pending[2].application),
            &Type::Bool
        );
        assert_eq!(fixture.selector.pending_method_rigidity_count, 1);
        assert!(fixture.selector.selected.is_empty());
        assert_eq!(fixture.selector.method_rigidity_count(), 0);
        assert!(fixture.missing_slot.selection().is_none());
        assert!(fixture.repeat_slot.selection().is_none());
        assert!(trailing_slot.selection().is_none());

        let mut exact_constraints = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        let mut exact_types = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
        assert!(
            fixture
                .selector
                .close_method_rigidity_with_registry(
                    &fixture.registry,
                    fixture.target,
                    |ty, _| Ok(ty),
                    &mut exact_constraints,
                    &mut exact_types,
                )
                .expect("the exact shifted-removal retry should succeed")
        );
        assert_eq!(exact_constraints.used(), EXACT_CONSTRAINT_WORK);
        assert_eq!(exact_types.used(), EXACT_TYPE_WORK);
        assert_eq!(fixture.selector.pending.len(), 2);
        assert_eq!(
            unary_argument(&fixture.selector.pending[0].application),
            &Type::Int
        );
        assert_eq!(
            unary_argument(&fixture.selector.pending[1].application),
            &Type::Bool
        );
        assert_eq!(fixture.selector.pending_method_rigidity_count, 0);
        assert_eq!(fixture.selector.selected.len(), 1);
        assert_eq!(fixture.selector.method_rigidity_count(), 1);
        assert!(fixture.missing_slot.selection().is_none());
        assert!(fixture.repeat_slot.selection().is_none());
        assert!(trailing_slot.selection().is_none());
    }

    #[test]
    fn interface_selector_method_scheme_has_exact_atomic_dual_boundaries() {
        // Binder and index admission costs ten cells; the shared clone
        // preflight visits the five method-type cells once in each ledger.
        const EXACT_CONSTRAINT_WORK: usize = 10 + 5;

        let setup = || {
            let mut fact = interface_fact_with_kind(Kind::Type);
            let method_parameter = TypeVariableId::resolved(fact.id.module(), 1);
            fact.methods = Box::new([
                CheckedInterfaceMethodFact::with_mirrored_binder_authority_for_test(
                    MethodId::new(fact.id, 0),
                    "apply".to_owned(),
                    Box::new([ResolvedTypeVariable {
                        id: method_parameter,
                        spelling: "F".to_owned(),
                        kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                        origin: Origin::Source(fact.span),
                    }]),
                    Type::Function(
                        Box::new(Type::Variable(unary_parameter(&fact).id)),
                        Box::new(Type::Application(
                            Box::new(Type::Variable(method_parameter)),
                            Box::new(Type::Variable(unary_parameter(&fact).id)),
                        )),
                    ),
                    Origin::Source(fact.span),
                    fact.span,
                    fact.span,
                )
                .with_inherited_parameters(
                    crate::resolved::OwnerId::Interface(fact.id),
                    &fact.parameters,
                    &mut TypeWorkBudget::unbounded(),
                )
                .expect("fixture inherited owner roles"),
            ]);
            let registry = registry_for_interface_fact(&fact);
            (fact, registry, method_parameter)
        };
        let run = |constraint_limit, type_limit| {
            let (fact, registry, method_parameter) = setup();
            let mut selector = EvidenceSelector::new();
            let mut constraints = InterfaceConstraintBudget::with_limit(constraint_limit);
            let mut types = TypeWorkBudget::with_limit(type_limit);
            let result =
                selector.add_interface_fact(&registry, &fact, &mut constraints, &mut types);
            (
                result,
                selector,
                method_parameter,
                constraints.used(),
                types.used(),
            )
        };

        let (measured, selector, method_parameter, exact_constraints, exact_types) =
            run(usize::MAX, usize::MAX);
        measured.expect("the measured method scheme should publish atomically");
        assert_eq!(exact_constraints, EXACT_CONSTRAINT_WORK);
        let method = selector
            .method(selector.interfaces[0].methods[0].id)
            .expect("the selector should retain the method scheme");
        assert_eq!(
            method.type_parameters(),
            &[(
                method_parameter,
                Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type))
            )]
        );

        let (constraint_short, selector, _, _, _) = run(exact_constraints - 1, exact_types);
        assert!(matches!(
            constraint_short,
            Err(SelectionFailure::ConstraintResource)
        ));
        assert!(selector.interfaces.is_empty());

        let (type_short, selector, _, _, _) = run(exact_constraints, exact_types - 1);
        assert!(matches!(type_short, Err(SelectionFailure::TypeResource)));
        assert!(selector.interfaces.is_empty());

        let (exact, selector, _, used_constraints, used_types) =
            run(exact_constraints, exact_types);
        exact.expect("the exact method-scheme budgets should publish atomically");
        assert_eq!(used_constraints, exact_constraints);
        assert_eq!(used_types, exact_types);
        assert_eq!(selector.interfaces.len(), 1);
    }

    #[test]
    fn deep_method_clone_ingress_has_atomic_dual_budget_retries() {
        const DEPTH: usize = 16_384;
        const METHOD_CELLS: usize = 2 * DEPTH + 3;
        // Three interface-parameter checks and two method-index cells precede
        // the two cloned methods. Type retention also owns one binder and Kind.
        const CONSTRAINT_WORK: usize = 5 + 2 * METHOD_CELLS;
        const TYPE_WORK: usize = 4 + 2 * METHOD_CELLS; // two inherited owner-role checks
        std::thread::Builder::new()
            .name("deep-method-clone-ingress".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut fact = interface_fact_with_kind(Kind::Type);
                fact.methods = (0..2)
                    .map(|index| {
                        CheckedInterfaceMethodFact::with_mirrored_binder_authority_for_test(
                            MethodId::new(fact.id, index),
                            format!("method{index}"),
                            Box::new([]),
                            Type::Function(
                                Box::new(Type::Variable(unary_parameter(&fact).id)),
                                Box::new(deep_value_type(DEPTH)),
                            ),
                            Origin::Source(fact.span),
                            fact.span,
                            fact.span,
                        )
                        .with_inherited_parameters(
                            crate::resolved::OwnerId::Interface(fact.id),
                            &fact.parameters,
                            &mut TypeWorkBudget::unbounded(),
                        )
                        .expect("fixture inherited owner roles")
                    })
                    .collect();
                let registry = registry_for_interface_fact(&fact);
                for (constraint_limit, type_limit, expected) in [
                    (
                        CONSTRAINT_WORK - 1,
                        TYPE_WORK,
                        SelectionFailure::ConstraintResource,
                    ),
                    (
                        CONSTRAINT_WORK,
                        TYPE_WORK - 1,
                        SelectionFailure::TypeResource,
                    ),
                ] {
                    let mut selector = EvidenceSelector::new();
                    assert_eq!(
                        selector.add_interface_fact(
                            &registry,
                            &fact,
                            &mut InterfaceConstraintBudget::with_limit(constraint_limit),
                            &mut TypeWorkBudget::with_limit(type_limit),
                        ),
                        Err(expected),
                    );
                    assert!(selector.interfaces.is_empty());
                    assert!(selector.interface_indices.is_empty());
                    assert!(selector.method_indices.is_empty());
                    let mut constraints = InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
                    let mut types = TypeWorkBudget::with_limit(TYPE_WORK);
                    selector
                        .add_interface_fact(&registry, &fact, &mut constraints, &mut types)
                        .expect("fresh exact ledgers should retry both deep methods");
                    assert_eq!(constraints.used(), CONSTRAINT_WORK);
                    assert_eq!(types.used(), TYPE_WORK);
                    assert_eq!(selector.interfaces[0].methods.len(), 2);
                }
            })
            .expect("the deep method-clone worker should spawn")
            .join()
            .expect("staged and published deep methods must dispose iteratively");
    }

    #[test]
    fn wide_method_scheme_ingress_charges_retained_and_duplicate_indexes() {
        const WIDTH: usize = 1_024;
        // Four cells per method binder, one per cloned tuple element, and
        // seven fixed interface, method-index, and outer-type cells.
        const EXACT_CONSTRAINT_WORK: usize = WIDTH * 5 + 7;
        const EXACT_TYPE_WORK: usize = WIDTH * 3 + 6; // one inherited owner-role check

        let setup = || {
            let mut fact = interface_fact_with_kind(Kind::Type);
            let mut parameters = Vec::new();
            parameters
                .try_reserve(WIDTH)
                .expect("the wide parameter fixture should fit");
            for index in 0..WIDTH {
                parameters.push(ResolvedTypeVariable {
                    id: TypeVariableId::resolved(
                        fact.id.module(),
                        u32::try_from(index + 1)
                            .expect("the wide parameter ordinal should fit u32"),
                    ),
                    spelling: format!("T{index}"),
                    kind: Kind::Type,
                    origin: Origin::Source(fact.span),
                });
            }
            let values = parameters
                .iter()
                .map(|parameter| Type::Variable(parameter.id))
                .collect::<Vec<_>>()
                .into_boxed_slice();
            fact.methods = Box::new([
                CheckedInterfaceMethodFact::with_mirrored_binder_authority_for_test(
                    MethodId::new(fact.id, 0),
                    "wide".to_owned(),
                    parameters.into_boxed_slice(),
                    Type::Function(
                        Box::new(Type::Variable(unary_parameter(&fact).id)),
                        Box::new(Type::Tuple(values)),
                    ),
                    Origin::Source(fact.span),
                    fact.span,
                    fact.span,
                )
                .with_inherited_parameters(
                    crate::resolved::OwnerId::Interface(fact.id),
                    &fact.parameters,
                    &mut TypeWorkBudget::unbounded(),
                )
                .expect("fixture inherited owner roles"),
            ]);
            let registry = registry_for_interface_fact(&fact);
            (fact, registry)
        };
        let (fact, registry) = setup();
        let mut selector = EvidenceSelector::new();
        let short = selector.add_interface_fact(
            &registry,
            &fact,
            &mut InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1),
            &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
        );
        assert_eq!(short, Err(SelectionFailure::ConstraintResource));
        assert!(selector.interfaces.is_empty());
        assert!(selector.interface_indices.is_empty());
        assert!(selector.method_indices.is_empty());

        let mut exact_constraints = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        let mut exact_types = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
        selector
            .add_interface_fact(&registry, &fact, &mut exact_constraints, &mut exact_types)
            .expect("the exact wide dual-index retry should publish");
        assert_eq!(exact_constraints.used(), EXACT_CONSTRAINT_WORK);
        assert_eq!(exact_types.used(), EXACT_TYPE_WORK);
        assert_eq!(selector.interfaces.len(), 1);
        assert_eq!(
            selector.interfaces[0].methods[0].type_parameters.len(),
            WIDTH
        );
    }

    #[test]
    fn publication_preflight_rejects_without_partially_filling_an_earlier_slot() {
        let (interface, method, requirement) = ids();
        let mut budget = InterfaceConstraintBudget::default();
        let mut builder = EvidenceSelectionBuilder::new();
        let root = builder
            .push_abstract(requirement, &[], &mut budget)
            .expect("one abstract evidence node should fit");
        let selection = builder
            .finish(root, unary_application(interface, Type::Int))
            .expect("the abstract selection should have one valid root");
        let first = EvidenceSlot::empty();
        let second = EvidenceSlot::empty();
        let first_handle = first.handle();
        let second_handle = second.handle();
        second_handle
            .fill(
                None,
                unary_application(interface, Type::Int),
                Box::new([]),
                None,
                selection.clone(),
            )
            .expect("the second slot should begin filled for the invalid fixture");
        let mut slot_ids = HashMap::new();
        slot_ids
            .try_reserve(2)
            .expect("two preflight fixture identities should fit");
        slot_ids.insert(first_handle.storage_id(), Some(method));
        slot_ids.insert(second_handle.storage_id(), None);
        let publication = PendingEvidencePublication {
            occurrences: vec![
                SelectedOccurrence {
                    checked_method: Some(method),
                    checked_application: unary_application(interface, Type::Int),
                    method_arguments: Box::new([Type::Bool]),
                    checked_value_type: Some(Type::Unit),
                    selection: Some(selection.clone()),
                    slot: Some(first_handle),
                },
                SelectedOccurrence {
                    checked_method: None,
                    checked_application: unary_application(interface, Type::Int),
                    method_arguments: Box::new([]),
                    checked_value_type: None,
                    selection: Some(selection),
                    slot: Some(second_handle),
                },
            ],
            slot_ids,
        };

        assert_eq!(publication.publish(), Err(SelectionFailure::InvalidState));
        assert!(first.selection().is_none());
        assert!(first.method_arguments().is_empty());
        assert!(second.selection().is_some());
    }

    #[test]
    fn actual_capture_selected_routes_refuse_wrong_method_slot_and_prior_corruption() {
        let (_, method, _) = ids();
        let slot = EvidenceSlot::empty();
        let other = EvidenceSlot::empty();
        let mut publication = publication_batch(&slot);
        assert!(
            publication
                .capture_selection_if_present(
                    other.storage_id(),
                    None,
                    &mut TypeWorkBudget::unbounded()
                )
                .unwrap()
                .is_none()
        );
        assert!(
            matches!(
                publication.capture_selection_if_present(
                    slot.storage_id(),
                    Some(method),
                    &mut TypeWorkBudget::unbounded()
                ),
                Err(SelectionFailure::InvalidState)
            ),
            "wrong method is malformed, not absence permitting fallback"
        );
        let mut selector = EvidenceSelector::new();
        selector.selected.push(publication.occurrences.remove(0));
        assert!(matches!(
            selector.capture_selected(other.storage_id(), None, &mut TypeWorkBudget::unbounded()),
            Err(SelectionFailure::InvalidState)
        ));
        assert!(matches!(
            selector.capture_selected(
                slot.storage_id(),
                Some(method),
                &mut TypeWorkBudget::unbounded()
            ),
            Err(SelectionFailure::InvalidState)
        ));
        assert!(
            selector
                .capture_selected(slot.storage_id(), None, &mut TypeWorkBudget::unbounded())
                .is_ok()
        );
        assert!(
            slot.selection().is_none(),
            "reading the immutable selected plan never publishes"
        );
        let mut measured = TypeWorkBudget::unbounded();
        selector
            .capture_selected(slot.storage_id(), None, &mut measured)
            .unwrap();
        let cost = measured.used();
        assert!(cost > 0);
        assert!(matches!(
            selector.capture_selected(
                slot.storage_id(),
                None,
                &mut TypeWorkBudget::with_limit(cost - 1)
            ),
            Err(SelectionFailure::TypeResource)
        ));
        assert!(
            selector
                .capture_selected(
                    slot.storage_id(),
                    None,
                    &mut TypeWorkBudget::with_limit(cost)
                )
                .is_ok()
        );
        selector
            .selected
            .push(publication_batch(&slot).occurrences.remove(0));
        assert!(
            matches!(
                selector.capture_selected(
                    slot.storage_id(),
                    None,
                    &mut TypeWorkBudget::unbounded()
                ),
                Err(SelectionFailure::InvalidState)
            ),
            "duplicate slot grants no route"
        );
        let mut malformed = publication_batch(&slot);
        malformed.slot_ids.insert(slot.storage_id(), Some(method));
        assert!(
            matches!(
                malformed.capture_selection_if_present(
                    slot.storage_id(),
                    None,
                    &mut TypeWorkBudget::unbounded()
                ),
                Err(SelectionFailure::InvalidState)
            ),
            "wrong prior slot authority never falls back"
        );
        for missing_occurrence in [true, false] {
            let mut malformed = publication_batch(&slot);
            if missing_occurrence {
                malformed.occurrences.clear();
            } else {
                malformed.slot_ids.remove(&slot.storage_id());
            }
            let mut measured = TypeWorkBudget::unbounded();
            assert!(
                matches!(
                    malformed.capture_selection_if_present(slot.storage_id(), None, &mut measured),
                    Err(SelectionFailure::InvalidState)
                ),
                "one missing slot domain cannot permit current-selector fallback"
            );
            let cost = measured.used();
            assert!(
                cost > 0,
                "the domain lookup is charged even for an orphan index"
            );
            for prefix in [0, 9] {
                let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
                short.charge(prefix).unwrap();
                assert!(matches!(
                    malformed.capture_selection_if_present(slot.storage_id(), None, &mut short),
                    Err(SelectionFailure::TypeResource)
                ));
                let mut exact = TypeWorkBudget::with_limit(prefix + cost);
                exact.charge(prefix).unwrap();
                assert!(matches!(
                    malformed.capture_selection_if_present(slot.storage_id(), None, &mut exact),
                    Err(SelectionFailure::InvalidState)
                ));
                assert_eq!(exact.used(), prefix + cost);
            }
            assert!(
                slot.selection().is_none(),
                "refused route lookup never publishes"
            );
        }
    }

    #[test]
    fn combined_publication_keeps_all_batches_unpublished_until_commit() {
        let first = EvidenceSlot::empty();
        let second = EvidenceSlot::empty();
        let mut publication = publication_batch(&first);
        publication
            .append(
                publication_batch(&second),
                &mut InterfaceConstraintBudget::default(),
            )
            .unwrap();
        assert!(first.selection().is_none());
        assert!(second.selection().is_none());
        publication.publish().unwrap();
        assert!(first.selection().is_some());
        assert!(second.selection().is_some());
    }

    fn publication_batch(slot: &EvidenceSlot) -> PendingEvidencePublication {
        let (interface, _, requirement) = ids();
        let mut builder = EvidenceSelectionBuilder::new();
        let root = builder
            .push_abstract(requirement, &[], &mut InterfaceConstraintBudget::default())
            .unwrap();
        let selection = builder
            .finish(root, unary_application(interface, Type::Int))
            .unwrap();
        PendingEvidencePublication {
            occurrences: vec![SelectedOccurrence {
                checked_method: None,
                checked_application: unary_application(interface, Type::Int),
                method_arguments: Box::new([]),
                checked_value_type: None,
                selection: Some(selection),
                slot: Some(slot.handle()),
            }],
            slot_ids: HashMap::from([(slot.storage_id(), None)]),
        }
    }

    #[test]
    fn combined_publication_duplicate_and_budget_failure_allow_fresh_retry() {
        let first = EvidenceSlot::empty();
        let second = EvidenceSlot::empty();
        let mut publication = publication_batch(&first);
        let mut short = InterfaceConstraintBudget::with_limit(1);
        assert_eq!(
            publication.append(publication_batch(&second), &mut short),
            Err(SelectionFailure::ConstraintResource)
        );
        assert_eq!(publication.occurrences.len(), 1);
        assert!(first.selection().is_none());
        assert!(second.selection().is_none());
        assert_eq!(
            publication.append(
                publication_batch(&first),
                &mut InterfaceConstraintBudget::default()
            ),
            Err(SelectionFailure::InvalidState)
        );
        assert_eq!(publication.occurrences.len(), 1);
        let mut exact = InterfaceConstraintBudget::with_limit(2);
        publication
            .append(publication_batch(&second), &mut exact)
            .unwrap();
        assert_eq!(exact.used(), 2);
        publication.publish().unwrap();
        assert!(first.selection().is_some());
        assert!(second.selection().is_some());
    }

    #[test]
    fn combined_publication_late_invalid_slot_rolls_back_every_batch() {
        let first = EvidenceSlot::empty();
        let second = EvidenceSlot::empty();
        let mut publication = publication_batch(&first);
        publication
            .append(
                publication_batch(&second),
                &mut InterfaceConstraintBudget::default(),
            )
            .unwrap();
        publication_batch(&second).publish().unwrap();
        assert_eq!(publication.publish(), Err(SelectionFailure::InvalidState));
        assert!(first.selection().is_none());
    }

    #[test]
    fn pending_method_arguments_have_exact_atomic_publication_boundaries() {
        // Two method arguments, the authenticated checked-value carrier, and
        // two occurrence/slot records, then the exact two-unit comparison of
        // the checked and selected Int goal.
        const EXACT_CONSTRAINT_WORK: usize = 2 + 1 + 1 + 2 + 2;
        // The checked application owns one aligned zonk-vector cell, and the
        // ordered method-argument vector owns two retained Type carriers. The
        // identity zonk fixture performs no additional Type cloning.
        const EXACT_TYPE_WORK: usize = 1 + 2;

        let run = |constraint_limit, type_limit| {
            let (interface, method, requirement) = ids();
            let mut builder = EvidenceSelectionBuilder::new();
            let root = builder
                .push_abstract(requirement, &[], &mut InterfaceConstraintBudget::default())
                .expect("one abstract evidence node should fit");
            let selection = builder
                .finish(root, unary_application(interface, Type::Int))
                .expect("the pending selection should have one valid root");
            let slot = EvidenceSlot::empty();
            let mut selector = EvidenceSelector::new();
            selector.selected.push(SelectedOccurrence {
                checked_method: Some(method),
                checked_application: unary_application(interface, Type::Int),
                method_arguments: Box::new([Type::Bool, Type::Int]),
                checked_value_type: Some(Type::Bool),
                selection: Some(selection),
                slot: Some(slot.handle()),
            });
            let mut constraints = InterfaceConstraintBudget::with_limit(constraint_limit);
            let mut types = TypeWorkBudget::with_limit(type_limit);
            let result = selector.prepare_publication(
                |argument, _| Ok(argument),
                &mut constraints,
                &mut types,
            );
            (result, slot, constraints.used(), types.used())
        };

        let (constraint_short, slot, _, _) = run(EXACT_CONSTRAINT_WORK - 1, EXACT_TYPE_WORK);
        assert!(matches!(
            constraint_short,
            Err(SelectionFailure::ConstraintResource)
        ));
        assert!(slot.selection().is_none());

        let (type_short, slot, _, _) = run(EXACT_CONSTRAINT_WORK, EXACT_TYPE_WORK - 1);
        assert!(matches!(type_short, Err(SelectionFailure::TypeResource)));
        assert!(slot.selection().is_none());

        let (exact, slot, constraints, types) = run(EXACT_CONSTRAINT_WORK, EXACT_TYPE_WORK);
        exact
            .expect("the exact pending-publication budgets should stage the occurrence")
            .publish()
            .expect("a preflighted exact occurrence should publish");
        assert_eq!(constraints, EXACT_CONSTRAINT_WORK);
        assert_eq!(types, EXACT_TYPE_WORK);
        assert_eq!(slot.method_arguments(), &[Type::Bool, Type::Int]);
        assert!(matches!(
            slot.filled_method(),
            Some((_, application, [Type::Bool, Type::Int], Type::Bool, _))
                if unary_argument(application) == &Type::Int
        ));
        assert!(slot.selection().is_some());
    }

    #[test]
    fn conditional_method_rigidity_ingress_has_exact_atomic_retry_boundaries() {
        // One method identity, one method argument, one occurrence record, one
        // rigid argument, one condition record, plus the two-record traversals of the retained
        // interface Int and fresh method Bool arguments. The checked Unit
        // value type owns one carrier plus the two-cell retained type walk.
        const EXACT_CONSTRAINT_WORK: usize = 8 + 3 + 1;
        // The complete application clone owns one vector cell and its one
        // primitive argument.
        const EXACT_TYPE_WORK: usize = 1 + 1;
        let (interface, _, _) = ids();
        let source = SourceFile::new("method-rigidity-ingress.ash", "use")
            .expect("the ingress source should fit");
        let span = source
            .span(ByteRange::new(0, 3).expect("the ingress range should be ordered"))
            .expect("the ingress span should fit");
        let slot = EvidenceSlot::empty();
        let mut selector = EvidenceSelector::new();

        let mut short_constraints =
            InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1);
        assert_eq!(
            selector.push_cloned_obligation(
                &unary_application(interface, Type::Int),
                MethodObligationMetadata::new(
                    MethodId::new(interface, 0),
                    Box::new([Type::Bool]),
                    Some(MethodRigidityCondition::new(
                        Box::new([Type::Bool]),
                        MethodRigiditySite::application(span, span, span),
                    )),
                )
                .with_checked_value_type(Type::Unit),
                SelectionSite::plain(slot.handle(), span),
                &mut short_constraints,
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert!(selector.pending.is_empty());
        assert_eq!(selector.pending_method_rigidity_count, 0);
        assert!(slot.selection().is_none());

        assert_eq!(
            selector.push_cloned_obligation(
                &unary_application(interface, Type::Int),
                MethodObligationMetadata::new(
                    MethodId::new(interface, 0),
                    Box::new([Type::Bool]),
                    Some(MethodRigidityCondition::new(
                        Box::new([Type::Bool]),
                        MethodRigiditySite::application(span, span, span),
                    )),
                )
                .with_checked_value_type(Type::Unit),
                SelectionSite::plain(slot.handle(), span),
                &mut InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK - 1),
            ),
            Err(SelectionFailure::TypeResource)
        );
        assert!(selector.pending.is_empty());
        assert_eq!(selector.pending_method_rigidity_count, 0);
        assert!(slot.selection().is_none());

        let mut exact_constraints = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        let mut exact_types = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
        selector
            .push_cloned_obligation(
                &unary_application(interface, Type::Int),
                MethodObligationMetadata::new(
                    MethodId::new(interface, 0),
                    Box::new([Type::Bool]),
                    Some(MethodRigidityCondition::new(
                        Box::new([Type::Bool]),
                        MethodRigiditySite::application(span, span, span),
                    )),
                )
                .with_checked_value_type(Type::Unit),
                SelectionSite::plain(slot.handle(), span),
                &mut exact_constraints,
                &mut exact_types,
            )
            .expect("the exact conditional ingress budgets should retain one obligation");
        assert_eq!(exact_constraints.used(), EXACT_CONSTRAINT_WORK);
        assert_eq!(exact_types.used(), EXACT_TYPE_WORK);
        assert_eq!(selector.pending.len(), 1);
        assert_eq!(selector.pending_method_rigidity_count, 1);
        assert!(slot.selection().is_none());
    }

    #[test]
    fn wide_conditional_method_rigidity_ingress_is_exact_and_atomic() {
        const WIDTH: usize = 1_024;
        // Four cells per method/rigidity argument, five fixed ingress facts,
        // and the checked-value carrier plus its Unit traversal.
        const EXACT_CONSTRAINT_WORK: usize = WIDTH * 4 + 8;
        const EXACT_TYPE_WORK: usize = 1 + 1;
        let (interface, _, _) = ids();
        let source = SourceFile::new("wide-method-rigidity-ingress.ash", "use")
            .expect("the wide ingress source should fit");
        let span = source
            .span(ByteRange::new(0, 3).expect("the wide ingress range should be ordered"))
            .expect("the wide ingress span should fit");
        let slot = EvidenceSlot::empty();
        let make_arguments = || vec![Type::Bool; WIDTH].into_boxed_slice();

        let mut short = EvidenceSelector::new();
        assert_eq!(
            short.push_cloned_obligation(
                &unary_application(interface, Type::Int),
                MethodObligationMetadata::new(
                    MethodId::new(interface, 0),
                    make_arguments(),
                    Some(MethodRigidityCondition::new(
                        make_arguments(),
                        MethodRigiditySite::application(span, span, span),
                    )),
                )
                .with_checked_value_type(Type::Unit),
                SelectionSite::plain(slot.handle(), span),
                &mut InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1),
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert!(short.pending.is_empty());
        assert!(slot.selection().is_none());

        let mut exact = EvidenceSelector::new();
        let mut exact_constraints = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        exact
            .push_cloned_obligation(
                &unary_application(interface, Type::Int),
                MethodObligationMetadata::new(
                    MethodId::new(interface, 0),
                    make_arguments(),
                    Some(MethodRigidityCondition::new(
                        make_arguments(),
                        MethodRigiditySite::application(span, span, span),
                    )),
                )
                .with_checked_value_type(Type::Unit),
                SelectionSite::plain(slot.handle(), span),
                &mut exact_constraints,
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
            )
            .expect("the exact wide conditional ingress budget should fit");
        assert_eq!(exact_constraints.used(), EXACT_CONSTRAINT_WORK);
        assert_eq!(exact.pending.len(), 1);
        assert_eq!(exact.pending_method_rigidity_count, 1);
        assert!(slot.selection().is_none());
    }

    #[test]
    fn deep_method_rigidity_condition_failure_discards_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("deep-method-rigidity-condition".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let (interface, _, _) = ids();
                let source = SourceFile::new("deep-method-rigidity.ash", "use")
                    .expect("the deep condition source should fit");
                let span = source
                    .span(ByteRange::new(0, 3).expect("the deep range should be ordered"))
                    .expect("the deep span should fit");
                let slot = EvidenceSlot::empty();
                let mut selector = EvidenceSelector::new();
                assert_eq!(
                    selector.push_cloned_obligation(
                        &unary_application(interface, Type::Int),
                        MethodObligationMetadata::new(
                            MethodId::new(interface, 0),
                            Box::new([Type::Bool]),
                            Some(MethodRigidityCondition::new(
                                Box::new([deep_value_type(DEPTH)]),
                                MethodRigiditySite::application(span, span, span),
                            )),
                        ),
                        SelectionSite::plain(slot.handle(), span),
                        &mut InterfaceConstraintBudget::with_limit(0),
                        &mut TypeWorkBudget::default(),
                    ),
                    Err(SelectionFailure::ConstraintResource)
                );
                assert!(selector.pending.is_empty());
                assert!(slot.selection().is_none());
            })
            .expect("the small-stack condition thread should start")
            .join()
            .expect("a rejected deep rigidity condition must dismantle iteratively");
    }

    #[test]
    fn selected_deep_method_rigidity_condition_discards_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("selected-deep-method-rigidity-condition".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("selected-deep-method-rigidity.ash", "use")
                    .expect("the selected deep condition source should fit");
                let span = source
                    .span(ByteRange::new(0, 3).expect("the selected deep range is ordered"))
                    .expect("the selected deep span should fit");
                let mut selector = EvidenceSelector::new();
                selector.selected.push(SelectedOccurrence {
                    checked_method: Some(MethodId::new(InterfaceId::new(ModuleId::new(0), 0), 0)),
                    checked_application: unary_application(
                        InterfaceId::new(ModuleId::new(0), 0),
                        Type::Int,
                    ),
                    method_arguments: Box::new([Type::Bool]),
                    checked_value_type: Some(Type::Unit),
                    selection: None,
                    slot: None,
                });
                selector.method_rigidities.push(SelectedMethodRigidity {
                    selected_index: 0,
                    condition: MethodRigidityCondition::new(
                        Box::new([deep_value_type(DEPTH)]),
                        MethodRigiditySite::application(span, span, span),
                    ),
                });
                drop(selector);
            })
            .expect("the selected small-stack condition thread should start")
            .join()
            .expect("a selected deep rigidity condition must dismantle iteratively");
    }

    #[test]
    fn conditional_method_rigidity_is_gated_by_selected_exact_current_identity() {
        let (interface, method, _) = ids();
        let module = interface.module();
        let current = ImplId::new(module, 0);
        let prerequisite = RequirementId::new(RequirementOwner::Impl(current), 0);
        let source = SourceFile::new("conditional-rigidity-selection.ash", "use")
            .expect("the conditional selection source should fit");
        let span = source
            .span(ByteRange::new(0, 3).expect("the conditional range should be ordered"))
            .expect("the conditional span should fit");

        let mut abstract_selector = EvidenceSelector::new();
        abstract_selector.add_interface_raw(
            interface,
            TypeVariableId::new(0),
            vec![(method, Type::Unit)],
        );
        abstract_selector.add_implementation_raw(implementation(
            current,
            interface,
            Vec::new(),
            Type::Int,
            vec![(prerequisite, interface, Type::Int)],
            vec![ImplMethodId::new(current, method)],
        ));
        let abstract_registry = abstract_selector.canonical_registry_for_test();
        abstract_selector
            .enter_implementation_scope(
                current,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the identity-equal prerequisite scope should fit");
        let abstract_marker = abstract_selector.pending_marker();
        let abstract_slot = EvidenceSlot::empty();
        abstract_selector
            .push_cloned_obligation(
                &unary_application(interface, Type::Int),
                MethodObligationMetadata::new(
                    MethodId::new(interface, 0),
                    Box::new([Type::Bool]),
                    Some(MethodRigidityCondition::new(
                        Box::new([Type::Int]),
                        MethodRigiditySite::application(span, span, span),
                    )),
                )
                .with_checked_value_type(Type::Unit),
                SelectionSite::plain(abstract_slot.handle(), span),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the abstract-dispatch conditional occurrence should stage");
        abstract_selector
            .close_with_registry(
                &abstract_registry,
                abstract_marker,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("abstract evidence should retain its existing priority");
        assert_eq!(abstract_selector.method_rigidity_count(), 0);
        assert_eq!(abstract_selector.pending_method_rigidity_count, 0);
        let abstract_selection = abstract_selector.selected[0]
            .selection
            .as_ref()
            .expect("the abstract occurrence should retain private selection");
        assert!(matches!(
            abstract_selection.node(abstract_selection.root()),
            Some(EvidenceNode::Abstract {
                requirement: selected,
                ..
            }) if selected == prerequisite
        ));
        assert!(abstract_slot.selection().is_none());
        abstract_selector
            .prepare_publication(
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("abstract dispatch needs no rigidity relation")
            .publish()
            .expect("the abstract occurrence should publish atomically");
        assert_eq!(abstract_slot.method_arguments(), &[Type::Bool]);

        let mut current_selector = EvidenceSelector::new();
        current_selector.add_interface_raw(
            interface,
            TypeVariableId::new(0),
            vec![(method, Type::Unit)],
        );
        current_selector.add_implementation_raw(implementation(
            current,
            interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(current, method)],
        ));
        let current_registry = current_selector.canonical_registry_for_test();
        current_selector
            .enter_implementation_scope(
                current,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the exact-current scope should fit");
        let current_marker = current_selector.pending_marker();
        let current_slot = EvidenceSlot::empty();
        current_selector
            .push_cloned_obligation(
                &unary_application(interface, Type::Int),
                MethodObligationMetadata::new(
                    MethodId::new(interface, 0),
                    Box::new([Type::Bool]),
                    Some(MethodRigidityCondition::new(
                        Box::new([Type::Int]),
                        MethodRigiditySite::application(span, span, span),
                    )),
                )
                .with_checked_value_type(Type::Unit),
                SelectionSite::plain(current_slot.handle(), span),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the exact-current conditional occurrence should stage");
        current_selector
            .close_with_registry(
                &current_registry,
                current_marker,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the exact-current implementation should select unchanged");
        assert_eq!(current_selector.method_rigidity_count(), 1);
        let check = current_selector
            .method_rigidity(0)
            .expect("exact-current selection should expose one private rigidity check");
        assert_eq!(check.method_arguments(), &[Type::Bool]);
        assert_eq!(check.rigid_arguments(), &[Type::Int]);
        assert_eq!(
            check.site(),
            MethodRigiditySite::application(span, span, span)
        );
        assert!(current_slot.selection().is_none());
        assert!(matches!(
            current_selector.prepare_publication(
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::InvalidState)
        ));
        assert!(current_slot.selection().is_none());
    }

    #[test]
    fn pending_method_payload_zonk_failure_discards_staged_types_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("pending-method-argument-zonk-failure".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let (interface, method, requirement) = ids();
                let mut builder = EvidenceSelectionBuilder::new();
                let root = builder
                    .push_abstract(requirement, &[], &mut InterfaceConstraintBudget::default())
                    .expect("one abstract evidence node should fit");
                let selection = builder
                    .finish(root, unary_application(interface, Type::Int))
                    .expect("the pending selection should have one valid root");
                let slot = EvidenceSlot::empty();
                let mut selector = EvidenceSelector::new();
                selector.selected.push(SelectedOccurrence {
                    checked_method: Some(method),
                    checked_application: unary_application(interface, Type::Int),
                    method_arguments: Box::new([deep_value_type(DEPTH), Type::Bool]),
                    checked_value_type: Some(Type::Unit),
                    selection: Some(selection),
                    slot: Some(slot.handle()),
                });
                let mut zonk_calls = 0;
                let result = selector.prepare_publication(
                    |argument, _| {
                        zonk_calls += 1;
                        if zonk_calls == 4 {
                            discard_kinded_argument_iteratively(argument);
                            Err(SelectionFailure::TypeResource)
                        } else {
                            Ok(argument)
                        }
                    },
                    &mut InterfaceConstraintBudget::default(),
                    &mut TypeWorkBudget::default(),
                );
                assert!(matches!(result, Err(SelectionFailure::TypeResource)));
                assert_eq!(zonk_calls, 4);
                assert!(slot.selection().is_none());
            })
            .expect("the small-stack publication thread should start")
            .join()
            .expect("staged method arguments must be dismantled iteratively on zonk failure");
    }

    #[test]
    fn interface_selector_retains_kinds_at_exact_atomic_boundaries() {
        fn exercise(imported: bool) {
            // One retained parameter record, one canonical binder lookup,
            // and three Kind-pair cells.
            const EXACT_CONSTRAINT_WORK: usize = 5;
            // One retained binder record plus the three nodes in Type -> Type.
            const EXACT_TYPE_WORK: usize = 4;
            let kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
            let fact = interface_fact_with_kind(kind.clone());
            let registry = registry_for_interface_fact(&fact);

            let mut measured_selector = EvidenceSelector::new();
            let mut measured_constraints = InterfaceConstraintBudget::default();
            let mut measured_types = TypeWorkBudget::default();
            let measured = if imported {
                measured_selector.add_imported_interface_fact(
                    &registry,
                    &fact,
                    &mut measured_constraints,
                    &mut measured_types,
                )
            } else {
                measured_selector.add_interface_fact(
                    &registry,
                    &fact,
                    &mut measured_constraints,
                    &mut measured_types,
                )
            };
            measured.expect("the generous interface ingress budgets should fit");
            assert_eq!(measured_constraints.used(), EXACT_CONSTRAINT_WORK);
            assert_eq!(measured_types.used(), EXACT_TYPE_WORK);

            let mut constraint_short_selector = EvidenceSelector::new();
            let constraint_short = if imported {
                constraint_short_selector.add_imported_interface_fact(
                    &registry,
                    &fact,
                    &mut InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1),
                    &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
                )
            } else {
                constraint_short_selector.add_interface_fact(
                    &registry,
                    &fact,
                    &mut InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1),
                    &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
                )
            };
            assert_eq!(constraint_short, Err(SelectionFailure::ConstraintResource));
            assert!(constraint_short_selector.interfaces.is_empty());
            assert!(constraint_short_selector.interface_indices.is_empty());
            assert!(constraint_short_selector.method_indices.is_empty());

            let mut short_selector = EvidenceSelector::new();
            let mut short_type = TypeWorkBudget::default();
            short_type
                .charge(crate::types::TYPE_WORK_LIMIT - (EXACT_TYPE_WORK - 1))
                .expect("test setup leaves one fewer retained unit");
            let short = if imported {
                short_selector.add_imported_interface_fact(
                    &registry,
                    &fact,
                    &mut InterfaceConstraintBudget::default(),
                    &mut short_type,
                )
            } else {
                short_selector.add_interface_fact(
                    &registry,
                    &fact,
                    &mut InterfaceConstraintBudget::default(),
                    &mut short_type,
                )
            };
            assert_eq!(short, Err(SelectionFailure::TypeResource));
            assert!(short_selector.interfaces.is_empty());
            assert!(short_selector.interface_indices.is_empty());
            assert!(short_selector.method_indices.is_empty());

            let mut exact_selector = EvidenceSelector::new();
            let mut exact_constraints =
                InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
            let mut exact_type = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
            let exact = if imported {
                exact_selector.add_imported_interface_fact(
                    &registry,
                    &fact,
                    &mut exact_constraints,
                    &mut exact_type,
                )
            } else {
                exact_selector.add_interface_fact(
                    &registry,
                    &fact,
                    &mut exact_constraints,
                    &mut exact_type,
                )
            };
            assert_eq!(exact, Ok(()));
            let [parameter] = exact_selector.interfaces[0].parameters.as_ref() else {
                panic!("the unary fixture should retain one parameter");
            };
            assert_eq!(parameter.1, kind);
            assert_eq!(exact_constraints.used(), EXACT_CONSTRAINT_WORK);
            assert_eq!(exact_type.charge(1), Err(()));
        }

        exercise(false);
        exercise(true);
    }

    #[test]
    fn wide_interface_parameter_and_application_ingress_have_exact_retryable_boundaries() {
        // Complete owner arguments retain explicit scope/kind/tag records;
        // source mirrors preserve their predecessor structural comparison cost.
        const WIDTH: usize = 32_768;
        // Retained parameter ownership, canonical kind authentication, and
        // the canonical Kind mirror each own one unit per parameter.
        const INTERFACE_CONSTRAINT_WORK: usize = 3 * WIDTH;
        const INTERFACE_TYPE_WORK: usize = 2 * WIDTH;
        // One header record, two cells per resolved/checked leaf pair, the
        // complete candidate-vector records, interface authentication, scope
        // roots and visits, then one complete pre-retention type traversal.
        const APPLICATION_CONSTRAINT_WORK: usize = (7 + 1) * WIDTH + 5;
        const APPLICATION_TYPE_WORK: usize = 2 * WIDTH;

        let file = SourceFile::new("wide-relational-ingress.ash", "interface implementation")
            .expect("the wide ingress source should fit");
        let span = file
            .span(ByteRange::new(0, 9).expect("the wide ingress range should be ordered"))
            .expect("the wide ingress span should fit");
        let module = ModuleId::from(file.id());
        let interface = InterfaceId::new(module, 0);
        let implementation = ImplId::new(module, 0);
        let parameters = (0..WIDTH)
            .map(|index| ResolvedTypeVariable {
                id: TypeVariableId::resolved(
                    module,
                    u32::try_from(index).expect("the parameter identity should fit"),
                ),
                spelling: format!("P{index}"),
                kind: Kind::Type,
                origin: Origin::Source(span),
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let fact = CheckedInterfaceFact::without_methods_for_test(
            interface,
            "Wide".into(),
            parameters,
            Origin::Source(span),
            span,
        );
        let registry = registry_for_interface_fact(&fact);
        let assert_no_interface = |selector: &EvidenceSelector| {
            assert!(selector.interfaces.is_empty());
            assert!(selector.interface_indices.is_empty());
            assert!(selector.method_indices.is_empty());
        };

        let mut constraint_retry = EvidenceSelector::new();
        assert_eq!(
            constraint_retry.add_interface_fact(
                &registry,
                &fact,
                &mut InterfaceConstraintBudget::with_limit(INTERFACE_CONSTRAINT_WORK - 1),
                &mut TypeWorkBudget::with_limit(INTERFACE_TYPE_WORK),
            ),
            Err(SelectionFailure::ConstraintResource),
        );
        assert_no_interface(&constraint_retry);
        constraint_retry
            .add_interface_fact(
                &registry,
                &fact,
                &mut InterfaceConstraintBudget::with_limit(INTERFACE_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(INTERFACE_TYPE_WORK),
            )
            .expect("a fresh exact budget should retry the unpublished interface");
        assert_eq!(constraint_retry.interfaces[0].parameters.len(), WIDTH);

        let mut type_retry = EvidenceSelector::new();
        assert_eq!(
            type_retry.add_interface_fact(
                &registry,
                &fact,
                &mut InterfaceConstraintBudget::with_limit(INTERFACE_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(INTERFACE_TYPE_WORK - 1),
            ),
            Err(SelectionFailure::TypeResource),
        );
        assert_no_interface(&type_retry);
        type_retry
            .add_interface_fact(
                &registry,
                &fact,
                &mut InterfaceConstraintBudget::with_limit(INTERFACE_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(INTERFACE_TYPE_WORK),
            )
            .expect("a fresh exact type budget should retry the unpublished interface");

        let provenance =
            ResolvedTypeProvenance::new(vec![ResolvedTypeProvenanceNode::Fact(span)], 0);
        let resolved_arguments = (0..WIDTH)
            .map(|_| ResolvedOwnerArgument {
                ty: KindedArgument::TypeArg(Type::Int),
                provenance: provenance.clone(),
                origin: Origin::Source(span),
                span,
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let checked_arguments = vec![Type::Int; WIDTH].into_boxed_slice();
        let resolved = ResolvedImplementation {
            id: implementation,
            public: false,
            head: ResolvedInterfaceApplication {
                interface: ResolvedInterfaceOccurrence {
                    id: interface,
                    spelling: "Wide".into(),
                    origin: Origin::Source(span),
                },
                arguments: resolved_arguments,
                span,
            },
            head_parameters: Box::new([]),
            prerequisite_only_parameters: Box::new([]),
            prerequisites: Box::new([]),
            method_groups: Box::new([]),
            span,
        };
        let checked = CheckedImplementation::new(
            0,
            implementation,
            test_application(interface, checked_arguments),
            Box::new([]),
        );
        let selector = || {
            let mut selector = EvidenceSelector::new();
            selector.add_interface_parameters_raw(
                interface,
                fact.parameters
                    .iter()
                    .map(|parameter| parameter.id)
                    .collect(),
                Vec::new(),
            );
            selector
        };
        let assert_no_implementation = |selector: &EvidenceSelector| {
            assert!(selector.implementations.is_empty());
            assert!(selector.implementation_indices.is_empty());
            assert!(selector.implementation_candidates.is_empty());
        };

        let mut application_constraint_retry = selector();
        assert_eq!(
            application_constraint_retry.add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut InterfaceConstraintBudget::with_limit(APPLICATION_CONSTRAINT_WORK - 1),
                &mut TypeWorkBudget::with_limit(APPLICATION_TYPE_WORK),
            ),
            Err(SelectionFailure::ConstraintResource),
        );
        assert_no_implementation(&application_constraint_retry);
        application_constraint_retry
            .add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut InterfaceConstraintBudget::with_limit(APPLICATION_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(APPLICATION_TYPE_WORK),
            )
            .expect("a fresh exact budget should retry the unpublished application");
        assert_eq!(
            application_constraint_retry.implementations[0]
                .application
                .arguments()
                .len(),
            WIDTH,
        );

        let mut application_type_retry = selector();
        assert_eq!(
            application_type_retry.add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut InterfaceConstraintBudget::with_limit(APPLICATION_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(APPLICATION_TYPE_WORK - 1),
            ),
            Err(SelectionFailure::TypeResource),
        );
        assert_no_implementation(&application_type_retry);
        application_type_retry
            .add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut InterfaceConstraintBudget::with_limit(APPLICATION_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(APPLICATION_TYPE_WORK),
            )
            .expect("a fresh exact type budget should retry the unpublished application");
    }

    #[test]
    fn duplicate_incoming_interface_method_id_is_rejected_without_publication() {
        let mut fact = interface_fact_with_kind(Kind::Type);
        let method = MethodId::new(fact.id, 0);
        fact.methods = (0..2)
            .map(|_| {
                CheckedInterfaceMethodFact::with_mirrored_binder_authority_for_test(
                    method,
                    "method".into(),
                    Box::new([]),
                    Type::Unit,
                    Origin::Source(fact.span),
                    fact.span,
                    fact.span,
                )
                .with_inherited_parameters(
                    crate::resolved::OwnerId::Interface(fact.id),
                    &fact.parameters,
                    &mut TypeWorkBudget::unbounded(),
                )
                .expect("fixture inherited owner roles")
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let registry = registry_for_interface_fact(&fact);
        let mut selector = EvidenceSelector::new();

        assert_eq!(
            selector.add_interface_fact(
                &registry,
                &fact,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::InvalidState),
        );
        assert!(selector.interfaces.is_empty());
        assert!(selector.interface_indices.is_empty());
        assert!(selector.method_indices.is_empty());
    }

    #[test]
    fn interface_parameter_identity_order_rejects_noncanonical_rows_atomically() {
        let file = SourceFile::new("interface-parameter-identities.ash", "interface")
            .expect("the identity fixture source should fit");
        let span = file
            .span(ByteRange::new(0, 9).expect("the identity fixture range is ordered"))
            .expect("the identity fixture span should fit");
        let module = ModuleId::from(file.id());
        let interface = InterfaceId::new(module, 0);
        let first = TypeVariableId::resolved(module, 0);
        let second = TypeVariableId::resolved(module, 1);
        let parameter = |id| ResolvedTypeVariable {
            id,
            spelling: "A".into(),
            kind: Kind::Type,
            origin: Origin::Source(span),
        };
        let rows: [Box<[ResolvedTypeVariable]>; 4] = [
            Box::new([parameter(first), parameter(first)]),
            Box::new([parameter(second), parameter(first)]),
            Box::new([parameter(TypeVariableId::generated(0))]),
            Box::new([parameter(TypeVariableId::resolved(
                ModuleId::new(u32::MAX),
                0,
            ))]),
        ];

        for parameters in rows {
            let fact = CheckedInterfaceFact::without_methods_for_test(
                interface,
                "Invalid".into(),
                parameters,
                Origin::Source(span),
                span,
            );
            let registry = registry_for_interface_fact(&fact);
            let mut selector = EvidenceSelector::new();
            assert_eq!(
                selector.add_interface_fact(
                    &registry,
                    &fact,
                    &mut InterfaceConstraintBudget::default(),
                    &mut TypeWorkBudget::default(),
                ),
                Err(SelectionFailure::InvalidState),
            );
            assert!(selector.interfaces.is_empty());
            assert!(selector.interface_indices.is_empty());
            assert!(selector.method_indices.is_empty());
        }
    }

    #[test]
    fn local_and_imported_implementation_ingress_have_exact_atomic_boundaries() {
        // Complete owner arguments retain explicit scope/kind/tag records;
        // source mirrors preserve their predecessor structural comparison cost.
        // Both paths authenticate the complete head application and structural
        // scope. Local ingress additionally compares the resolved and checked
        // head mirror; imported ingress instead retains one authorization hop.
        const LOCAL_CONSTRAINT_WORK: usize = 12 + 1;
        const IMPORTED_CONSTRAINT_WORK: usize = 11 + 1;
        const TYPE_WORK: usize = 1 + 1;

        let source = SourceFile::new("atomic-implementation-ingress.ash", "impl")
            .expect("the ingress fixture source should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the ingress fixture range is ordered"))
            .expect("the ingress fixture span should fit");
        let module = ModuleId::new(53);
        let interface = InterfaceId::new(module, 0);
        let interface_parameter = TypeVariableId::resolved(module, 0);
        let implementation = ImplId::new(module, 0);

        let mut authority_selector = EvidenceSelector::new();
        authority_selector.add_interface_raw(interface, interface_parameter, Vec::new());
        let registry = authority_selector.canonical_registry_for_test();

        let imported = ImportedImplementationFact::for_test(
            CheckedImplementationFact {
                id: implementation,
                application: unary_application(interface, Type::Int),
                head_parameters: Box::new([]),
                prerequisites: Box::new([]),
                methods: Box::new([]),
                origin: Origin::Source(span),
                span,
            },
            ImplementationAuthorization::from_hops(vec![ImplementationRouteHop {
                from: ModuleId::new(1),
                to: module,
                import_span: span,
            }]),
            None,
        );
        let resolved = ResolvedImplementation {
            id: implementation,
            public: false,
            head: ResolvedInterfaceApplication {
                interface: ResolvedInterfaceOccurrence {
                    id: interface,
                    spelling: "I".into(),
                    origin: Origin::Source(span),
                },
                arguments: vec![ResolvedOwnerArgument {
                    ty: KindedArgument::TypeArg(Type::Int),
                    provenance: ResolvedTypeProvenance::new(
                        vec![ResolvedTypeProvenanceNode::Fact(span)],
                        0,
                    ),
                    origin: Origin::Source(span),
                    span,
                }]
                .into_boxed_slice(),
                span,
            },
            head_parameters: Box::new([]),
            prerequisite_only_parameters: Box::new([]),
            prerequisites: Box::new([]),
            method_groups: Box::new([]),
            span,
        };
        let checked = CheckedImplementation::new(
            0,
            implementation,
            unary_application(interface, Type::Int),
            Box::new([]),
        );

        let assert_empty = |selector: &EvidenceSelector| {
            assert!(selector.implementations.is_empty());
            assert!(selector.implementation_indices.is_empty());
            assert!(selector.implementation_candidates.is_empty());
        };

        let mut measured_imported = EvidenceSelector::new();
        measured_imported.add_interface_raw(interface, interface_parameter, Vec::new());
        let mut imported_constraints = InterfaceConstraintBudget::default();
        let mut imported_types = TypeWorkBudget::default();
        measured_imported
            .add_implementation_fact(
                &registry,
                &imported,
                &mut imported_constraints,
                &mut imported_types,
            )
            .expect("the measured imported implementation should publish");
        let imported_constraint_limit = imported_constraints.used();
        let imported_type_limit = imported_types.used();
        assert_eq!(imported_constraint_limit, IMPORTED_CONSTRAINT_WORK);
        assert_eq!(imported_type_limit, TYPE_WORK);

        let mut imported_constraint_short = EvidenceSelector::new();
        imported_constraint_short.add_interface_raw(interface, interface_parameter, Vec::new());
        assert_eq!(
            imported_constraint_short.add_implementation_fact(
                &registry,
                &imported,
                &mut InterfaceConstraintBudget::with_limit(imported_constraint_limit - 1),
                &mut TypeWorkBudget::with_limit(imported_type_limit),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert_empty(&imported_constraint_short);

        let mut imported_type_short = EvidenceSelector::new();
        imported_type_short.add_interface_raw(interface, interface_parameter, Vec::new());
        assert_eq!(
            imported_type_short.add_implementation_fact(
                &registry,
                &imported,
                &mut InterfaceConstraintBudget::with_limit(imported_constraint_limit),
                &mut TypeWorkBudget::with_limit(imported_type_limit - 1),
            ),
            Err(SelectionFailure::TypeResource)
        );
        assert_empty(&imported_type_short);

        let mut imported_exact = EvidenceSelector::new();
        imported_exact.add_interface_raw(interface, interface_parameter, Vec::new());
        imported_exact
            .add_implementation_fact(
                &registry,
                &imported,
                &mut InterfaceConstraintBudget::with_limit(IMPORTED_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(TYPE_WORK),
            )
            .expect("the exact imported ingress budgets should publish atomically");

        let mut measured_local = EvidenceSelector::new();
        measured_local.add_interface_raw(interface, interface_parameter, Vec::new());
        let mut local_constraints = InterfaceConstraintBudget::default();
        let mut local_types = TypeWorkBudget::default();
        measured_local
            .add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut local_constraints,
                &mut local_types,
            )
            .expect("the measured local implementation should publish");
        let local_constraint_limit = local_constraints.used();
        let local_type_limit = local_types.used();
        assert_eq!(local_constraint_limit, LOCAL_CONSTRAINT_WORK);
        assert_eq!(local_type_limit, TYPE_WORK);

        let mut local_constraint_short = EvidenceSelector::new();
        local_constraint_short.add_interface_raw(interface, interface_parameter, Vec::new());
        assert_eq!(
            local_constraint_short.add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut InterfaceConstraintBudget::with_limit(local_constraint_limit - 1),
                &mut TypeWorkBudget::with_limit(local_type_limit),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert_empty(&local_constraint_short);

        let mut local_type_short = EvidenceSelector::new();
        local_type_short.add_interface_raw(interface, interface_parameter, Vec::new());
        assert_eq!(
            local_type_short.add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut InterfaceConstraintBudget::with_limit(local_constraint_limit),
                &mut TypeWorkBudget::with_limit(local_type_limit - 1),
            ),
            Err(SelectionFailure::TypeResource)
        );
        assert_empty(&local_type_short);

        let mut local_exact = EvidenceSelector::new();
        local_exact.add_interface_raw(interface, interface_parameter, Vec::new());
        local_exact
            .add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut InterfaceConstraintBudget::with_limit(LOCAL_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(TYPE_WORK),
            )
            .expect("the exact local ingress budgets should publish atomically");
    }

    #[test]
    fn generic_implementation_parameter_ingress_has_exact_retryable_boundaries() {
        // Complete owner arguments retain explicit scope/kind/tag records;
        // source mirrors preserve their predecessor structural comparison cost.
        // Relative to a concrete unary head, the rigid parameter adds two
        // simultaneous parameter-index owners, binder authentication, scope
        // authentication, and retained-parameter ownership.
        const IMPORTED_CONSTRAINT_WORK: usize = 17 + 1;
        const LOCAL_CONSTRAINT_WORK: usize = 18 + 1;
        const TYPE_WORK: usize = 2;

        let source = SourceFile::new("generic-implementation-ingress.ash", "implementation")
            .expect("the ingress fixture source should fit");
        let span = source
            .span(ByteRange::new(0, 14).expect("the ingress fixture range is ordered"))
            .expect("the ingress fixture span should fit");
        let module = ModuleId::from(source.id());
        let interface = InterfaceId::new(module, 0);
        let interface_parameter = TypeVariableId::resolved(module, 0);
        let implementation_parameter = TypeVariableId::resolved(module, 1);
        let implementation = ImplId::new(module, 0);
        let parameter = ResolvedTypeVariable {
            id: implementation_parameter,
            spelling: "T".into(),
            kind: Kind::Type,
            origin: Origin::Source(span),
        };
        let argument = Type::Variable(implementation_parameter);
        let mut authority_selector = EvidenceSelector::new();
        authority_selector.add_interface_raw(interface, interface_parameter, Vec::new());
        let registry = authority_selector
            .canonical_registry_for_test()
            .with_additional_type_variables([parameter.clone()]);
        let imported = ImportedImplementationFact::for_test(
            CheckedImplementationFact {
                id: implementation,
                application: unary_application(interface, argument.clone()),
                head_parameters: Box::new([parameter.clone()]),
                prerequisites: Box::new([]),
                methods: Box::new([]),
                origin: Origin::Source(span),
                span,
            },
            ImplementationAuthorization::from_hops(vec![ImplementationRouteHop {
                from: ModuleId::new(1),
                to: module,
                import_span: span,
            }]),
            None,
        );
        let resolved = ResolvedImplementation {
            id: implementation,
            public: false,
            head: ResolvedInterfaceApplication {
                interface: ResolvedInterfaceOccurrence {
                    id: interface,
                    spelling: "I".into(),
                    origin: Origin::Source(span),
                },
                arguments: Box::new([ResolvedOwnerArgument {
                    ty: KindedArgument::TypeArg(argument.clone()),
                    provenance: ResolvedTypeProvenance::new(
                        vec![ResolvedTypeProvenanceNode::Fact(span)],
                        0,
                    ),
                    origin: Origin::Source(span),
                    span,
                }]),
                span,
            },
            head_parameters: Box::new([parameter]),
            prerequisite_only_parameters: Box::new([]),
            prerequisites: Box::new([]),
            method_groups: Box::new([]),
            span,
        };
        let checked = CheckedImplementation::new(
            0,
            implementation,
            unary_application(interface, argument),
            Box::new([]),
        );
        let selector = || {
            let mut selector = EvidenceSelector::new();
            selector.add_interface_raw(interface, interface_parameter, Vec::new());
            selector
        };
        let assert_empty = |selector: &EvidenceSelector| {
            assert!(selector.implementations.is_empty());
            assert!(selector.implementation_indices.is_empty());
            assert!(selector.implementation_candidates.is_empty());
        };

        let mut imported_retry = selector();
        assert_eq!(
            imported_retry.add_implementation_fact(
                &registry,
                &imported,
                &mut InterfaceConstraintBudget::with_limit(IMPORTED_CONSTRAINT_WORK - 1),
                &mut TypeWorkBudget::with_limit(TYPE_WORK),
            ),
            Err(SelectionFailure::ConstraintResource),
        );
        assert_empty(&imported_retry);
        let mut imported_exact_constraints =
            InterfaceConstraintBudget::with_limit(IMPORTED_CONSTRAINT_WORK);
        let mut imported_exact_types = TypeWorkBudget::with_limit(TYPE_WORK);
        imported_retry
            .add_implementation_fact(
                &registry,
                &imported,
                &mut imported_exact_constraints,
                &mut imported_exact_types,
            )
            .expect("an exact fresh budget should retry the unpublished imported implementation");
        assert_eq!(imported_exact_constraints.used(), IMPORTED_CONSTRAINT_WORK);
        assert_eq!(imported_exact_types.used(), TYPE_WORK);

        let mut local_retry = selector();
        assert_eq!(
            local_retry.add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut InterfaceConstraintBudget::with_limit(LOCAL_CONSTRAINT_WORK - 1),
                &mut TypeWorkBudget::with_limit(TYPE_WORK),
            ),
            Err(SelectionFailure::ConstraintResource),
        );
        assert_empty(&local_retry);
        let mut local_exact_constraints =
            InterfaceConstraintBudget::with_limit(LOCAL_CONSTRAINT_WORK);
        let mut local_exact_types = TypeWorkBudget::with_limit(TYPE_WORK);
        local_retry
            .add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut local_exact_constraints,
                &mut local_exact_types,
            )
            .expect("an exact fresh budget should retry the unpublished local implementation");
        assert_eq!(local_exact_constraints.used(), LOCAL_CONSTRAINT_WORK);
        assert_eq!(local_exact_types.used(), TYPE_WORK);
    }

    #[test]
    fn wide_local_and_imported_implementation_closures_have_exact_retryable_boundaries() {
        // Complete owner arguments retain explicit scope/kind/tag records;
        // source mirrors preserve their predecessor structural comparison cost.
        const LOCAL_WIDTH: usize = 8_192;
        const IMPORTED_WIDTH: usize = 8_192;
        const TOTAL_WIDTH: usize = LOCAL_WIDTH + IMPORTED_WIDTH;
        const EXACT_CONSTRAINT_WORK: usize = (12 + 1) * LOCAL_WIDTH + (11 + 1) * IMPORTED_WIDTH;
        const EXACT_TYPE_WORK: usize = 2 * TOTAL_WIDTH;

        let source = SourceFile::new("wide-implementation-closure.ash", "implementation")
            .expect("the wide closure source should fit");
        let span = source
            .span(ByteRange::new(0, 14).expect("the wide closure range should be ordered"))
            .expect("the wide closure span should fit");
        let module = ModuleId::from(source.id());
        let imported_module = ModuleId::new(u32::MAX - 1);
        let registry = ResolvedRegistry::new(Vec::new(), Vec::new());
        let selector = || {
            let mut selector = EvidenceSelector::new();
            for index in 0..TOTAL_WIDTH {
                let index = u32::try_from(index).expect("the interface index should fit");
                selector.add_interface_raw(
                    InterfaceId::new(module, index),
                    TypeVariableId::resolved(module, index),
                    Vec::new(),
                );
            }
            selector
        };
        let add = |selector: &mut EvidenceSelector,
                   index: usize,
                   constraints: &mut InterfaceConstraintBudget,
                   types: &mut TypeWorkBudget| {
            let index = u32::try_from(index).expect("the implementation index should fit");
            let interface = InterfaceId::new(module, index);
            let implementation = ImplId::new(module, index);
            if usize::try_from(index).expect("the index should fit") < LOCAL_WIDTH {
                let resolved_type = ResolvedOwnerArgument {
                    ty: KindedArgument::TypeArg(Type::Int),
                    provenance: ResolvedTypeProvenance::new(
                        vec![ResolvedTypeProvenanceNode::Fact(span)],
                        0,
                    ),
                    origin: Origin::Source(span),
                    span,
                };
                let resolved = ResolvedImplementation {
                    id: implementation,
                    public: false,
                    head: ResolvedInterfaceApplication {
                        interface: ResolvedInterfaceOccurrence {
                            id: interface,
                            spelling: format!("Local{index}"),
                            origin: Origin::Source(span),
                        },
                        arguments: Box::new([resolved_type]),
                        span,
                    },
                    head_parameters: Box::new([]),
                    prerequisite_only_parameters: Box::new([]),
                    prerequisites: Box::new([]),
                    method_groups: Box::new([]),
                    span,
                };
                let checked = CheckedImplementation::new(
                    0,
                    implementation,
                    unary_application(interface, Type::Int),
                    Box::new([]),
                );
                selector.add_local_implementation(
                    &registry,
                    &resolved,
                    &checked,
                    constraints,
                    types,
                )
            } else {
                let imported = ImportedImplementationFact::for_test(
                    CheckedImplementationFact {
                        id: implementation,
                        application: unary_application(interface, Type::Int),
                        head_parameters: Box::new([]),
                        prerequisites: Box::new([]),
                        methods: Box::new([]),
                        origin: Origin::Source(span),
                        span,
                    },
                    ImplementationAuthorization::from_hops(vec![ImplementationRouteHop {
                        from: module,
                        to: imported_module,
                        import_span: span,
                    }]),
                    None,
                );
                selector.add_implementation_fact(&registry, &imported, constraints, types)
            }
        };

        let mut exact_selector = selector();
        let mut exact_constraints = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        let mut exact_types = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
        for index in 0..TOTAL_WIDTH {
            add(
                &mut exact_selector,
                index,
                &mut exact_constraints,
                &mut exact_types,
            )
            .expect("the exact graph-wide implementation closure should publish");
        }
        assert_eq!(exact_selector.implementations.len(), TOTAL_WIDTH);
        assert_eq!(exact_constraints.used(), EXACT_CONSTRAINT_WORK);
        assert_eq!(exact_types.used(), EXACT_TYPE_WORK);

        let mut constraint_retry = selector();
        let mut short_constraints =
            InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1);
        let mut exact_types = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
        for index in 0..TOTAL_WIDTH - 1 {
            add(
                &mut constraint_retry,
                index,
                &mut short_constraints,
                &mut exact_types,
            )
            .expect("every affordable closure row should publish");
        }
        assert_eq!(
            add(
                &mut constraint_retry,
                TOTAL_WIDTH - 1,
                &mut short_constraints,
                &mut exact_types,
            ),
            Err(SelectionFailure::ConstraintResource),
        );
        assert_eq!(constraint_retry.implementations.len(), TOTAL_WIDTH - 1);
        add(
            &mut constraint_retry,
            TOTAL_WIDTH - 1,
            &mut InterfaceConstraintBudget::with_limit(11 + 1),
            &mut TypeWorkBudget::with_limit(2),
        )
        .expect("a fresh exact budget should retry the unpublished imported row");
        assert_eq!(constraint_retry.implementations.len(), TOTAL_WIDTH);

        let mut type_retry = selector();
        let mut exact_constraints = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        let mut short_types = TypeWorkBudget::with_limit(EXACT_TYPE_WORK - 1);
        for index in 0..TOTAL_WIDTH - 1 {
            add(
                &mut type_retry,
                index,
                &mut exact_constraints,
                &mut short_types,
            )
            .expect("every completely retained closure row should publish");
        }
        assert_eq!(
            add(
                &mut type_retry,
                TOTAL_WIDTH - 1,
                &mut exact_constraints,
                &mut short_types,
            ),
            Err(SelectionFailure::TypeResource),
        );
        assert_eq!(type_retry.implementations.len(), TOTAL_WIDTH - 1);
        add(
            &mut type_retry,
            TOTAL_WIDTH - 1,
            &mut InterfaceConstraintBudget::with_limit(11 + 1),
            &mut TypeWorkBudget::with_limit(2),
        )
        .expect("a fresh exact type budget should retry the unpublished imported row");
        assert_eq!(type_retry.implementations.len(), TOTAL_WIDTH);
    }

    #[test]
    fn relational_local_implementation_is_admitted_as_one_complete_application() {
        // Complete owner arguments retain explicit scope/kind/tag records;
        // source mirrors preserve their predecessor structural comparison cost.
        let source = SourceFile::new("relational-evidence-ingress.ash", "impl")
            .expect("the ingress fixture should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the ingress range is ordered"))
            .expect("the ingress span should fit");
        let module = ModuleId::new(54);
        let interface = InterfaceId::new(module, 0);
        let left_parameter = TypeVariableId::resolved(module, 0);
        let right_parameter = TypeVariableId::resolved(module, 1);
        let implementation = ImplId::new(module, 0);
        let mut authority = EvidenceSelector::new();
        authority.add_interface_parameters_raw(
            interface,
            vec![left_parameter, right_parameter],
            Vec::new(),
        );
        let registry = authority.canonical_registry_for_test();
        let resolved_type = |ty| ResolvedOwnerArgument {
            ty: KindedArgument::TypeArg(ty),
            provenance: ResolvedTypeProvenance::new(
                vec![ResolvedTypeProvenanceNode::Fact(span)],
                0,
            ),
            origin: Origin::Source(span),
            span,
        };
        let resolved = ResolvedImplementation {
            id: implementation,
            public: false,
            head: ResolvedInterfaceApplication {
                interface: ResolvedInterfaceOccurrence {
                    id: interface,
                    spelling: "Relation".into(),
                    origin: Origin::Source(span),
                },
                arguments: vec![resolved_type(Type::Int), resolved_type(Type::Bool)]
                    .into_boxed_slice(),
                span,
            },
            head_parameters: Box::new([]),
            prerequisite_only_parameters: Box::new([]),
            prerequisites: Box::new([]),
            method_groups: Box::new([]),
            span,
        };
        let checked = CheckedImplementation::new(
            0,
            implementation,
            test_application(interface, Box::new([Type::Int, Type::Bool])),
            Box::new([]),
        );
        const EXACT_CONSTRAINT_WORK: usize = 1 + (2 * 2) + (2 + 2) + (1 + 1 + 2 + 2) + (2 * 2) + 2;
        const EXACT_TYPE_WORK: usize = 2 + 2;
        let add_authority = |selector: &mut EvidenceSelector| {
            selector.add_interface_parameters_raw(
                interface,
                vec![left_parameter, right_parameter],
                Vec::new(),
            );
        };
        let mut short_selector = EvidenceSelector::new();
        add_authority(&mut short_selector);
        assert_eq!(
            short_selector.add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1),
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
            ),
            Err(SelectionFailure::ConstraintResource),
        );
        assert!(short_selector.implementations.is_empty());
        assert!(short_selector.implementation_indices.is_empty());
        assert!(short_selector.implementation_candidates.is_empty());

        let mut type_short_selector = EvidenceSelector::new();
        add_authority(&mut type_short_selector);
        assert_eq!(
            type_short_selector.add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK - 1),
            ),
            Err(SelectionFailure::TypeResource),
        );
        assert!(type_short_selector.implementations.is_empty());

        let mut exact_selector = EvidenceSelector::new();
        add_authority(&mut exact_selector);
        let mut exact_constraints = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        let mut exact_types = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
        exact_selector
            .add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut exact_constraints,
                &mut exact_types,
            )
            .expect("the complete two-argument application should publish atomically");
        assert_eq!(exact_constraints.used(), EXACT_CONSTRAINT_WORK);
        assert_eq!(exact_types.used(), EXACT_TYPE_WORK);
        assert_eq!(
            exact_selector.implementations[0].application.arguments(),
            &[
                KindedArgument::TypeArg(Type::Int),
                KindedArgument::TypeArg(Type::Bool)
            ],
        );
    }

    #[test]
    fn local_prerequisite_clone_discards_a_deep_first_argument_on_second_failure() {
        const DEPTH: usize = 16_384;
        const DEEP_ARGUMENT_CELLS: usize = 1 + 2 * DEPTH;
        // Two vector records precede the two retained prerequisite arguments.
        const FIRST_ARGUMENT_PREFIX: usize = 2 + DEEP_ARGUMENT_CELLS;
        const EXACT_TYPE_WORK: usize = FIRST_ARGUMENT_PREFIX + 1;

        std::thread::Builder::new()
            .name("local-prerequisite-partial-clone-owner".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("local-prerequisite-clone.ash", "Pair")
                    .expect("the prerequisite fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the fixture range is ordered"))
                    .expect("the fixture span should fit");
                let resolved_type = |ty| ResolvedOwnerArgument {
                    ty: KindedArgument::TypeArg(ty),
                    provenance: ResolvedTypeProvenance::new(
                        vec![ResolvedTypeProvenanceNode::Fact(span)],
                        0,
                    ),
                    origin: Origin::Source(span),
                    span,
                };
                let mut deep = Type::Int;
                for _ in 0..DEPTH {
                    deep = Type::Application(Box::new(deep), Box::new(Type::Unit));
                }
                let arguments = vec![resolved_type(deep), resolved_type(Type::Bool)];

                let mut one_short = TypeWorkBudget::with_limit(FIRST_ARGUMENT_PREFIX);
                assert!(matches!(
                    clone_local_prerequisite_arguments(&arguments, &mut one_short),
                    Err(SelectionFailure::TypeResource),
                ));
                assert_eq!(one_short.used(), FIRST_ARGUMENT_PREFIX);

                let mut exact = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
                let cloned = clone_local_prerequisite_arguments(&arguments, &mut exact)
                    .expect("a fresh exact prerequisite clone should retain both arguments");
                assert_eq!(cloned.0.len(), 2);
                assert_eq!(exact.used(), EXACT_TYPE_WORK);
                drop(cloned);
                for argument in arguments {
                    argument.discard_iteratively();
                }
            })
            .expect("the small-stack prerequisite worker should start")
            .join()
            .expect("partial and complete prerequisite clones must dismantle iteratively");
    }

    #[test]
    fn late_relational_local_prerequisite_has_an_exact_ingress_guard_boundary() {
        const WIDTH: usize = 32;
        // Initial relation enumeration, the unary head mirror, complete-vector
        // staging, and interface/count authentication all reach the final
        // extra prerequisite argument before rejecting it.
        const EXACT_WORK: usize = (WIDTH + 1) + 2 + (3 * WIDTH + 4) + (2 * WIDTH + 2);

        let source = SourceFile::new("late-relational-evidence-ingress.ash", "impl")
            .expect("the ingress fixture should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the ingress range is ordered"))
            .expect("the ingress span should fit");
        let module = ModuleId::new(55);
        let interface = InterfaceId::new(module, 0);
        let interface_parameter = TypeVariableId::resolved(module, 0);
        let implementation = ImplId::new(module, 0);
        let mut authority = EvidenceSelector::new();
        authority.add_interface_raw(interface, interface_parameter, Vec::new());
        let registry = authority.canonical_registry_for_test();
        let resolved_type = |ty| ResolvedOwnerArgument {
            ty: KindedArgument::TypeArg(ty),
            provenance: ResolvedTypeProvenance::new(
                vec![ResolvedTypeProvenanceNode::Fact(span)],
                0,
            ),
            origin: Origin::Source(span),
            span,
        };
        let prerequisites = (0..WIDTH)
            .map(|index| ResolvedRequirement {
                id: RequirementId::new(
                    RequirementOwner::Impl(implementation),
                    u32::try_from(index).expect("the fixture width should fit"),
                ),
                application: ResolvedInterfaceApplication {
                    interface: ResolvedInterfaceOccurrence {
                        id: interface,
                        spelling: "Relation".into(),
                        origin: Origin::Source(span),
                    },
                    arguments: if index + 1 == WIDTH {
                        vec![resolved_type(Type::Int), resolved_type(Type::Bool)].into_boxed_slice()
                    } else {
                        vec![resolved_type(Type::Int)].into_boxed_slice()
                    },
                    span,
                },
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        let resolved = ResolvedImplementation {
            id: implementation,
            public: false,
            head: ResolvedInterfaceApplication {
                interface: ResolvedInterfaceOccurrence {
                    id: interface,
                    spelling: "Relation".into(),
                    origin: Origin::Source(span),
                },
                arguments: vec![resolved_type(Type::Int)].into_boxed_slice(),
                span,
            },
            head_parameters: Box::new([]),
            prerequisite_only_parameters: Box::new([]),
            prerequisites,
            method_groups: Box::new([]),
            span,
        };
        let checked = CheckedImplementation::new(
            0,
            implementation,
            unary_application(interface, Type::Int),
            Box::new([]),
        );

        let mut short_selector = EvidenceSelector::new();
        short_selector.add_interface_raw(interface, interface_parameter, Vec::new());
        assert_eq!(
            short_selector.add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut InterfaceConstraintBudget::with_limit(EXACT_WORK - 1),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::ConstraintResource),
        );
        assert!(short_selector.implementations.is_empty());
        assert!(short_selector.implementation_indices.is_empty());
        assert!(short_selector.implementation_candidates.is_empty());

        let mut exact_selector = EvidenceSelector::new();
        exact_selector.add_interface_raw(interface, interface_parameter, Vec::new());
        let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
        assert_eq!(
            exact_selector.add_local_implementation(
                &registry,
                &resolved,
                &checked,
                &mut exact,
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::InvalidState),
        );
        assert_eq!(exact.used(), EXACT_WORK);
        assert!(exact_selector.implementations.is_empty());
        assert!(exact_selector.implementation_indices.is_empty());
        assert!(exact_selector.implementation_candidates.is_empty());
    }

    #[test]
    fn higher_kinded_implementation_ingress_has_exact_atomic_and_scope_boundaries() {
        // Complete owner arguments retain explicit scope/kind/tag records;
        // source mirrors preserve their predecessor structural comparison cost.
        // Candidate authentication is:
        //   2 parameter slots + 1 parameter scan + 1 canonical lookup
        //   + 2 relation slots + 2 interface lookups
        //   + 2 root slots + 2 * 6 application/child scope cells = 21.
        // Imported carrier retention adds 6 flat records (including one
        // method ID/span pair) and two 6-cell constraint traversals; local
        // retention adds 5 flat records and the same traversals. Retention
        // clones the two 3-node Types.
        const RELATION_VECTOR_WORK: usize = 2 * 2 + 2;
        const AUTHENTICATION_WORK: usize = 22 + 2;
        const RELATION_CONSTRAINT_WORK: usize = 6 + 6;
        const RELATION_TYPE_CELLS: usize = 3 + 3;
        const IMPORTED_CARRIER_WORK: usize = 6;
        const LOCAL_CARRIER_WORK: usize = 5;
        const LOCAL_RESOLVED_CHECKED_MIRROR_WORK: usize = 2 + 4;
        const IMPORTED_CONSTRAINT_WORK: usize = RELATION_VECTOR_WORK
            + AUTHENTICATION_WORK
            + IMPORTED_CARRIER_WORK
            + RELATION_CONSTRAINT_WORK;
        const LOCAL_CONSTRAINT_WORK: usize = RELATION_VECTOR_WORK
            + LOCAL_RESOLVED_CHECKED_MIRROR_WORK
            + AUTHENTICATION_WORK
            + LOCAL_CARRIER_WORK
            + RELATION_CONSTRAINT_WORK;
        const RETAINED_TYPE_WORK: usize = 2 + RELATION_TYPE_CELLS;
        const LATE_TYPE_SHORT_WORK: usize = RETAINED_TYPE_WORK - 1;

        let source = SourceFile::new("higher-kinded-ingress.ash", "implementation")
            .expect("the higher-kinded ingress source should fit");
        let span = source
            .span(ByteRange::new(0, 14).expect("the ingress range is ordered"))
            .expect("the ingress span should fit");
        let module = ModuleId::new(93);
        let interface = InterfaceId::new(module, 0);
        let interface_parameter = TypeVariableId::resolved(module, 0);
        let function = TypeVariableId::resolved(module, 1);
        let outside = TypeVariableId::resolved(module, 2);
        let implementation = ImplId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let implementation_method = ImplMethodId::new(implementation, method);
        let method_binder = BinderId::resolved(module, 10);
        let prerequisite = RequirementId::new(RequirementOwner::Impl(implementation), 0);
        let function_kind = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let registry = ResolvedRegistry::new(Vec::new(), Vec::new())
            .with_additional_type_variables([
                ResolvedTypeVariable {
                    id: interface_parameter,
                    spelling: "A".into(),
                    kind: Kind::Type,
                    origin: Origin::Source(span),
                },
                ResolvedTypeVariable {
                    id: function,
                    spelling: "F".into(),
                    kind: function_kind.clone(),
                    origin: Origin::Source(span),
                },
                ResolvedTypeVariable {
                    id: outside,
                    spelling: "G".into(),
                    kind: function_kind.clone(),
                    origin: Origin::Source(span),
                },
            ]);
        let parameter = |id| ResolvedTypeVariable {
            id,
            spelling: if id == function { "F" } else { "G" }.into(),
            kind: function_kind.clone(),
            origin: Origin::Source(span),
        };
        let application =
            |id, argument| Type::Application(Box::new(Type::Variable(id)), Box::new(argument));
        let resolved_type = |ty| ResolvedOwnerArgument {
            ty: KindedArgument::TypeArg(ty),
            provenance: ResolvedTypeProvenance::new(
                vec![ResolvedTypeProvenanceNode::Fact(span)],
                0,
            ),
            origin: Origin::Source(span),
            span,
        };
        let imported = |parameters: Vec<ResolvedTypeVariable>, prerequisite_argument| {
            ImportedImplementationFact::for_test(
                CheckedImplementationFact {
                    id: implementation,
                    application: unary_application(interface, application(function, Type::Int)),
                    head_parameters: parameters.into_boxed_slice(),
                    prerequisites: vec![CheckedRequirement {
                        id: prerequisite,
                        application: unary_application(interface, prerequisite_argument),
                        origin: Origin::Source(span),
                        span,
                    }]
                    .into_boxed_slice(),
                    methods: vec![CheckedImplementationMethodFact {
                        capture: crate::core::capture::CaptureValueSummary::default(),
                        id: implementation_method,
                        method,
                        binder: method_binder,
                        scheme: ConstrainedScheme {
                            type_parameters: Box::new([]),
                            requirements: Box::new([]),
                            value_type: Type::Unit,
                        },
                        head_type_parameter_count: 0,
                        origin: Origin::Source(span),
                        span,
                    }]
                    .into_boxed_slice(),
                    origin: Origin::Source(span),
                    span,
                },
                ImplementationAuthorization::from_hops(vec![ImplementationRouteHop {
                    from: ModuleId::new(1),
                    to: module,
                    import_span: span,
                }]),
                None,
            )
        };
        let resolved =
            |parameters: Vec<ResolvedTypeVariable>, prerequisite_argument| ResolvedImplementation {
                id: implementation,
                public: false,
                head: ResolvedInterfaceApplication {
                    interface: ResolvedInterfaceOccurrence {
                        id: interface,
                        spelling: "Construct".into(),
                        origin: Origin::Source(span),
                    },
                    arguments: vec![resolved_type(application(function, Type::Int))]
                        .into_boxed_slice(),
                    span,
                },
                head_parameters: parameters.into_boxed_slice(),
                prerequisite_only_parameters: Box::new([]),
                prerequisites: vec![ResolvedRequirement {
                    id: prerequisite,
                    application: ResolvedInterfaceApplication {
                        interface: ResolvedInterfaceOccurrence {
                            id: interface,
                            spelling: "Construct".into(),
                            origin: Origin::Source(span),
                        },
                        arguments: vec![resolved_type(prerequisite_argument)].into_boxed_slice(),
                        span,
                    },
                }]
                .into_boxed_slice(),
                method_groups: vec![ResolvedImplementationMethodGroup {
                    contextual_parameters: Box::new([]),
                    method: Some(method),
                    identity: Some(implementation_method),
                    binder: Binder {
                        id: method_binder,
                        spelling: "construct".into(),
                        origin: Origin::Source(span),
                    },
                    equations: Box::new([]),
                    span,
                }]
                .into_boxed_slice(),
                span,
            };
        let checked = CheckedImplementation::new(
            0,
            implementation,
            unary_application(interface, application(function, Type::Int)),
            vec![CheckedImplMethod {
                source_group: 0,
                id: implementation_method,
                method,
                binder: method_binder,
            }]
            .into_boxed_slice(),
        );
        let valid_imported =
            || imported(vec![parameter(function)], application(function, Type::Bool));
        let valid_resolved =
            || resolved(vec![parameter(function)], application(function, Type::Bool));
        let selector = || {
            let mut selector = EvidenceSelector::new();
            selector.add_interface_raw(interface, interface_parameter, Vec::new());
            selector
        };
        let assert_empty = |selector: &EvidenceSelector| {
            assert!(selector.implementations.is_empty());
            assert!(selector.implementation_indices.is_empty());
            assert!(selector.implementation_candidates.is_empty());
        };

        let mut measured_imported = selector();
        let mut imported_constraints = InterfaceConstraintBudget::default();
        let mut imported_types = TypeWorkBudget::default();
        measured_imported
            .add_implementation_fact(
                &registry,
                &valid_imported(),
                &mut imported_constraints,
                &mut imported_types,
            )
            .expect("the measured imported higher-kinded fact should publish");
        assert_eq!(imported_constraints.used(), IMPORTED_CONSTRAINT_WORK);
        assert_eq!(imported_types.used(), RETAINED_TYPE_WORK);

        let mut imported_constraint_short = selector();
        assert_eq!(
            imported_constraint_short.add_implementation_fact(
                &registry,
                &valid_imported(),
                &mut InterfaceConstraintBudget::with_limit(IMPORTED_CONSTRAINT_WORK - 1),
                &mut TypeWorkBudget::with_limit(RETAINED_TYPE_WORK),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert_empty(&imported_constraint_short);

        let mut imported_type_short = selector();
        let mut imported_late_type_work = TypeWorkBudget::with_limit(RETAINED_TYPE_WORK - 1);
        assert_eq!(
            imported_type_short.add_implementation_fact(
                &registry,
                &valid_imported(),
                &mut InterfaceConstraintBudget::with_limit(IMPORTED_CONSTRAINT_WORK),
                &mut imported_late_type_work,
            ),
            Err(SelectionFailure::TypeResource)
        );
        assert_eq!(
            imported_late_type_work.used(),
            LATE_TYPE_SHORT_WORK,
            "the prerequisite and partial head clones must remain local on late failure"
        );
        assert_empty(&imported_type_short);

        let mut imported_exact = selector();
        imported_exact
            .add_implementation_fact(
                &registry,
                &valid_imported(),
                &mut InterfaceConstraintBudget::with_limit(IMPORTED_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(RETAINED_TYPE_WORK),
            )
            .expect("the exact imported higher-kinded ingress budgets should fit");

        let mut measured_local = selector();
        let mut local_constraints = InterfaceConstraintBudget::default();
        let mut local_types = TypeWorkBudget::default();
        measured_local
            .add_local_implementation(
                &registry,
                &valid_resolved(),
                &checked,
                &mut local_constraints,
                &mut local_types,
            )
            .expect("the measured local higher-kinded fact should publish");
        assert_eq!(local_constraints.used(), LOCAL_CONSTRAINT_WORK);
        assert_eq!(local_types.used(), RETAINED_TYPE_WORK);

        let mut local_constraint_short = selector();
        assert_eq!(
            local_constraint_short.add_local_implementation(
                &registry,
                &valid_resolved(),
                &checked,
                &mut InterfaceConstraintBudget::with_limit(LOCAL_CONSTRAINT_WORK - 1),
                &mut TypeWorkBudget::with_limit(RETAINED_TYPE_WORK),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert_empty(&local_constraint_short);

        let mut local_type_short = selector();
        let mut local_late_type_work = TypeWorkBudget::with_limit(RETAINED_TYPE_WORK - 1);
        assert_eq!(
            local_type_short.add_local_implementation(
                &registry,
                &valid_resolved(),
                &checked,
                &mut InterfaceConstraintBudget::with_limit(LOCAL_CONSTRAINT_WORK),
                &mut local_late_type_work,
            ),
            Err(SelectionFailure::TypeResource)
        );
        assert_eq!(
            local_late_type_work.used(),
            LATE_TYPE_SHORT_WORK,
            "the local prerequisite and partial head clones must not publish"
        );
        assert_empty(&local_type_short);

        let mut local_exact = selector();
        local_exact
            .add_local_implementation(
                &registry,
                &valid_resolved(),
                &checked,
                &mut InterfaceConstraintBudget::with_limit(LOCAL_CONSTRAINT_WORK),
                &mut TypeWorkBudget::with_limit(RETAINED_TYPE_WORK),
            )
            .expect("the exact local higher-kinded ingress budgets should fit");

        let mut missing = selector();
        let missing_registry = ResolvedRegistry::new(Vec::new(), Vec::new())
            .with_additional_type_variables([ResolvedTypeVariable {
                id: interface_parameter,
                spelling: "A".into(),
                kind: Kind::Type,
                origin: Origin::Source(span),
            }]);
        let failure = missing
            .add_implementation_fact(
                &missing_registry,
                &valid_imported(),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .unwrap_err();
        let SelectionFailure::Kind { context, .. } = failure else {
            panic!("missing canonical binder must retain its kind cause")
        };
        assert_eq!(context.name(), "missing-canonical-binder");
        assert_eq!(context.span(), span);
        assert_empty(&missing);

        let mut duplicate = selector();
        assert_eq!(
            duplicate.add_local_implementation(
                &registry,
                &resolved(
                    vec![parameter(function), parameter(function)],
                    application(function, Type::Bool),
                ),
                &checked,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::InvalidState)
        );
        assert_empty(&duplicate);

        let mut out_of_scope = selector();
        assert_eq!(
            out_of_scope.add_implementation_fact(
                &registry,
                &imported(vec![parameter(function)], application(outside, Type::Bool)),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::InvalidState)
        );
        assert_empty(&out_of_scope);
    }

    #[test]
    fn imported_selector_kind_failure_is_stack_safe_and_atomic() {
        const DEPTH: usize = 32_768;
        const KIND_NODES: usize = 2 * DEPTH + 1;
        const EXACT_WORK: usize = 1 + KIND_NODES;

        std::thread::Builder::new()
            .name("deep-selector-kind-retention".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut kind = Kind::Type;
                for _ in 0..DEPTH {
                    kind = Kind::Arrow(Box::new(Kind::Type), Box::new(kind));
                }
                let fact = interface_fact_with_kind(kind);
                let registry = registry_for_interface_fact(&fact);
                let mut selector = EvidenceSelector::new();
                let mut type_work = TypeWorkBudget::default();
                type_work
                    .charge(crate::types::TYPE_WORK_LIMIT - (EXACT_WORK - 1))
                    .expect("test setup leaves one fewer retained unit");
                assert_eq!(
                    selector.add_imported_interface_fact(
                        &registry,
                        &fact,
                        &mut InterfaceConstraintBudget::default(),
                        &mut type_work,
                    ),
                    Err(SelectionFailure::TypeResource)
                );
                assert!(selector.interfaces.is_empty());
                assert!(selector.interface_indices.is_empty());
            })
            .expect("deep selector thread")
            .join()
            .expect("deep selector retention and teardown stay iterative");
    }

    fn implementation(
        id: ImplId,
        interface: InterfaceId,
        parameters: Vec<TypeVariableId>,
        argument: Type,
        prerequisites: Vec<(RequirementId, InterfaceId, Type)>,
        methods: Vec<ImplMethodId>,
    ) -> ImplementationEntry {
        let file = SourceFile::new("implementation-selection-fixture.ash", "x")
            .expect("implementation fixture source");
        let span = file
            .span(ByteRange::new(0, 1).expect("implementation fixture range"))
            .expect("implementation fixture span");
        let method_spans = vec![span; methods.len()];
        ImplementationEntry {
            id,
            application: unary_application(interface, argument),
            parameters: parameters.into_boxed_slice(),
            prerequisites: prerequisites
                .into_iter()
                .map(|(id, interface, argument)| RequirementEntry {
                    id,
                    application: unary_application(interface, argument),
                    span,
                })
                .collect(),
            methods: methods.into_boxed_slice(),
            span,
            method_spans,
            import_spans: Box::new([]),
        }
    }

    #[test]
    fn exact_abstract_requirement_shadows_concrete_search() {
        let (interface, method, requirement) = ids();
        let parameter = TypeVariableId::new(0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(interface, parameter, vec![(method, Type::Unit)]);
        let concrete = ImplId::new(ModuleId::new(1), 0);
        selector.add_implementation_raw(implementation(
            concrete,
            interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(concrete, method)],
        ));
        selector
            .push_abstract(
                requirement,
                interface,
                Type::Int,
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("abstract fixture");

        let mut measured_constraints = InterfaceConstraintBudget::default();
        let mut measured_types = TypeWorkBudget::default();
        let selection = selector
            .select(
                interface,
                &Type::Int,
                &mut measured_constraints,
                &mut measured_types,
            )
            .expect("exact abstract evidence");

        assert_eq!(
            selection.node(selection.root()),
            Some(EvidenceNode::Abstract {
                requirement,
                methods: &[method],
            })
        );
        assert_eq!(
            selector.select(
                interface,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(measured_constraints.used() - 1),
                &mut TypeWorkBudget::with_limit(measured_types.used()),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        selector
            .select(
                interface,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(measured_constraints.used()),
                &mut TypeWorkBudget::with_limit(measured_types.used()),
            )
            .expect("exact abstract-selection budgets");
    }

    #[test]
    fn generic_implementation_instantiates_prerequisites_in_order() {
        let module = ModuleId::new(2);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let parameter = TypeVariableId::resolved(module, 0);
        let option = NominalTypeId::new(module, 0);
        let base = ImplId::new(module, 0);
        let generic = ImplId::new(module, 1);
        let prerequisite = RequirementId::new(RequirementOwner::Impl(generic), 0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(interface, parameter, vec![(method, Type::Unit)]);
        selector.add_implementation_raw(implementation(
            base,
            interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(base, method)],
        ));
        selector.add_implementation_raw(implementation(
            generic,
            interface,
            vec![parameter],
            Type::apply_arguments(Type::Nominal(option), [Type::Variable(parameter)]),
            vec![(prerequisite, interface, Type::Variable(parameter))],
            vec![ImplMethodId::new(generic, method)],
        ));

        let goal = Type::apply_arguments(Type::Nominal(option), [Type::Int]);
        let mut measured_constraints = InterfaceConstraintBudget::default();
        let mut measured_types = TypeWorkBudget::default();
        let selection = selector
            .select(
                interface,
                &goal,
                &mut measured_constraints,
                &mut measured_types,
            )
            .expect("generic evidence");

        let EvidenceNode::Implementation {
            implementation,
            substitution,
            prerequisites,
            methods,
        } = selection
            .node(selection.root())
            .expect("root implementation")
        else {
            panic!("concrete root")
        };
        assert_eq!(implementation, generic);
        assert_eq!(substitution.len(), 1);
        assert_eq!(substitution[0].parameter(), parameter);
        assert_eq!(substitution[0].argument(), &Type::Int);
        assert_eq!(methods, &[ImplMethodId::new(generic, method)]);
        assert_eq!(prerequisites.len(), 1);
        assert!(matches!(
            selection.node(prerequisites[0]),
            Some(EvidenceNode::Implementation {
                implementation,
                substitution: [],
                prerequisites: [],
                ..
            }) if implementation == base
        ));
        let constraint_limit = measured_constraints.used();
        let type_limit = measured_types.used();
        assert!(constraint_limit > 0);
        assert!(type_limit > 0);
        assert_eq!(
            selector.select(
                interface,
                &goal,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit),
                &mut TypeWorkBudget::with_limit(type_limit - 1),
            ),
            Err(SelectionFailure::TypeResource)
        );
        assert_eq!(
            selector.select(
                interface,
                &goal,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit - 1),
                &mut TypeWorkBudget::with_limit(type_limit),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        selector
            .select(
                interface,
                &goal,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit),
                &mut TypeWorkBudget::with_limit(type_limit),
            )
            .expect("exact prerequisite-selection budgets");
    }

    #[test]
    fn full_higher_kinded_selection_has_exact_atomic_dual_limits() {
        // Complete owner arguments retain explicit scope/kind/tag records;
        // source mirrors preserve their predecessor structural comparison cost.
        // Constraint work is the additive sum of one close/initial task pair,
        // two canonical Option<T> goal environments, three head inspections
        // (ground mismatch, higher-kinded match, ground prerequisite), root
        // and prerequisite scheduling, two Finish/result nodes, and checked
        // argument publication.
        const CLOSE_AND_INITIAL_TASK_WORK: usize = 2;
        const GOAL_ENVIRONMENT_WORK: usize = 2 * (1 + 8);
        const HEAD_MATCH_WORK: usize = (18 + 2) + (32 + 2) + (18 + 2);
        // Each goal key now carries one argument-position sentinel, observed
        // by the two active-set charges and the Finish charge for both goals.
        const GOAL_CONTROL_AND_SCHEDULING_WORK: usize = 28 + 19 + (2 * 3);
        const FINISH_AND_RESULT_WORK: usize = 7 + 9;
        const CHECKED_ARGUMENT_PUBLICATION_WORK: usize = 7;
        // Two retained pending-publication carrier records plus the six-cell
        // exact comparison between checked and selected Option<Int> goals.
        const PENDING_PUBLICATION_WORK: usize = 2 + 6;
        // Full owner argument scope, kind, and goal-key records add 19 units.
        const EXACT_CONSTRAINT_WORK: usize = 19
            + CLOSE_AND_INITIAL_TASK_WORK
            + GOAL_ENVIRONMENT_WORK
            + HEAD_MATCH_WORK
            + GOAL_CONTROL_AND_SCHEDULING_WORK
            + FINISH_AND_RESULT_WORK
            + CHECKED_ARGUMENT_PUBLICATION_WORK
            + PENDING_PUBLICATION_WORK;

        // Type work retains the initial goal clone, both canonical nominal
        // environments, the authenticated F -> Option substitution, its
        // replacement index/value, the instantiated prerequisite, and the
        // final selection argument.
        const INITIAL_GOAL_CLONE_WORK: usize = 1 + 3;
        // Each one-formal XI costs four retained cells and one owner-kind scan.
        const GOAL_ENVIRONMENT_TYPE_WORK: usize = 2 * 5;
        const MATCHED_SUBSTITUTION_TYPE_WORK: usize = 1;
        const REPLACEMENT_INDEX_AND_VALUE_WORK: usize = 2;
        // Replacement retention plus the retained three-cell prerequisite result.
        const PREREQUISITE_SUBSTITUTION_WORK: usize = 1 + 3;
        const SELECTION_ARGUMENT_WORK: usize = 1 + 3;
        // Closing and publication each move one complete application through
        // an aligned zonk buffer before either result is visible.
        const APPLICATION_ZONK_VECTOR_WORK: usize = 2;
        const EXACT_TYPE_WORK: usize = 1
            + INITIAL_GOAL_CLONE_WORK
            + GOAL_ENVIRONMENT_TYPE_WORK
            + MATCHED_SUBSTITUTION_TYPE_WORK
            + REPLACEMENT_INDEX_AND_VALUE_WORK
            + PREREQUISITE_SUBSTITUTION_WORK
            + SELECTION_ARGUMENT_WORK
            + APPLICATION_ZONK_VECTOR_WORK;

        let source = SourceFile::new("higher-kinded-selection-budget.ash", "selection")
            .expect("the higher-kinded selection source should fit");
        let span = source
            .span(ByteRange::new(0, 9).expect("the selection range is ordered"))
            .expect("the selection span should fit");
        let module = ModuleId::new(94);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let interface_parameter = TypeVariableId::resolved(module, 0);
        let function = TypeVariableId::resolved(module, 1);
        let nominal_parameter = TypeVariableId::resolved(module, 2);
        let option = NominalTypeId::new(module, 0);
        let base = ImplId::new(module, 0);
        let generic = ImplId::new(module, 1);
        let prerequisite = RequirementId::new(RequirementOwner::Impl(generic), 0);
        let apply = |function, argument| Type::Application(Box::new(function), Box::new(argument));
        let option_of = |argument| apply(Type::Nominal(option), argument);
        let function_of = |argument| apply(Type::Variable(function), argument);
        let setup = || {
            let registry = ResolvedRegistry::new(
                vec![ResolvedNominalType {
                    representation_provenance: None,
                    declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                    representation: None,
                    id: option,
                    spelling: "Option".into(),
                    constructors: Box::new([]),
                    origin: Origin::Source(span),
                }],
                Vec::new(),
            )
            .with_type_parameters(vec![(
                option,
                vec![ResolvedTypeVariable {
                    id: nominal_parameter,
                    spelling: "A".into(),
                    kind: Kind::Type,
                    origin: Origin::Source(span),
                }],
            )])
            .with_additional_type_variables([
                ResolvedTypeVariable {
                    id: interface_parameter,
                    spelling: "A".into(),
                    kind: Kind::Type,
                    origin: Origin::Source(span),
                },
                ResolvedTypeVariable {
                    id: function,
                    spelling: "F".into(),
                    kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
                    origin: Origin::Source(span),
                },
            ]);
            let mut selector = EvidenceSelector::new();
            selector.add_interface_raw(interface, interface_parameter, vec![(method, Type::Unit)]);
            selector.add_implementation_raw(implementation(
                base,
                interface,
                Vec::new(),
                option_of(Type::Bool),
                Vec::new(),
                vec![ImplMethodId::new(base, method)],
            ));
            selector.add_implementation_raw(implementation(
                generic,
                interface,
                vec![function],
                function_of(Type::Int),
                vec![(prerequisite, interface, function_of(Type::Bool))],
                vec![ImplMethodId::new(generic, method)],
            ));
            (selector, registry)
        };
        let run = |constraint_limit, type_limit| {
            let (mut selector, registry) = setup();
            let marker = selector.pending_marker();
            let slot = EvidenceSlot::empty();
            selector
                .push_obligation(
                    interface,
                    option_of(Type::Int),
                    slot.handle(),
                    span,
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("the full-selection obligation should queue");
            let mut constraints = InterfaceConstraintBudget::with_limit(constraint_limit);
            let mut types = TypeWorkBudget::with_limit(type_limit);
            let result = selector.close_with_registry(
                &registry,
                marker,
                |ty, _| Ok(ty),
                &mut constraints,
                &mut types,
            );
            let result = result.and_then(|()| {
                let publication = selector
                    .prepare_publication(|ty, _| Ok(ty), &mut constraints, &mut types)
                    .map_err(|failure| SelectionError {
                        failure,
                        span: None,
                        declaration_span: None,
                        import_span: None,
                        causes: Vec::new(),
                    })?;
                publication.publish().map_err(|failure| SelectionError {
                    failure,
                    span: None,
                    declaration_span: None,
                    import_span: None,
                    causes: Vec::new(),
                })
            });
            (result, slot, constraints.used(), types.used())
        };

        let (measured, slot, measured_constraints, measured_types) = run(usize::MAX, usize::MAX);
        measured.expect("the measured higher-kinded selection should fill its slot");
        let (_, selection) = slot.filled().expect("the measured slot should be filled");
        let EvidenceNode::Implementation {
            implementation,
            substitution,
            prerequisites,
            methods,
        } = selection
            .node(selection.root())
            .expect("the measured selection should retain a root")
        else {
            panic!("the higher-kinded candidate should produce concrete evidence")
        };
        assert_eq!(implementation, generic);
        assert_eq!(substitution.len(), 1);
        assert_eq!(substitution[0].parameter(), function);
        assert_eq!(substitution[0].argument(), &Type::Nominal(option));
        assert_eq!(methods, &[ImplMethodId::new(generic, method)]);
        assert!(matches!(
            selection.node(prerequisites[0]),
            Some(EvidenceNode::Implementation {
                implementation,
                prerequisites: [],
                ..
            }) if implementation == base
        ));
        assert_eq!(measured_constraints, EXACT_CONSTRAINT_WORK);
        assert_eq!(measured_types, EXACT_TYPE_WORK);

        let (constraint_short, constraint_slot, _, _) =
            run(EXACT_CONSTRAINT_WORK - 1, EXACT_TYPE_WORK);
        assert_eq!(
            constraint_short,
            Err(SelectionError {
                failure: SelectionFailure::ConstraintResource,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })
        );
        assert!(constraint_slot.selection().is_none());

        let (type_short, type_slot, _, _) = run(EXACT_CONSTRAINT_WORK, EXACT_TYPE_WORK - 1);
        assert_eq!(
            type_short,
            Err(SelectionError {
                failure: SelectionFailure::TypeResource,
                span: None,
                declaration_span: None,
                import_span: None,
                causes: Vec::new(),
            })
        );
        assert!(type_slot.selection().is_none());

        let (exact, exact_slot, exact_constraints, exact_types) =
            run(EXACT_CONSTRAINT_WORK, EXACT_TYPE_WORK);
        exact.expect("the exact higher-kinded selection budgets should fill the slot");
        assert!(exact_slot.selection().is_some());
        assert_eq!(exact_constraints, EXACT_CONSTRAINT_WORK);
        assert_eq!(exact_types, EXACT_TYPE_WORK);
    }

    #[test]
    fn exact_current_implementation_uses_declared_abstract_prerequisites() {
        let module = ModuleId::new(3);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let parameter = TypeVariableId::resolved(module, 0);
        let option = NominalTypeId::new(module, 0);
        let current = ImplId::new(module, 0);
        let prerequisite = RequirementId::new(RequirementOwner::Impl(current), 0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(interface, parameter, vec![(method, Type::Unit)]);
        selector.add_implementation_raw(implementation(
            current,
            interface,
            vec![parameter],
            Type::apply_arguments(Type::Nominal(option), [Type::Variable(parameter)]),
            vec![(prerequisite, interface, Type::Variable(parameter))],
            vec![ImplMethodId::new(current, method)],
        ));
        selector
            .enter_implementation_scope(
                current,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("implementation evidence scope");

        let component = selector
            .select(
                interface,
                &Type::Variable(parameter),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("declared prerequisite evidence");
        assert_eq!(
            component.node(component.root()),
            Some(EvidenceNode::Abstract {
                requirement: prerequisite,
                methods: &[method],
            })
        );

        let current_argument =
            Type::apply_arguments(Type::Nominal(option), [Type::Variable(parameter)]);
        let mut measured_constraints = InterfaceConstraintBudget::default();
        let mut measured_types = TypeWorkBudget::default();
        let selection = selector
            .select(
                interface,
                &current_argument,
                &mut measured_constraints,
                &mut measured_types,
            )
            .expect("rigid self evidence");
        let EvidenceNode::Implementation { prerequisites, .. } = selection
            .node(selection.root())
            .expect("current implementation")
        else {
            panic!("implementation root")
        };
        assert_eq!(prerequisites.len(), 1);
        assert_eq!(
            selection.node(prerequisites[0]),
            Some(EvidenceNode::Abstract {
                requirement: prerequisite,
                methods: &[method],
            })
        );
        let constraint_limit = measured_constraints.used();
        let type_limit = measured_types.used();
        assert!(constraint_limit > 0);
        assert!(type_limit > 0);
        assert_eq!(
            selector.select(
                interface,
                &current_argument,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit),
                &mut TypeWorkBudget::with_limit(type_limit - 1),
            ),
            Err(SelectionFailure::TypeResource)
        );
        assert_eq!(
            selector.select(
                interface,
                &current_argument,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit - 1),
                &mut TypeWorkBudget::with_limit(type_limit),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        selector
            .select(
                interface,
                &current_argument,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit),
                &mut TypeWorkBudget::with_limit(type_limit),
            )
            .expect("exact current-implementation budgets");
    }

    #[test]
    fn undetermined_goal_is_ambiguous_before_candidate_or_active_goal_work() {
        let (interface, method, requirement) = ids();
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            interface,
            TypeVariableId::new(0),
            vec![(method, Type::Unit)],
        );
        let candidate = ImplId::new(ModuleId::new(1), 0);
        selector.add_implementation_raw(implementation(
            candidate,
            interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(candidate, method)],
        ));

        let mut causes = Vec::new();
        assert_eq!(
            selector.select_owned_for_test(
                interface,
                Type::Inference(crate::types::InferenceVariableId::new(0)),
                &mut causes,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::with_limit(1),
            ),
            Err(SelectionFailure::Reason(InterfaceReason::Ambiguous))
        );
        assert_eq!(causes.len(), 1);
        assert_eq!(causes[0].kind(), SelectionCauseKind::Interface);

        let nested_inference = Type::Function(
            Box::new(Type::Inference(crate::types::InferenceVariableId::new(1))),
            Box::new(Type::Int),
        );
        selector
            .push_abstract(
                requirement,
                interface,
                nested_inference.clone(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the abstract fixture should fit");
        let mut nested_causes = Vec::new();
        assert_eq!(
            selector.select_owned_for_test(
                interface,
                nested_inference,
                &mut nested_causes,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::Reason(InterfaceReason::Ambiguous))
        );
        assert_eq!(nested_causes.len(), 1);
        assert_eq!(nested_causes[0].kind(), SelectionCauseKind::Interface);

        for (inference, nested_application) in [
            (
                crate::types::InferenceVariableId::new(2),
                Type::Application(
                    Box::new(Type::Inference(crate::types::InferenceVariableId::new(2))),
                    Box::new(Type::Int),
                ),
            ),
            (
                crate::types::InferenceVariableId::new(3),
                Type::Application(
                    Box::new(Type::Int),
                    Box::new(Type::Inference(crate::types::InferenceVariableId::new(3))),
                ),
            ),
        ] {
            let mut application_causes = Vec::new();
            assert_eq!(
                selector.select_owned_for_test(
                    interface,
                    nested_application,
                    &mut application_causes,
                    &mut InterfaceConstraintBudget::default(),
                    &mut TypeWorkBudget::default(),
                ),
                Err(SelectionFailure::Reason(InterfaceReason::Ambiguous)),
                "nested inference {inference:?} must fail before abstract/current/candidate/active work"
            );
            assert_eq!(application_causes.len(), 1);
            assert_eq!(application_causes[0].kind(), SelectionCauseKind::Interface);
        }

        assert_eq!(
            selector.select(
                interface,
                &Type::Inference(crate::types::InferenceVariableId::new(0)),
                &mut InterfaceConstraintBudget::with_limit(0),
                &mut TypeWorkBudget::with_limit(2),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert_eq!(
            selector.select(
                interface,
                &Type::Inference(crate::types::InferenceVariableId::new(0)),
                &mut InterfaceConstraintBudget::with_limit(1),
                &mut TypeWorkBudget::with_limit(2),
            ),
            Err(SelectionFailure::Reason(InterfaceReason::Ambiguous))
        );
    }

    #[test]
    fn determination_snapshot_has_exact_independent_retryable_boundaries() {
        // Complete owner arguments retain explicit scope/kind/tag records;
        // source mirrors preserve their predecessor structural comparison cost.
        // Snapshot/output storage (3), one key-position authentication and
        // clone (2), inference-free key traversal (1), the concrete candidate
        // route and first-order key match (8), dependent transaction output
        // (2), and task publication (1) total 17 constraint units. The goal
        // key traversal is owned once by its canonical environment rather than
        // repeated for each candidate. Cloning
        // the one key, source dependent, and goal dependent costs six type
        // units including their precharged output slots. Complete owner arguments
        // add three constraint staging/inspection cells and one retained Type task.
        const CONSTRAINT_WORK: usize = 17 + 3;
        const TYPE_WORK: usize = 6 + 1;
        let module = ModuleId::new(12_001);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let implementation = ImplId::new(module, 0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_parameters_with_determination_raw(
            interface,
            vec![
                TypeVariableId::resolved(module, 0),
                TypeVariableId::resolved(module, 1),
            ],
            Some(DeterminationKey::new(Box::new([0]))),
            vec![(
                method,
                Type::Function(Box::new(Type::Int), Box::new(Type::Bool)),
            )],
        );
        let span = selector
            .interface_entry(interface)
            .expect("the determined interface should remain indexed")
            .span;
        selector.add_implementation_raw(ImplementationEntry {
            id: implementation,
            application: test_application(interface, Box::new([Type::Int, Type::Bool])),
            parameters: Box::new([]),
            prerequisites: Box::new([]),
            methods: Box::new([ImplMethodId::new(implementation, method)]),
            span,
            method_spans: vec![span],
            import_spans: Box::new([]),
        });
        let registry = selector.canonical_registry_for_test();
        let slot = EvidenceSlot::empty();
        selector
            .push_owned_obligation(
                test_application(
                    interface,
                    Box::new([
                        Type::Int,
                        Type::Inference(crate::types::InferenceVariableId::new(0)),
                    ]),
                ),
                SelectionSite::plain(slot.handle(), span),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the determined obligation should stage");

        let prepare = |constraint_work: &mut InterfaceConstraintBudget,
                       type_work: &mut TypeWorkBudget| {
            selector.prepare_determination_snapshot(
                &registry,
                PendingObligationMarker::for_test(0, 0),
                |ty, _| Ok(ty),
                constraint_work,
                type_work,
            )
        };
        let mut measured_constraint = InterfaceConstraintBudget::default();
        let mut measured_type = TypeWorkBudget::default();
        let measured = prepare(&mut measured_constraint, &mut measured_type)
            .expect("the measured snapshot should fit");
        assert_eq!(measured.eligible.as_ref(), [true]);
        assert_eq!(measured.tasks.len(), 1);
        let constraint_limit = measured_constraint.used();
        let type_limit = measured_type.used();
        assert_eq!(constraint_limit, CONSTRAINT_WORK);
        assert_eq!(type_limit, TYPE_WORK);

        let mut constraint_short = InterfaceConstraintBudget::with_limit(constraint_limit - 1);
        assert!(matches!(
            prepare(
                &mut constraint_short,
                &mut TypeWorkBudget::with_limit(type_limit)
            ),
            Err(SelectionFailure::ConstraintResource),
        ));
        assert_eq!(constraint_short.used(), constraint_limit - 1);
        let mut type_short = TypeWorkBudget::with_limit(type_limit - 1);
        assert!(matches!(
            prepare(
                &mut InterfaceConstraintBudget::with_limit(constraint_limit),
                &mut type_short,
            ),
            Err(SelectionFailure::TypeResource),
        ));
        assert_eq!(type_short.used(), type_limit - 1);
        for _ in 0..2 {
            let mut exact_constraint = InterfaceConstraintBudget::with_limit(constraint_limit);
            let mut exact_type = TypeWorkBudget::with_limit(type_limit);
            let snapshot = prepare(&mut exact_constraint, &mut exact_type)
                .expect("the exact snapshot boundary should be reusable");
            assert_eq!(snapshot.eligible.as_ref(), [true]);
            assert_eq!(snapshot.tasks.len(), 1);
            assert_eq!(exact_constraint.used(), constraint_limit);
            assert_eq!(exact_type.used(), type_limit);
        }
    }

    #[test]
    fn wide_no_edge_snapshot_keeps_the_predecessor_zero_work_fast_path() {
        const WIDTH: usize = 8_192;
        let module = ModuleId::new(12_004);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            interface,
            TypeVariableId::resolved(module, 0),
            vec![(method, Type::Unit)],
        );
        let registry = selector.canonical_registry_for_test();
        let span = selector
            .interface_entry(interface)
            .expect("the ordinary interface should remain indexed")
            .span;
        let marker = selector.pending_marker();
        for _ in 0..WIDTH {
            selector
                .push_owned_obligation(
                    unary_application(interface, Type::Int),
                    SelectionSite::plain(EvidenceSlot::empty().handle(), span),
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("the ordinary obligation suffix should stage");
        }

        let mut constraints = InterfaceConstraintBudget::with_limit(0);
        let mut types = TypeWorkBudget::with_limit(0);
        let snapshot = selector
            .prepare_determination_snapshot(
                &registry,
                marker,
                |ty, _| Ok(ty),
                &mut constraints,
                &mut types,
            )
            .expect("an all-no-edge suffix should retain the predecessor fast path");
        assert!(snapshot.eligible.is_empty());
        assert!(snapshot.tasks.is_empty());
        assert_eq!(constraints.used(), 0);
        assert_eq!(types.used(), 0);
    }

    #[test]
    fn late_determined_obligation_snapshot_has_exact_linear_retry_boundaries() {
        // Complete owner arguments retain explicit scope/kind/tag records;
        // source mirrors preserve their predecessor structural comparison cost.
        const WIDTH: usize = 1_024;
        // The fixed suffix is the same 17-unit determined row above, minus the
        // one snapshot header already accounted for by the width term.
        const CONSTRAINT_WORK: usize = 3 * WIDTH + 14 + 3;
        const TYPE_WORK: usize = 6 + 1;
        let module = ModuleId::new(12_005);
        let ordinary = InterfaceId::new(module, 0);
        let ordinary_method = MethodId::new(ordinary, 0);
        let determined = InterfaceId::new(module, 1);
        let determined_method = MethodId::new(determined, 0);
        let implementation = ImplId::new(module, 0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            ordinary,
            TypeVariableId::resolved(module, 0),
            vec![(ordinary_method, Type::Unit)],
        );
        selector.add_interface_parameters_with_determination_raw(
            determined,
            vec![
                TypeVariableId::resolved(module, 1),
                TypeVariableId::resolved(module, 2),
            ],
            Some(DeterminationKey::new(Box::new([0]))),
            vec![(determined_method, Type::Unit)],
        );
        let span = selector
            .interface_entry(determined)
            .expect("the determined interface should remain indexed")
            .span;
        selector.add_implementation_raw(ImplementationEntry {
            id: implementation,
            application: test_application(determined, Box::new([Type::Int, Type::Bool])),
            parameters: Box::new([]),
            prerequisites: Box::new([]),
            methods: Box::new([ImplMethodId::new(implementation, determined_method)]),
            span,
            method_spans: vec![span],
            import_spans: Box::new([]),
        });
        let registry = selector.canonical_registry_for_test();
        let marker = selector.pending_marker();
        for _ in 1..WIDTH {
            selector
                .push_owned_obligation(
                    unary_application(ordinary, Type::Int),
                    SelectionSite::plain(EvidenceSlot::empty().handle(), span),
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("the no-edge prefix should stage");
        }
        selector
            .push_owned_obligation(
                test_application(
                    determined,
                    Box::new([
                        Type::Int,
                        Type::Inference(crate::types::InferenceVariableId::new(0)),
                    ]),
                ),
                SelectionSite::plain(EvidenceSlot::empty().handle(), span),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the late determined obligation should stage");
        let prepare = |constraint_work: &mut InterfaceConstraintBudget,
                       type_work: &mut TypeWorkBudget| {
            selector.prepare_determination_snapshot(
                &registry,
                marker,
                |ty, _| Ok(ty),
                constraint_work,
                type_work,
            )
        };

        let mut one_short = InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 1);
        assert!(matches!(
            prepare(&mut one_short, &mut TypeWorkBudget::with_limit(TYPE_WORK)),
            Err(SelectionFailure::ConstraintResource),
        ));
        assert_eq!(one_short.used(), CONSTRAINT_WORK - 1);
        for _ in 0..2 {
            let mut exact_constraints = InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
            let mut exact_types = TypeWorkBudget::with_limit(TYPE_WORK);
            let snapshot = prepare(&mut exact_constraints, &mut exact_types)
                .expect("the exact late-determined snapshot should remain retryable");
            assert_eq!(snapshot.eligible.len(), WIDTH);
            assert!(snapshot.eligible.iter().all(|eligible| *eligible));
            assert_eq!(snapshot.tasks.len(), 1);
            assert_eq!(exact_constraints.used(), CONSTRAINT_WORK);
            assert_eq!(exact_types.used(), TYPE_WORK);
        }
    }

    #[test]
    fn determined_pending_counter_is_atomic_across_push_failures() {
        let module = ModuleId::new(12_006);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_parameters_with_determination_raw(
            interface,
            vec![
                TypeVariableId::resolved(module, 0),
                TypeVariableId::resolved(module, 1),
            ],
            Some(DeterminationKey::new(Box::new([0]))),
            vec![(method, Type::Unit)],
        );
        let span = selector
            .interface_entry(interface)
            .expect("the determined interface should remain indexed")
            .span;
        let marker = selector.pending_marker();

        assert_eq!(
            selector.push_owned_obligation(
                test_application(interface, Box::new([Type::Int, Type::Bool])),
                SelectionSite::plain(EvidenceSlot::empty().handle(), span),
                &mut InterfaceConstraintBudget::with_limit(0),
            ),
            Err(SelectionFailure::ConstraintResource),
        );
        assert!(selector.pending.is_empty());
        assert_eq!(selector.pending_determined_count, marker.determined_count);

        assert_eq!(
            selector.push_cloned_obligation(
                &test_application(interface, Box::new([Type::Int, Type::Bool])),
                MethodObligationMetadata::new(method, Box::new([]), None),
                SelectionSite::plain(EvidenceSlot::empty().handle(), span),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::with_limit(0),
            ),
            Err(SelectionFailure::TypeResource),
        );
        assert!(selector.pending.is_empty());
        assert_eq!(selector.pending_determined_count, marker.determined_count);

        selector
            .push_owned_obligation(
                test_application(interface, Box::new([Type::Int, Type::Bool])),
                SelectionSite::plain(EvidenceSlot::empty().handle(), span),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("a successful determined push should publish one counted record");
        assert_eq!(selector.pending.len(), marker.pending_len + 1);
        assert_eq!(
            selector.pending_determined_count,
            marker.determined_count + 1
        );
    }

    #[test]
    fn successful_normal_close_restores_the_captured_determined_count() {
        let module = ModuleId::new(12_007);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let implementation = ImplId::new(module, 0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_parameters_with_determination_raw(
            interface,
            vec![
                TypeVariableId::resolved(module, 0),
                TypeVariableId::resolved(module, 1),
            ],
            Some(DeterminationKey::new(Box::new([0]))),
            vec![(method, Type::Unit)],
        );
        let span = selector
            .interface_entry(interface)
            .expect("the determined interface should remain indexed")
            .span;
        selector.add_implementation_raw(ImplementationEntry {
            id: implementation,
            application: test_application(interface, Box::new([Type::Int, Type::Bool])),
            parameters: Box::new([]),
            prerequisites: Box::new([]),
            methods: Box::new([ImplMethodId::new(implementation, method)]),
            span,
            method_spans: vec![span],
            import_spans: Box::new([]),
        });
        let marker = selector.pending_marker();
        let slot = EvidenceSlot::empty();
        selector
            .push_owned_obligation(
                test_application(interface, Box::new([Type::Int, Type::Bool])),
                SelectionSite::plain(slot.handle(), span),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the determined close fixture should stage");
        assert_eq!(
            selector.pending_determined_count,
            marker.determined_count + 1
        );

        selector
            .close(
                marker,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the determined obligation should select and publish");
        assert_eq!(selector.pending.len(), marker.pending_len);
        assert_eq!(selector.pending_determined_count, marker.determined_count);
        assert!(slot.selection().is_some());
    }

    #[test]
    fn partial_normal_close_keeps_the_remaining_determined_count_exact() {
        let module = ModuleId::new(12_008);
        let determined = InterfaceId::new(module, 0);
        let determined_method = MethodId::new(determined, 0);
        let ordinary = InterfaceId::new(module, 1);
        let ordinary_method = MethodId::new(ordinary, 0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_parameters_with_determination_raw(
            determined,
            vec![
                TypeVariableId::resolved(module, 0),
                TypeVariableId::resolved(module, 1),
            ],
            Some(DeterminationKey::new(Box::new([0]))),
            vec![(determined_method, Type::Unit)],
        );
        selector.add_interface_raw(
            ordinary,
            TypeVariableId::resolved(module, 2),
            vec![(ordinary_method, Type::Unit)],
        );
        let registry = selector.canonical_registry_for_test();
        let span = selector
            .interface_entry(determined)
            .expect("the determined interface should remain indexed")
            .span;
        let marker = selector.pending_marker();
        selector
            .push_owned_obligation(
                test_application(determined, Box::new([Type::Int, Type::Bool])),
                SelectionSite::plain(EvidenceSlot::empty().handle(), span),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the determined obligation should stage first");
        selector
            .push_owned_obligation(
                unary_application(ordinary, Type::Int),
                SelectionSite::plain(EvidenceSlot::empty().handle(), span),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the ordinary obligation should remain after the first failure");

        let failure = selector
            .close_with_registry(
                &registry,
                marker,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect_err("the first source-order obligation has no selection source");
        assert_eq!(
            failure.failure(),
            SelectionFailure::Reason(InterfaceReason::Unsatisfied)
        );
        assert_eq!(selector.pending.len(), marker.pending_len + 1);
        assert_eq!(selector.pending_determined_count, marker.determined_count);
        assert_eq!(
            selector.pending[marker.pending_len].application.interface(),
            ordinary
        );
    }

    #[test]
    fn determined_failed_body_removal_preserves_failure_and_retry_counts() {
        let module = ModuleId::new(12_009);
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let current = ImplId::new(module, 0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_parameters_with_determination_raw(
            interface,
            vec![
                TypeVariableId::resolved(module, 0),
                TypeVariableId::resolved(module, 1),
            ],
            Some(DeterminationKey::new(Box::new([0]))),
            vec![(method, Type::Unit)],
        );
        let span = selector
            .interface_entry(interface)
            .expect("the determined interface should remain indexed")
            .span;
        selector.add_implementation_raw(ImplementationEntry {
            id: current,
            application: test_application(interface, Box::new([Type::Int, Type::Bool])),
            parameters: Box::new([]),
            prerequisites: Box::new([]),
            methods: Box::new([ImplMethodId::new(current, method)]),
            span,
            method_spans: vec![span],
            import_spans: Box::new([]),
        });
        let registry = selector.canonical_registry_for_test();
        selector
            .enter_implementation_scope(
                current,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the exact-current scope should fit");
        let marker = selector.pending_marker();
        selector
            .push_cloned_obligation(
                &test_application(interface, Box::new([Type::Int, Type::Bool])),
                MethodObligationMetadata::new(
                    method,
                    Box::new([Type::Bool]),
                    Some(MethodRigidityCondition::new(
                        Box::new([Type::Int]),
                        MethodRigiditySite::application(span, span, span),
                    )),
                ),
                SelectionSite::plain(EvidenceSlot::empty().handle(), span),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the determined failed-body obligation should stage");
        let target = MethodRigidityTarget::new(marker, span);
        let mut snapshot = selector
            .prepare_method_rigidity_determination(
                &registry,
                target,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the matching failed-body snapshot should prepare");
        assert!(snapshot.take_task().is_some());

        let failure = selector
            .close_method_rigidity_with_snapshot_and_registry(
                &registry,
                target,
                &snapshot,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::with_limit(0),
                &mut TypeWorkBudget::default(),
            )
            .expect_err("one missing close unit should preserve the pending obligation");
        assert_eq!(failure.failure(), SelectionFailure::ConstraintResource);
        assert_eq!(selector.pending.len(), marker.pending_len + 1);
        assert_eq!(
            selector.pending_determined_count,
            marker.determined_count + 1
        );
        assert_eq!(selector.pending_method_rigidity_count, 1);

        assert!(
            selector
                .close_method_rigidity_with_snapshot_and_registry(
                    &registry,
                    target,
                    &snapshot,
                    |ty, _| Ok(ty),
                    &mut InterfaceConstraintBudget::default(),
                    &mut TypeWorkBudget::default(),
                )
                .expect("the fresh retry should remove only the matching obligation")
        );
        assert_eq!(selector.pending.len(), marker.pending_len);
        assert_eq!(selector.pending_determined_count, marker.determined_count);
        assert_eq!(selector.pending_method_rigidity_count, 0);
        assert_eq!(selector.method_rigidity_count(), 1);
    }

    #[test]
    fn packed_builtin_evidence_goals_keep_distinct_keys() {
        let interface = InterfaceId::new(ModuleId::new(10), 0);
        let mut keys = Vec::new();
        for ty in [Type::Bytes, Type::String, Type::Int, Type::Bool, Type::Unit] {
            keys.push(
                goal_key(
                    &test_application(interface, Box::new([ty])),
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("builtin evidence goal"),
            );
        }
        for (index, key) in keys.iter().enumerate() {
            for other in &keys[index + 1..] {
                assert_ne!(key, other);
            }
        }
    }

    #[test]
    fn goal_key_and_exact_type_matching_have_exact_deep_constraint_boundaries() {
        let interface = InterfaceId::new(ModuleId::new(10), 0);
        let ordered_application = test_application(interface, Box::new([Type::Int, Type::Bool]));
        let reordered_application = test_application(interface, Box::new([Type::Bool, Type::Int]));
        let ordered_key = goal_key(
            &ordered_application,
            &mut InterfaceConstraintBudget::default(),
        )
        .expect("ordered relational goal key");
        let reordered_key = goal_key(
            &reordered_application,
            &mut InterfaceConstraintBudget::default(),
        )
        .expect("reordered relational goal key");
        assert_eq!(
            ordered_key.cells.as_ref(),
            [
                GoalCell::Argument(0),
                GoalCell::TypeArgument,
                GoalCell::Int,
                GoalCell::Argument(1),
                GoalCell::TypeArgument,
                GoalCell::Bool,
            ]
        );
        assert_ne!(ordered_key, reordered_key);

        let left_associated = test_application(
            interface,
            Box::new([
                Type::Function(
                    Box::new(Type::Function(Box::new(Type::Int), Box::new(Type::Bool))),
                    Box::new(Type::Unit),
                ),
                Type::Bool,
            ]),
        );
        let right_associated = test_application(
            interface,
            Box::new([
                Type::Function(
                    Box::new(Type::Int),
                    Box::new(Type::Function(Box::new(Type::Bool), Box::new(Type::Unit))),
                ),
                Type::Bool,
            ]),
        );
        assert_ne!(
            goal_key(&left_associated, &mut InterfaceConstraintBudget::default(),)
                .expect("left-associated deep goal key"),
            goal_key(&right_associated, &mut InterfaceConstraintBudget::default(),)
                .expect("right-associated deep goal key"),
        );

        let cross_argument_boundary_left = test_application(
            interface,
            Box::new([
                Type::Function(
                    Box::new(Type::Tuple(vec![Type::Int, Type::Bool].into_boxed_slice())),
                    Box::new(Type::Unit),
                ),
                Type::Bool,
            ]),
        );
        let cross_argument_boundary_right = test_application(
            interface,
            Box::new([
                Type::Function(
                    Box::new(Type::Tuple(vec![Type::Int, Type::Bool].into_boxed_slice())),
                    Box::new(Type::Bool),
                ),
                Type::Unit,
            ]),
        );
        assert_ne!(
            goal_key(
                &cross_argument_boundary_left,
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("left cross-argument-boundary goal key"),
            goal_key(
                &cross_argument_boundary_right,
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("right cross-argument-boundary goal key"),
        );

        let argument = Type::Function(
            Box::new(Type::Tuple(vec![Type::Int, Type::Bool].into_boxed_slice())),
            Box::new(Type::Unit),
        );
        let application = unary_application(interface, argument.clone());

        let mut key_budget = InterfaceConstraintBudget::default();
        let key = goal_key(&application, &mut key_budget).expect("measured goal key");
        let key_limit = key_budget.used();
        assert_eq!(key.cells.len(), 7);
        assert_eq!(
            goal_key(
                &application,
                &mut InterfaceConstraintBudget::with_limit(key_limit - 1),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        goal_key(
            &application,
            &mut InterfaceConstraintBudget::with_limit(key_limit),
        )
        .expect("exact goal-key budget");
        assert_eq!(
            charge_goal_key(
                &key,
                &mut InterfaceConstraintBudget::with_limit(key.cells.len()),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        let mut exact_active =
            InterfaceConstraintBudget::with_limit(key.cells.len().saturating_add(1));
        charge_goal_key(&key, &mut exact_active).expect("exact active-goal operation budget");
        assert_eq!(exact_active.used(), key.cells.len().saturating_add(1));

        let mut equality_budget = InterfaceConstraintBudget::default();
        assert_eq!(
            same_type_with_constraint_budget(&argument, &argument, &mut equality_budget),
            Ok(true)
        );
        let equality_limit = equality_budget.used();
        assert_eq!(
            same_type_with_constraint_budget(
                &argument,
                &argument,
                &mut InterfaceConstraintBudget::with_limit(equality_limit - 1),
            ),
            Err(())
        );
        assert_eq!(
            same_type_with_constraint_budget(
                &argument,
                &argument,
                &mut InterfaceConstraintBudget::with_limit(equality_limit),
            ),
            Ok(true)
        );
        assert_eq!(
            charge_candidate_inspection(&mut InterfaceConstraintBudget::with_limit(0)),
            Err(SelectionFailure::ConstraintResource)
        );
        charge_candidate_inspection(&mut InterfaceConstraintBudget::with_limit(1))
            .expect("one candidate-inspection unit");
        assert_eq!(
            charge_prerequisite_goal(
                &unary_application(interface, Type::Int),
                &mut InterfaceConstraintBudget::with_limit(2),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        let mut exact_prerequisite = InterfaceConstraintBudget::with_limit(3);
        charge_prerequisite_goal(
            &unary_application(interface, Type::Int),
            &mut exact_prerequisite,
        )
        .expect("one edge plus the retained prerequisite argument");
        assert_eq!(exact_prerequisite.used(), 3);
    }

    #[test]
    fn selection_goal_keys_preserve_closed_and_rigid_open_effect_rows() {
        let interface = InterfaceId::new(ModuleId::new(10), 0);
        let effect = crate::types::EffectId::new(ModuleId::new(11), 0);
        let noncanonical_pure = Type::EffectfulFunction(
            Box::new(Type::Unit),
            Box::new(crate::types::ComputationType::new(
                Type::Bool,
                crate::types::EffectRow::empty(),
            )),
        );
        let noncanonical_key = goal_key(
            &unary_application(interface, noncanonical_pure),
            &mut InterfaceConstraintBudget::default(),
        )
        .expect("an empty effectful representation has the pure function key");
        let pure_key = goal_key(
            &unary_application(
                interface,
                Type::Function(Box::new(Type::Unit), Box::new(Type::Bool)),
            ),
            &mut InterfaceConstraintBudget::default(),
        )
        .expect("the canonical pure function has a selection key");
        assert_eq!(noncanonical_key, pure_key);

        let closed = Type::function_computation(
            Type::Unit,
            crate::types::ComputationType::new(
                Type::Bool,
                crate::types::EffectRow::singleton(crate::types::EffectInstance::new(
                    effect,
                    Box::new([Type::Int]),
                )),
            ),
        );
        let distinct = Type::function_computation(
            Type::Unit,
            crate::types::ComputationType::new(
                Type::Bool,
                crate::types::EffectRow::singleton(crate::types::EffectInstance::new(
                    effect,
                    Box::new([Type::Bool]),
                )),
            ),
        );
        let closed_key = goal_key(
            &unary_application(interface, closed),
            &mut InterfaceConstraintBudget::default(),
        )
        .expect("a closed effectful function is a valid selection argument");
        let distinct_key = goal_key(
            &unary_application(interface, distinct),
            &mut InterfaceConstraintBudget::default(),
        )
        .expect("a distinct closed effectful function is also valid");
        assert_ne!(closed_key, distinct_key);

        let open = Type::function_computation(
            Type::Unit,
            crate::types::ComputationType::new(
                Type::Bool,
                crate::types::EffectRow::open(
                    EffectRowVariable::rigid(TypeVariableId::new(0)),
                    Box::new([]),
                ),
            ),
        );
        let open_key = goal_key(
            &unary_application(interface, open),
            &mut InterfaceConstraintBudget::default(),
        )
        .expect("a rigid open row has a complete memo key");
        assert_ne!(open_key, closed_key);
    }

    #[test]
    fn absent_candidate_is_unsatisfied() {
        let (interface, method, _) = ids();
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            interface,
            TypeVariableId::new(0),
            vec![(method, Type::Unit)],
        );
        let mut measured = InterfaceConstraintBudget::default();
        assert_eq!(
            selector.select(
                interface,
                &Type::Int,
                &mut measured,
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::Reason(InterfaceReason::Unsatisfied))
        );
        assert_eq!(
            selector.select(
                interface,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(measured.used() - 1),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert_eq!(
            selector.select(
                interface,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(measured.used()),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::Reason(InterfaceReason::Unsatisfied))
        );
    }

    #[test]
    fn every_same_interface_candidate_inspection_is_constraint_bounded() {
        // Complete owner arguments retain explicit scope/kind/tag records;
        // local source mirrors additionally compare the argument tags.
        const REJECTED: u32 = 128;
        // The rigid goal environment is discovered once per selection task.
        // Each rejected ground candidate owns one ordered inspection, two
        // aligned application-root cells, and six first-order structural
        // preflight/mismatch cells.
        const REJECTED_CANDIDATE_WORK: usize = 1 + 2 + 6 + 1;
        let (interface, method, _) = ids();
        let matching = ImplId::new(ModuleId::new(1), 1);
        let mut baseline = EvidenceSelector::new();
        baseline.add_interface_raw(
            interface,
            TypeVariableId::new(0),
            vec![(method, Type::Unit)],
        );
        baseline.add_implementation_raw(implementation(
            matching,
            interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(matching, method)],
        ));
        let mut baseline_work = InterfaceConstraintBudget::default();
        baseline
            .select(
                interface,
                &Type::Int,
                &mut baseline_work,
                &mut TypeWorkBudget::default(),
            )
            .expect("first candidate");

        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            interface,
            TypeVariableId::new(0),
            vec![(method, Type::Unit)],
        );
        for declaration in 0..REJECTED {
            let candidate = ImplId::new(ModuleId::new(1), declaration);
            selector.add_implementation_raw(implementation(
                candidate,
                interface,
                Vec::new(),
                Type::Bool,
                Vec::new(),
                vec![ImplMethodId::new(candidate, method)],
            ));
        }
        let candidate = ImplId::new(ModuleId::new(1), REJECTED);
        selector.add_implementation_raw(implementation(
            candidate,
            interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(candidate, method)],
        ));
        let mut measured = InterfaceConstraintBudget::default();
        selector
            .select(
                interface,
                &Type::Int,
                &mut measured,
                &mut TypeWorkBudget::default(),
            )
            .expect("second candidate");
        assert_eq!(
            measured.used(),
            baseline_work.used()
                + usize::try_from(REJECTED).expect("fixture width") * REJECTED_CANDIDATE_WORK,
            "each rejected ground candidate owns only inspection and structural comparison",
        );
        assert_eq!(
            selector.select(
                interface,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(measured.used() - 1),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
    }

    #[test]
    fn ground_prerequisite_reentry_is_a_cycle_before_resource_exhaustion() {
        let module = ModuleId::new(4);
        let left = InterfaceId::new(module, 0);
        let right = InterfaceId::new(module, 1);
        let left_method = MethodId::new(left, 0);
        let right_method = MethodId::new(right, 0);
        let left_impl = ImplId::new(module, 0);
        let right_impl = ImplId::new(module, 1);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            left,
            TypeVariableId::new(0),
            vec![(left_method, Type::Unit)],
        );
        selector.add_interface_raw(
            right,
            TypeVariableId::new(1),
            vec![(right_method, Type::Unit)],
        );
        selector.add_implementation_raw(implementation(
            left_impl,
            left,
            Vec::new(),
            Type::Int,
            vec![(
                RequirementId::new(RequirementOwner::Impl(left_impl), 0),
                right,
                Type::Int,
            )],
            vec![ImplMethodId::new(left_impl, left_method)],
        ));
        selector.add_implementation_raw(implementation(
            right_impl,
            right,
            Vec::new(),
            Type::Int,
            vec![(
                RequirementId::new(RequirementOwner::Impl(right_impl), 0),
                left,
                Type::Int,
            )],
            vec![ImplMethodId::new(right_impl, right_method)],
        ));
        let mut measured = InterfaceConstraintBudget::default();
        assert_eq!(
            selector.select(
                left,
                &Type::Int,
                &mut measured,
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::Reason(InterfaceReason::Cycle))
        );
        let before_reentry = measured.used();
        assert_eq!(
            selector.select(
                left,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(before_reentry),
                &mut TypeWorkBudget::default(),
            ),
            Err(SelectionFailure::Reason(InterfaceReason::Cycle))
        );
    }

    #[test]
    fn failing_sibling_prerequisites_retain_only_the_first_declaration_order_path() {
        let module = ModuleId::new(14);
        let root = InterfaceId::new(module, 0);
        let first = InterfaceId::new(module, 1);
        let second = InterfaceId::new(module, 2);
        let root_method = MethodId::new(root, 0);
        let root_impl = ImplId::new(module, 0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            root,
            TypeVariableId::new(0),
            vec![(root_method, Type::Unit)],
        );
        selector.add_interface_raw(first, TypeVariableId::new(1), Vec::new());
        selector.add_interface_raw(second, TypeVariableId::new(2), Vec::new());
        selector.add_implementation_raw(implementation(
            root_impl,
            root,
            Vec::new(),
            Type::Int,
            vec![
                (
                    RequirementId::new(RequirementOwner::Impl(root_impl), 0),
                    first,
                    Type::Int,
                ),
                (
                    RequirementId::new(RequirementOwner::Impl(root_impl), 1),
                    second,
                    Type::Int,
                ),
            ],
            vec![ImplMethodId::new(root_impl, root_method)],
        ));
        let root_span = selector.interface_entry(root).expect("root interface").span;
        let first_span = selector
            .interface_entry(first)
            .expect("first prerequisite interface")
            .span;
        let second_span = selector
            .interface_entry(second)
            .expect("second prerequisite interface")
            .span;
        let mut causes = Vec::new();

        let failure = selector.select_owned_for_test(
            root,
            Type::Int,
            &mut causes,
            &mut InterfaceConstraintBudget::default(),
            &mut TypeWorkBudget::default(),
        );

        assert_eq!(
            failure,
            Err(SelectionFailure::Reason(InterfaceReason::Unsatisfied))
        );
        let interface_spans = causes
            .iter()
            .filter(|cause| cause.kind() == SelectionCauseKind::Interface)
            .map(|cause| cause.span())
            .collect::<Vec<_>>();
        assert_eq!(interface_spans, vec![root_span, first_span]);
        assert!(!interface_spans.contains(&second_span));
    }

    #[test]
    fn concrete_selection_has_exact_constraint_and_type_work_boundaries() {
        let (interface, method, _) = ids();
        let implementation_id = ImplId::new(ModuleId::new(1), 0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            interface,
            TypeVariableId::new(0),
            vec![(method, Type::Unit)],
        );
        selector.add_implementation_raw(implementation(
            implementation_id,
            interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(implementation_id, method)],
        ));
        let mut constraints = InterfaceConstraintBudget::default();
        let mut types = TypeWorkBudget::default();
        selector
            .select(interface, &Type::Int, &mut constraints, &mut types)
            .expect("measured selection");
        let constraint_limit = constraints.used();
        let type_limit = types.used();
        assert_eq!(
            selector.select(
                interface,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit - 1),
                &mut TypeWorkBudget::with_limit(type_limit),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        assert_eq!(
            selector.select(
                interface,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit),
                &mut TypeWorkBudget::with_limit(type_limit - 1),
            ),
            Err(SelectionFailure::TypeResource)
        );
        selector
            .select(
                interface,
                &Type::Int,
                &mut InterfaceConstraintBudget::with_limit(constraint_limit),
                &mut TypeWorkBudget::with_limit(type_limit),
            )
            .expect("exact budgets");
    }

    #[test]
    fn transitive_import_causes_have_proportional_exact_boundaries() {
        let source = SourceFile::new("transitive-selection.ash", "abcdefghijklmnop")
            .expect("the transitive selection source should fit");
        let span = |start, end| {
            source
                .span(ByteRange::new(start, end).expect("the span should be ordered"))
                .expect("the span should belong to the fixture")
        };
        let first_hop = span(0, 2);
        let second_hop = span(3, 5);
        let definition = span(6, 8);
        let interface = InterfaceId::new(ModuleId::new(11), 0);
        let implementation_id = ImplId::new(ModuleId::new(11), 0);
        let imported = |hops| {
            ImportedImplementationFact::for_test(
                CheckedImplementationFact {
                    id: implementation_id,
                    application: unary_application(interface, Type::Int),
                    head_parameters: Box::new([]),
                    prerequisites: Box::new([]),
                    methods: Box::new([]),
                    origin: Origin::Source(definition),
                    span: definition,
                },
                ImplementationAuthorization::from_hops(hops),
                None,
            )
        };
        let one_hop = imported(vec![ImplementationRouteHop {
            from: ModuleId::new(1),
            to: ModuleId::new(11),
            import_span: first_hop,
        }]);
        let two_hops = imported(vec![
            ImplementationRouteHop {
                from: ModuleId::new(1),
                to: ModuleId::new(10),
                import_span: first_hop,
            },
            ImplementationRouteHop {
                from: ModuleId::new(10),
                to: ModuleId::new(11),
                import_span: second_hop,
            },
        ]);

        let mut one_selector = EvidenceSelector::new();
        one_selector.add_interface_raw(interface, TypeVariableId::new(0), Vec::new());
        let one_registry = one_selector.canonical_registry_for_test();
        let mut one_retention = InterfaceConstraintBudget::default();
        one_selector
            .add_implementation_fact(
                &one_registry,
                &one_hop,
                &mut one_retention,
                &mut TypeWorkBudget::default(),
            )
            .expect("one imported hop should be retained");

        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(interface, TypeVariableId::new(0), Vec::new());
        let registry = selector.canonical_registry_for_test();
        let mut retention = InterfaceConstraintBudget::default();
        let mut retention_types = TypeWorkBudget::default();
        selector
            .add_implementation_fact(&registry, &two_hops, &mut retention, &mut retention_types)
            .expect("both imported hops should be retained");
        assert_eq!(retention.used(), one_retention.used() + 1);
        let mut short_selector = EvidenceSelector::new();
        short_selector.add_interface_raw(interface, TypeVariableId::new(0), Vec::new());
        let short_registry = short_selector.canonical_registry_for_test();
        assert_eq!(
            short_selector.add_implementation_fact(
                &short_registry,
                &two_hops,
                &mut InterfaceConstraintBudget::with_limit(retention.used() - 1),
                &mut TypeWorkBudget::with_limit(retention_types.used()),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        let mut exact_selector = EvidenceSelector::new();
        exact_selector.add_interface_raw(interface, TypeVariableId::new(0), Vec::new());
        let exact_registry = exact_selector.canonical_registry_for_test();
        exact_selector
            .add_implementation_fact(
                &exact_registry,
                &two_hops,
                &mut InterfaceConstraintBudget::with_limit(retention.used()),
                &mut TypeWorkBudget::with_limit(retention_types.used()),
            )
            .expect("the exact two-hop retention budget should admit the implementation");

        let mut one_causes = Vec::new();
        let mut one_selection_work = InterfaceConstraintBudget::default();
        let mut one_selection_types = TypeWorkBudget::default();
        let (checked_argument, _) = one_selector
            .select_owned_for_test(
                interface,
                Type::Int,
                &mut one_causes,
                &mut one_selection_work,
                &mut one_selection_types,
            )
            .expect("the one-hop implementation should select");
        discard_type_iteratively(checked_argument);

        let mut causes = Vec::new();
        let mut selection_work = InterfaceConstraintBudget::default();
        let mut selection_types = TypeWorkBudget::default();
        let (checked_argument, _) = selector
            .select_owned_for_test(
                interface,
                Type::Int,
                &mut causes,
                &mut selection_work,
                &mut selection_types,
            )
            .expect("the transitive imported implementation should select");
        discard_type_iteratively(checked_argument);
        assert_eq!(selection_work.used(), one_selection_work.used() + 1);
        assert_eq!(selection_types.used(), one_selection_types.used());
        let import_causes = causes
            .iter()
            .filter(|cause| cause.kind() == SelectionCauseKind::ImplementationImport)
            .map(|cause| cause.span())
            .collect::<Vec<_>>();
        assert_eq!(import_causes, vec![first_hop, second_hop]);

        assert_eq!(
            selector.select_owned_for_test(
                interface,
                Type::Int,
                &mut Vec::new(),
                &mut InterfaceConstraintBudget::with_limit(selection_work.used() - 1),
                &mut TypeWorkBudget::with_limit(selection_types.used()),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        let (checked_argument, _) = selector
            .select_owned_for_test(
                interface,
                Type::Int,
                &mut Vec::new(),
                &mut InterfaceConstraintBudget::with_limit(selection_work.used()),
                &mut TypeWorkBudget::with_limit(selection_types.used()),
            )
            .expect("the exact cause-retention budget should select");
        discard_type_iteratively(checked_argument);
    }

    #[test]
    fn pending_obligation_retention_has_an_exact_constraint_boundary() {
        let (interface, _, _) = ids();
        let file = SourceFile::new("pending.ash", "x").expect("source");
        let span = file
            .span(ByteRange::new(0, 1).expect("range"))
            .expect("span");
        let mut short = EvidenceSelector::new();
        assert_eq!(
            short.push_obligation(
                interface,
                Type::Int,
                EvidenceSlot::empty().handle(),
                span,
                &mut InterfaceConstraintBudget::with_limit(2),
            ),
            Err(SelectionFailure::ConstraintResource)
        );
        let mut exact = EvidenceSelector::new();
        exact
            .push_obligation(
                interface,
                Type::Int,
                EvidenceSlot::empty().handle(),
                span,
                &mut InterfaceConstraintBudget::with_limit(3),
            )
            .expect("exact pending budget");
    }

    fn lexical_ingress_fixture(depth: usize) -> (EvidenceSelector, InterfaceApplication, Span) {
        let (interface, method, _) = ids();
        let module = interface.module();
        let mut selector = EvidenceSelector::new();
        selector.add_interface_parameters_with_determination_raw(
            interface,
            vec![TypeVariableId::new(0), TypeVariableId::new(1)],
            Some(DeterminationKey::new(Box::new([0]))),
            vec![(method, Type::Unit)],
        );
        let span = selector.interface_entry(interface).expect("interface").span;
        for index in 0..depth {
            selector
                .add_lexical_source(
                    LexicalEvidenceId::new(module, index as u32),
                    test_application(
                        interface,
                        Box::new([
                            Type::Nominal(NominalTypeId::lexical(module, index as u32)),
                            Type::Int,
                        ]),
                    ),
                    span,
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("the distinct lexical source should fit");
        }
        let application = test_application(
            interface,
            Box::new([
                Type::Nominal(NominalTypeId::lexical(module, depth as u32)),
                Type::Int,
            ]),
        );
        (selector, application, span)
    }

    #[test]
    fn lexical_source_ingress_has_an_exact_atomic_retry_boundary() {
        // Source and parent records, then charge_type(N) + charge_type(Int).
        const WORK: usize = 2 + 2 + 2;
        for depth in [0, 1, 256] {
            let (mut selector, application, span) = lexical_ingress_fixture(depth);
            let source = LexicalEvidenceId::new(application.interface().module(), depth as u32);
            let old_head = selector.lexical_head();
            let mut short = InterfaceConstraintBudget::with_limit(WORK - 1);
            assert_eq!(
                selector.add_lexical_source(source, application.clone(), span, &mut short),
                Err(SelectionFailure::ConstraintResource),
            );
            assert_eq!(selector.lexical_sources.len(), depth);
            assert_eq!(selector.lexical_head(), old_head);

            let mut exact = InterfaceConstraintBudget::with_limit(WORK);
            selector
                .add_lexical_source(source, application.clone(), span, &mut exact)
                .expect("the exact budget should retry the unpublished source");
            assert_eq!(exact.used(), WORK);
            assert_eq!(selector.lexical_sources.len(), depth + 1);
            assert_eq!(selector.lexical_head(), Some(depth));
            let retained = &selector.lexical_sources[depth];
            assert_eq!(retained.id, source);
            assert_eq!(retained.parent, old_head);
            assert_eq!(retained.application, application);
        }
    }

    #[test]
    fn owned_pending_ingress_retains_one_scope_head_at_exact_atomic_boundaries() {
        for depth in [0, 1, 256] {
            for retry in [false, true] {
                let (mut selector, application, span) = lexical_ingress_fixture(depth);
                let head = selector.lexical_head();
                // Pending record, optional scope index, and both retained type walks.
                let work = 1 + usize::from(head.is_some()) + 2 + 2;
                let slot = EvidenceSlot::empty();
                // Keep an earlier pending occurrence to check append atomicity too.
                selector
                    .push_owned_obligation(
                        application.clone(),
                        SelectionSite::plain(EvidenceSlot::empty().handle(), span),
                        &mut InterfaceConstraintBudget::default(),
                    )
                    .expect("the existing occurrence should fit");
                let marker = selector.pending_marker();
                if retry {
                    assert_eq!(
                        selector.push_owned_obligation(
                            application.clone(),
                            SelectionSite::plain(slot.handle(), span),
                            &mut InterfaceConstraintBudget::with_limit(work - 1),
                        ),
                        Err(SelectionFailure::ConstraintResource),
                    );
                    assert_eq!(selector.pending.len(), marker.pending_len);
                    assert_eq!(selector.pending_determined_count, marker.determined_count);
                    assert_eq!(selector.pending[0].lexical_head, head);
                    assert_eq!(selector.lexical_head(), head);
                    assert_eq!(selector.lexical_sources.len(), depth);
                    assert!(slot.selection().is_none());
                }
                let mut exact = InterfaceConstraintBudget::with_limit(work);
                selector
                    .push_owned_obligation(
                        application.clone(),
                        SelectionSite::plain(slot.handle(), span),
                        &mut exact,
                    )
                    .expect("the exact budget should retain one occurrence");
                assert_eq!(exact.used(), work);
                assert_eq!(selector.pending.len(), marker.pending_len + 1);
                assert_eq!(
                    selector.pending_determined_count,
                    marker.determined_count + 1
                );
                assert_eq!(selector.lexical_sources.len(), depth);
                assert_eq!(
                    selector.pending[marker.pending_len].application,
                    application
                );

                selector
                    .add_lexical_source(
                        LexicalEvidenceId::new(application.interface().module(), depth as u32),
                        application,
                        span,
                        &mut InterfaceConstraintBudget::default(),
                    )
                    .expect("the later traversal source should fit");
                assert_eq!(selector.lexical_head(), Some(depth));
                assert_eq!(selector.pending[marker.pending_len].lexical_head, head);
                selector.restore_lexical_head(None);
                assert_eq!(selector.pending[marker.pending_len].lexical_head, head);
                assert!(slot.selection().is_none());
            }
        }
    }

    #[test]
    fn cloned_pending_ingress_retains_one_scope_head_at_exact_atomic_dual_boundaries() {
        // The predecessor conditional-method fixture costs 12 constraint units
        // for Int; a complete <N, Int> adds one two-unit retained type walk.
        const BASE_WORK: usize = 12 + 2;
        // Two aligned application cells and two leaf clones.
        const TYPE_WORK: usize = 2 + 2;
        for depth in [0, 1, 256] {
            for failure in [
                None,
                Some(SelectionFailure::ConstraintResource),
                Some(SelectionFailure::TypeResource),
            ] {
                let (mut selector, application, span) = lexical_ingress_fixture(depth);
                let head = selector.lexical_head();
                let work = BASE_WORK + usize::from(head.is_some());
                let metadata = || {
                    MethodObligationMetadata::new(
                        MethodId::new(application.interface(), 0),
                        Box::new([Type::Bool]),
                        Some(MethodRigidityCondition::new(
                            Box::new([Type::Bool]),
                            MethodRigiditySite::application(span, span, span),
                        )),
                    )
                    .with_checked_value_type(Type::Unit)
                };
                let slot = EvidenceSlot::empty();
                selector
                    .push_cloned_obligation(
                        &application,
                        metadata(),
                        SelectionSite::plain(EvidenceSlot::empty().handle(), span),
                        &mut InterfaceConstraintBudget::default(),
                        &mut TypeWorkBudget::default(),
                    )
                    .expect("the existing method occurrence should fit");
                let marker = selector.pending_marker();
                if let Some(failure) = failure {
                    assert_eq!(
                        selector.push_cloned_obligation(
                            &application,
                            metadata(),
                            SelectionSite::plain(slot.handle(), span),
                            &mut InterfaceConstraintBudget::with_limit(
                                work - usize::from(failure == SelectionFailure::ConstraintResource)
                            ),
                            &mut TypeWorkBudget::with_limit(
                                TYPE_WORK - usize::from(failure == SelectionFailure::TypeResource)
                            ),
                        ),
                        Err(failure),
                    );
                    assert_eq!(selector.pending.len(), marker.pending_len);
                    assert_eq!(selector.pending_determined_count, marker.determined_count);
                    assert_eq!(selector.pending_method_rigidity_count, 1);
                    assert_eq!(selector.pending[0].lexical_head, head);
                    assert_eq!(selector.lexical_head(), head);
                    assert_eq!(selector.lexical_sources.len(), depth);
                    assert!(slot.selection().is_none());
                }
                let mut exact = InterfaceConstraintBudget::with_limit(work);
                let mut types = TypeWorkBudget::with_limit(TYPE_WORK);
                selector
                    .push_cloned_obligation(
                        &application,
                        metadata(),
                        SelectionSite::plain(slot.handle(), span),
                        &mut exact,
                        &mut types,
                    )
                    .expect("fresh exact budgets should retain the method occurrence");
                assert_eq!(exact.used(), work);
                assert_eq!(types.used(), TYPE_WORK);
                assert_eq!(selector.pending.len(), marker.pending_len + 1);
                assert_eq!(
                    selector.pending_determined_count,
                    marker.determined_count + 1
                );
                assert_eq!(selector.pending_method_rigidity_count, 2);
                assert_eq!(selector.lexical_sources.len(), depth);
                let pending = &selector.pending[marker.pending_len];
                assert_eq!(pending.application, application);
                assert_eq!(pending.method_arguments.as_ref(), &[Type::Bool]);
                assert_eq!(pending.checked_value_type, Some(Type::Unit));
                selector
                    .add_lexical_source(
                        LexicalEvidenceId::new(application.interface().module(), depth as u32),
                        application,
                        span,
                        &mut InterfaceConstraintBudget::default(),
                    )
                    .expect("the later traversal source should fit");
                assert_eq!(selector.lexical_head(), Some(depth));
                assert_eq!(selector.pending[marker.pending_len].lexical_head, head);
                selector.restore_lexical_head(None);
                assert_eq!(selector.pending[marker.pending_len].lexical_head, head);
                assert!(slot.selection().is_none());
            }
        }
    }

    #[test]
    fn closing_obligation_transfer_has_an_exact_preallocation_boundary() {
        const WIDTH: usize = 128;
        let (interface, _, _) = ids();
        let file = SourceFile::new("pending-close.ash", "x").expect("source");
        let span = file
            .span(ByteRange::new(0, 1).expect("range"))
            .expect("span");
        let mut selector = EvidenceSelector::new();
        let mut setup = InterfaceConstraintBudget::default();
        for _ in 0..WIDTH {
            selector
                .push_obligation(
                    interface,
                    Type::Int,
                    EvidenceSlot::empty().handle(),
                    span,
                    &mut setup,
                )
                .expect("pending fixture");
        }

        let short = selector
            .close(
                PendingObligationMarker::for_test(0, 0),
                |argument, _| Ok(argument),
                &mut InterfaceConstraintBudget::with_limit(WIDTH - 1),
                &mut TypeWorkBudget::default(),
            )
            .expect_err("one missing transfer unit must reject before moving obligations");
        assert_eq!(short.failure(), SelectionFailure::ConstraintResource);
        assert_eq!(short.span(), None);
        assert_eq!(selector.pending.len(), WIDTH);
        assert_eq!(selector.selected.capacity(), 0);

        let task_short = selector
            .close(
                PendingObligationMarker::for_test(0, 0),
                |argument, _| Ok(argument),
                &mut InterfaceConstraintBudget::with_limit(WIDTH),
                &mut TypeWorkBudget::default(),
            )
            .expect_err("one missing task-slot unit should reject the first obligation");
        assert_eq!(task_short.failure(), SelectionFailure::ConstraintResource);
        assert_eq!(task_short.span(), Some(span));
        assert_eq!(selector.pending.len(), WIDTH - 1);
        assert!(selector.selected.capacity() >= WIDTH);

        let reached_first = selector
            .close(
                PendingObligationMarker::for_test(0, 0),
                |argument, _| Ok(argument),
                &mut InterfaceConstraintBudget::with_limit(WIDTH),
                &mut TypeWorkBudget::default(),
            )
            .expect_err("transfer plus one task slot should reach the first obligation");
        assert_eq!(reached_first.failure(), SelectionFailure::InvalidState);
        assert_eq!(reached_first.span(), Some(span));
    }

    #[test]
    fn normal_close_reserves_all_selected_outputs_before_moving_pending_records() {
        const WIDTH: usize = 128;
        let (interface, _, _) = ids();
        let source = SourceFile::new("normal-close-reservation.ash", "x")
            .expect("the reservation source should fit");
        let span = source
            .span(ByteRange::new(0, 1).expect("the reservation range should be ordered"))
            .expect("the reservation span should fit");
        let mut failing = EvidenceSelector::new();
        for _ in 0..WIDTH {
            failing
                .push_obligation(
                    interface,
                    Type::Int,
                    EvidenceSlot::empty().handle(),
                    span,
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("the pending reservation fixture should stage");
        }
        assert_eq!(failing.selected.capacity(), 0);
        let error = failing
            .close_with_registry(
                &ResolvedRegistry::new(Vec::new(), Vec::new()),
                PendingObligationMarker::for_test(0, 0),
                |argument, _| Ok(argument),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect_err("missing interface authority should fail after output reservation");
        assert_eq!(error.failure(), SelectionFailure::InvalidState);
        assert_eq!(failing.pending.len(), WIDTH - 1);
        assert!(
            failing.selected.capacity() >= WIDTH,
            "all selected outputs must reserve before the first pending record moves"
        );

        let method = MethodId::new(interface, 0);
        let current = ImplId::new(interface.module(), 0);
        let mut ordered = EvidenceSelector::new();
        ordered.add_interface_raw(
            interface,
            TypeVariableId::new(0),
            vec![(method, Type::Unit)],
        );
        ordered.add_implementation_raw(implementation(
            current,
            interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(current, method)],
        ));
        let registry = ordered.canonical_registry_for_test();
        ordered
            .enter_implementation_scope(
                current,
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the ordered current scope should fit");
        let marker = ordered.pending_marker();
        for conditional in [true, false, true] {
            let slot = EvidenceSlot::empty();
            if conditional {
                ordered
                    .push_cloned_obligation(
                        &unary_application(interface, Type::Int),
                        MethodObligationMetadata::new(
                            MethodId::new(interface, 0),
                            Box::new([Type::Bool]),
                            Some(MethodRigidityCondition::new(
                                Box::new([Type::Int]),
                                MethodRigiditySite::application(span, span, span),
                            )),
                        ),
                        SelectionSite::plain(slot.handle(), span),
                        &mut InterfaceConstraintBudget::default(),
                        &mut TypeWorkBudget::default(),
                    )
                    .expect("the ordered conditional obligation should stage");
            } else {
                ordered
                    .push_owned_obligation(
                        unary_application(interface, Type::Int),
                        SelectionSite::plain(slot.handle(), span),
                        &mut InterfaceConstraintBudget::default(),
                    )
                    .expect("the ordered plain obligation should stage");
            }
        }
        ordered
            .close_with_registry(
                &registry,
                marker,
                |argument, _| Ok(argument),
                &mut InterfaceConstraintBudget::default(),
                &mut TypeWorkBudget::default(),
            )
            .expect("the pre-reserved output batch should close in source order");
        assert!(ordered.pending.is_empty());
        assert_eq!(ordered.selected.len(), 3);
        assert_eq!(ordered.selected[0].method_arguments.len(), 1);
        assert!(ordered.selected[1].method_arguments.is_empty());
        assert_eq!(ordered.selected[2].method_arguments.len(), 1);
        assert_eq!(ordered.method_rigidities.len(), 2);
        assert_eq!(ordered.method_rigidities[0].selected_index, 0);
        assert_eq!(ordered.method_rigidities[1].selected_index, 2);
    }

    #[test]
    fn closure_zonks_then_fills_the_exact_structural_slot() {
        let (interface, method, _) = ids();
        let concrete = ImplId::new(ModuleId::new(1), 0);
        let mut selector = EvidenceSelector::new();
        selector.add_interface_raw(
            interface,
            TypeVariableId::new(0),
            vec![(method, Type::Unit)],
        );
        selector.add_implementation_raw(implementation(
            concrete,
            interface,
            Vec::new(),
            Type::Int,
            Vec::new(),
            vec![ImplMethodId::new(concrete, method)],
        ));
        let slot = EvidenceSlot::empty();
        let file = SourceFile::new("selection.ash", "x").expect("source");
        let span = file
            .span(ByteRange::new(0, 1).expect("range"))
            .expect("span");
        let mut constraints = InterfaceConstraintBudget::default();
        selector
            .push_obligation(
                interface,
                Type::Inference(crate::types::InferenceVariableId::new(0)),
                slot.handle(),
                span,
                &mut constraints,
            )
            .expect("pending obligation");

        let mut type_work = TypeWorkBudget::default();
        let close_constraint_start = constraints.used();
        selector
            .close(
                PendingObligationMarker::for_test(0, 0),
                |argument, _type_work| {
                    discard_kinded_argument_iteratively(argument);
                    Ok(KindedArgument::TypeArg(Type::Int))
                },
                &mut constraints,
                &mut type_work,
            )
            .expect("selected closure");
        let exact_constraint_work = constraints.used() - close_constraint_start;
        let exact_type_work = type_work.used();

        let (checked_application, selection) = slot.filled().expect("filled exact slot");
        assert_eq!(unary_argument(checked_application), &Type::Int);
        assert_eq!(selection.arguments(), &[KindedArgument::TypeArg(Type::Int)]);
        assert!(matches!(
            selection.node(selection.root()),
            Some(EvidenceNode::Implementation { implementation, .. })
                if implementation == concrete
        ));

        let short_slot = EvidenceSlot::empty();
        selector
            .push_obligation(
                interface,
                Type::Inference(crate::types::InferenceVariableId::new(1)),
                short_slot.handle(),
                span,
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the one-short fixture should retain its obligation");
        assert_eq!(
            selector
                .close(
                    PendingObligationMarker::for_test(0, 0),
                    |argument, _type_work| {
                        discard_kinded_argument_iteratively(argument);
                        Ok(KindedArgument::TypeArg(Type::Int))
                    },
                    &mut InterfaceConstraintBudget::default(),
                    &mut TypeWorkBudget::with_limit(exact_type_work - 1),
                )
                .expect_err("one type-work unit below checked-goal retention must fail")
                .failure(),
            SelectionFailure::TypeResource,
        );
        assert!(short_slot.selection().is_none());

        let constraint_short_slot = EvidenceSlot::empty();
        selector
            .push_obligation(
                interface,
                Type::Inference(crate::types::InferenceVariableId::new(3)),
                constraint_short_slot.handle(),
                span,
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the constraint-short fixture should retain its obligation");
        assert_eq!(
            selector
                .close(
                    PendingObligationMarker::for_test(0, 0),
                    |argument, _type_work| {
                        discard_kinded_argument_iteratively(argument);
                        Ok(KindedArgument::TypeArg(Type::Int))
                    },
                    &mut InterfaceConstraintBudget::with_limit(exact_constraint_work - 1),
                    &mut TypeWorkBudget::with_limit(exact_type_work),
                )
                .expect_err("one constraint unit below task/result retention must fail")
                .failure(),
            SelectionFailure::ConstraintResource,
        );
        assert!(constraint_short_slot.selection().is_none());

        let exact_slot = EvidenceSlot::empty();
        selector
            .push_obligation(
                interface,
                Type::Inference(crate::types::InferenceVariableId::new(2)),
                exact_slot.handle(),
                span,
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the exact fixture should retain its obligation");
        let mut exact_constraints = InterfaceConstraintBudget::with_limit(exact_constraint_work);
        let mut exact = TypeWorkBudget::with_limit(exact_type_work);
        selector
            .close(
                PendingObligationMarker::for_test(0, 0),
                |argument, _type_work| {
                    discard_kinded_argument_iteratively(argument);
                    Ok(KindedArgument::TypeArg(Type::Int))
                },
                &mut exact_constraints,
                &mut exact,
            )
            .expect("the exact checked-goal retention budget should fill its slot");
        assert_eq!(exact.used(), exact_type_work);
        assert_eq!(exact_constraints.used(), exact_constraint_work);
        assert!(matches!(
            exact_slot.filled(),
            Some((application, selected))
                if unary_argument(application) == &Type::Int
                    && selected.arguments() == [KindedArgument::TypeArg(Type::Int)]
        ));
    }

    #[test]
    fn deep_ground_prerequisite_chain_selects_and_drops_on_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(64 * 1024)
            .spawn(|| {
                const DEPTH: usize = 1_000;
                let module = ModuleId::new(9);
                let mut selector = EvidenceSelector::new();
                for index in 0..DEPTH {
                    let declaration = u32::try_from(index).expect("interface index");
                    let interface = InterfaceId::new(module, declaration);
                    let method = MethodId::new(interface, 0);
                    let implementation_id = ImplId::new(module, declaration);
                    selector.add_interface_raw(
                        interface,
                        TypeVariableId::generated(declaration),
                        vec![(method, Type::Unit)],
                    );
                    let prerequisites = if index + 1 == DEPTH {
                        Vec::new()
                    } else {
                        let next = InterfaceId::new(module, declaration + 1);
                        vec![(
                            RequirementId::new(RequirementOwner::Impl(implementation_id), 0),
                            next,
                            Type::Int,
                        )]
                    };
                    selector.add_implementation_raw(implementation(
                        implementation_id,
                        interface,
                        Vec::new(),
                        Type::Int,
                        prerequisites,
                        vec![ImplMethodId::new(implementation_id, method)],
                    ));
                }
                let selection = selector
                    .select(
                        InterfaceId::new(module, 0),
                        &Type::Int,
                        &mut InterfaceConstraintBudget::default(),
                        &mut TypeWorkBudget::default(),
                    )
                    .expect("deep flat selection");
                assert_eq!(selection.node_count(), DEPTH);
            })
            .expect("small-stack selection thread")
            .join()
            .expect("selection and drop stay iterative");
    }

    fn deep_value_type(depth: usize) -> Type {
        let mut ty = Type::Unit;
        for _ in 0..depth {
            ty = Type::Function(Box::new(Type::Unit), Box::new(ty));
        }
        ty
    }

    #[test]
    fn source_free_deep_improvement_key_is_disposed_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("deep-improvement-key-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let module = ModuleId::new(12_002);
                let interface = InterfaceId::new(module, 0);
                let method = MethodId::new(interface, 0);
                let mut selector = EvidenceSelector::new();
                selector.add_interface_parameters_with_determination_raw(
                    interface,
                    vec![
                        TypeVariableId::resolved(module, 0),
                        TypeVariableId::resolved(module, 1),
                    ],
                    Some(DeterminationKey::new(Box::new([0]))),
                    vec![(method, Type::Unit)],
                );
                let span = selector
                    .interface_entry(interface)
                    .expect("the determined interface should remain indexed")
                    .span;
                let registry = selector.canonical_registry_for_test();
                let slot = EvidenceSlot::empty();
                selector
                    .push_owned_obligation(
                        test_application(
                            interface,
                            Box::new([
                                deep_value_type(DEPTH),
                                Type::Inference(crate::types::InferenceVariableId::new(0)),
                            ]),
                        ),
                        SelectionSite::plain(slot.handle(), span),
                        &mut InterfaceConstraintBudget::default(),
                    )
                    .expect("the deep determined obligation should stage");

                let snapshot = selector
                    .prepare_determination_snapshot(
                        &registry,
                        PendingObligationMarker::for_test(0, 0),
                        |ty, _| Ok(ty),
                        &mut InterfaceConstraintBudget::default(),
                        &mut TypeWorkBudget::default(),
                    )
                    .expect("the complete deep key should remain source-free");
                assert_eq!(snapshot.eligible.as_ref(), [true]);
                assert!(snapshot.tasks.is_empty());
            })
            .expect("the deep improvement worker should start")
            .join()
            .expect("source-free deep keys must be dismantled iteratively");
    }

    #[test]
    fn late_improvement_output_failure_disposes_the_deep_source_tuple_iteratively() {
        const DEPTH: usize = 32_768;
        const DEEP_CELLS: usize = 2 * DEPTH + 1;
        // Key output and clone (2), then dependent output and clone
        // (`1 + DEEP_CELLS`). The next actual-output slot is one short.
        const ONE_SHORT_TYPE_WORK: usize = 2 + 1 + DEEP_CELLS;

        std::thread::Builder::new()
            .name("deep-improvement-output-failure".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let module = ModuleId::new(12_003);
                let interface = InterfaceId::new(module, 0);
                let method = MethodId::new(interface, 0);
                let implementation = ImplId::new(module, 0);
                let mut selector = EvidenceSelector::new();
                selector.add_interface_parameters_with_determination_raw(
                    interface,
                    vec![
                        TypeVariableId::resolved(module, 0),
                        TypeVariableId::resolved(module, 1),
                    ],
                    Some(DeterminationKey::new(Box::new([0]))),
                    vec![(method, Type::Unit)],
                );
                let span = selector
                    .interface_entry(interface)
                    .expect("the determined interface should remain indexed")
                    .span;
                selector.abstracts.push(RequirementEntry {
                    id: RequirementId::new(RequirementOwner::Impl(implementation), 0),
                    application: test_application(
                        interface,
                        Box::new([Type::Int, deep_value_type(DEPTH)]),
                    ),
                    span,
                });
                let registry = selector.canonical_registry_for_test();
                let slot = EvidenceSlot::empty();
                selector
                    .push_owned_obligation(
                        test_application(interface, Box::new([Type::Int, Type::Bool])),
                        SelectionSite::plain(slot.handle(), span),
                        &mut InterfaceConstraintBudget::default(),
                    )
                    .expect("the determined obligation should stage");

                assert!(matches!(
                    selector.prepare_determination_snapshot(
                        &registry,
                        PendingObligationMarker::for_test(0, 0),
                        |ty, _| Ok(ty),
                        &mut InterfaceConstraintBudget::default(),
                        &mut TypeWorkBudget::with_limit(ONE_SHORT_TYPE_WORK),
                    ),
                    Err(SelectionFailure::TypeResource),
                ));
            })
            .expect("the late improvement failure worker should start")
            .join()
            .expect("late improvement output failure must dispose the source tuple iteratively");
    }

    #[test]
    fn wide_improvement_candidate_scan_has_an_exact_retryable_boundary() {
        // Complete owner arguments retain explicit scope/kind/tag records;
        // source mirrors preserve their predecessor structural comparison cost.
        const WIDTH: usize = 32_768;
        const EXACT_CONSTRAINT_WORK: usize = (6 + 1) * WIDTH + 11 + 2;
        const EXACT_TYPE_WORK: usize = 6 + 1;

        let source = SourceFile::new("wide-improvement-candidates.ash", "improvement")
            .expect("the wide improvement source should fit");
        let span = source
            .span(ByteRange::new(0, 11).expect("the improvement range should be ordered"))
            .expect("the improvement span should fit");
        let module = ModuleId::from(source.id());
        let interface = InterfaceId::new(module, 0);
        let method = MethodId::new(interface, 0);
        let key_parameter = TypeVariableId::resolved(module, 0);
        let dependent_parameter = TypeVariableId::resolved(module, 1);
        let nominals = (0..WIDTH - 1)
            .map(|index| ResolvedNominalType {
                representation_provenance: None,
                declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                representation: None,
                id: NominalTypeId::new(
                    module,
                    u32::try_from(index).expect("the nominal index should fit"),
                ),
                spelling: format!("Key{index}"),
                constructors: Box::new([]),
                origin: Origin::Source(span),
            })
            .collect::<Vec<_>>();
        let registry = ResolvedRegistry::new(nominals, Vec::new());
        let mut selector = EvidenceSelector::new();
        selector.add_interface_parameters_with_determination_raw(
            interface,
            vec![key_parameter, dependent_parameter],
            Some(DeterminationKey::new(Box::new([0]))),
            vec![(method, Type::Unit)],
        );
        for index in 0..WIDTH {
            let index = u32::try_from(index).expect("the implementation index should fit");
            let implementation = ImplId::new(module, index);
            let key =
                if usize::try_from(index).expect("the candidate index should fit") + 1 == WIDTH {
                    Type::Int
                } else {
                    Type::Nominal(NominalTypeId::new(module, index))
                };
            selector.add_implementation_raw(ImplementationEntry {
                id: implementation,
                application: test_application(interface, Box::new([key, Type::Bool])),
                parameters: Box::new([]),
                prerequisites: Box::new([]),
                methods: Box::new([ImplMethodId::new(implementation, method)]),
                span,
                method_spans: vec![span],
                import_spans: Box::new([]),
            });
        }
        let slot = EvidenceSlot::empty();
        selector
            .push_owned_obligation(
                test_application(
                    interface,
                    Box::new([
                        Type::Int,
                        Type::Inference(crate::types::InferenceVariableId::new(0)),
                    ]),
                ),
                SelectionSite::plain(slot.handle(), span),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the wide improvement obligation should stage");
        let marker = PendingObligationMarker::for_test(0, 0);

        assert!(matches!(
            selector.prepare_determination_snapshot(
                &registry,
                marker,
                |ty, _| Ok(ty),
                &mut InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1),
                &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
            ),
            Err(SelectionFailure::ConstraintResource),
        ));
        assert_eq!(selector.pending.len(), 1);
        assert!(selector.selected.is_empty());
        assert!(slot.selection().is_none());

        let mut exact_constraints = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        let mut exact_types = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
        let snapshot = selector
            .prepare_determination_snapshot(
                &registry,
                marker,
                |ty, _| Ok(ty),
                &mut exact_constraints,
                &mut exact_types,
            )
            .expect("a fresh exact budget should retry the unpublished improvement task");
        assert_eq!(snapshot.eligible.as_ref(), [true]);
        assert_eq!(snapshot.tasks.len(), 1);
        assert_eq!(
            snapshot.tasks[0].key.as_ref(),
            [KindedArgument::TypeArg(Type::Int)]
        );
        assert_eq!(
            snapshot.tasks[0].expected_dependents.as_ref(),
            [KindedArgument::TypeArg(Type::Bool)]
        );
        assert!(matches!(
            snapshot.tasks[0].actual_dependents.as_ref(),
            [KindedArgument::TypeArg(Type::Inference(_))]
        ));
        assert_eq!(exact_types.used(), EXACT_TYPE_WORK);
        assert_eq!(exact_constraints.used(), EXACT_CONSTRAINT_WORK);
    }

    #[test]
    fn owned_evidence_inputs_fail_without_recursive_drop_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("owned-evidence-input-failure".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let (interface, _, requirement) = ids();
                let source = SourceFile::new("owned-evidence.ash", "x")
                    .expect("the evidence fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 1).expect("the range should be ordered"))
                    .expect("the range should belong to the fixture");
                let mut selector = EvidenceSelector::new();
                assert_eq!(
                    selector.push_abstract(
                        requirement,
                        interface,
                        deep_value_type(DEPTH),
                        &mut InterfaceConstraintBudget::with_limit(0),
                    ),
                    Err(SelectionFailure::ConstraintResource),
                );
                let slot = EvidenceSlot::empty();
                assert_eq!(
                    selector.push_owned_obligation(
                        unary_application(interface, deep_value_type(DEPTH)),
                        SelectionSite::plain(slot.handle(), span),
                        &mut InterfaceConstraintBudget::with_limit(0),
                    ),
                    Err(SelectionFailure::ConstraintResource),
                );
            })
            .expect("the small-stack evidence thread should start")
            .join()
            .expect("owned evidence inputs must be dismantled iteratively on failure");
    }

    #[test]
    fn checked_argument_late_constraint_failure_drops_deep_type_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("checked-argument-late-failure".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let module = ModuleId::new(12);
                let interface = InterfaceId::new(module, 0);
                let method = MethodId::new(interface, 0);
                let parameter = TypeVariableId::resolved(module, 0);
                let implementation_id = ImplId::new(module, 0);
                let mut selector = EvidenceSelector::new();
                selector.add_interface_raw(interface, parameter, vec![(method, Type::Unit)]);
                selector.add_implementation_raw(implementation(
                    implementation_id,
                    interface,
                    vec![parameter],
                    Type::Variable(parameter),
                    Vec::new(),
                    vec![ImplMethodId::new(implementation_id, method)],
                ));

                let mut measured_constraints = InterfaceConstraintBudget::with_limit(usize::MAX);
                let mut measured_types = TypeWorkBudget::with_limit(usize::MAX);
                let (checked_argument, selection) = selector
                    .select_owned_for_test(
                        interface,
                        deep_value_type(DEPTH),
                        &mut Vec::new(),
                        &mut measured_constraints,
                        &mut measured_types,
                    )
                    .expect("the measured deep selection should succeed");
                discard_type_iteratively(checked_argument);
                drop(selection);

                assert_eq!(
                    selector.select_owned_for_test(
                        interface,
                        deep_value_type(DEPTH),
                        &mut Vec::new(),
                        &mut InterfaceConstraintBudget::with_limit(
                            measured_constraints.used() - 1,
                        ),
                        &mut TypeWorkBudget::with_limit(measured_types.used()),
                    ),
                    Err(SelectionFailure::ConstraintResource),
                );
            })
            .expect("the checked-argument failure thread should start")
            .join()
            .expect("late checked-argument failure must stay iterative");
    }

    #[test]
    fn duplicate_deep_replacement_is_dismantled_on_a_small_stack() {
        const DEPTH: usize = 32_768;

        std::thread::Builder::new()
            .name("duplicate-evidence-replacement".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let parameter = TypeVariableId::new(0);
                let substitutions = [
                    EvidenceSubstitution::new(parameter, deep_value_type(DEPTH)),
                    EvidenceSubstitution::new(parameter, deep_value_type(DEPTH)),
                ];
                assert!(matches!(
                    replacement_map(&substitutions, &mut TypeWorkBudget::default()),
                    Err(SelectionFailure::InvalidState),
                ));
            })
            .expect("the duplicate-replacement thread should start")
            .join()
            .expect("duplicate replacement teardown must stay iterative");
    }

    #[test]
    fn replacement_map_charges_indexes_and_cloned_arguments_exactly_before_publication() {
        const INDEX_RECORDS: usize = 2;
        const ARGUMENT_NODES: usize = 1 + 3;
        const EXACT_TYPE_WORK: usize = INDEX_RECORDS + ARGUMENT_NODES;

        let module = ModuleId::new(92);
        let first = TypeVariableId::resolved(module, 0);
        let second = TypeVariableId::resolved(module, 1);
        let option = NominalTypeId::new(module, 0);
        let substitutions = [
            EvidenceSubstitution::new(first, Type::Int),
            EvidenceSubstitution::new(
                second,
                Type::Application(Box::new(Type::Nominal(option)), Box::new(Type::Int)),
            ),
        ];

        let mut index_short = TypeWorkBudget::with_limit(INDEX_RECORDS - 1);
        assert!(matches!(
            replacement_map(&substitutions, &mut index_short),
            Err(SelectionFailure::TypeResource)
        ));
        assert_eq!(
            index_short.used(),
            0,
            "the atomic index-record charge must fail before reserve or cloning"
        );

        assert!(
            matches!(
                replacement_map(
                    &substitutions,
                    &mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK - 1),
                ),
                Err(SelectionFailure::TypeResource)
            ),
            "one missing retained Type cell must not publish a replacement map"
        );
        assert_eq!(substitutions[0].argument(), &Type::Int);
        assert!(matches!(
            substitutions[1].argument(),
            Type::Application(function, argument)
                if **function == Type::Nominal(option) && **argument == Type::Int
        ));

        let mut exact = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
        let replacements = replacement_map(&substitutions, &mut exact)
            .expect("the index records plus both cloned arguments should fit exactly");
        assert_eq!(replacements.as_map().get(&first), Some(&Type::Int));
        assert_eq!(
            replacements.as_map().get(&second),
            Some(&Type::Application(
                Box::new(Type::Nominal(option)),
                Box::new(Type::Int),
            ))
        );
        assert_eq!(exact.used(), EXACT_TYPE_WORK);
        assert_eq!(exact.charge(1), Err(()));
    }
}
#[cfg(test)]
mod replacement_owner_api_tests {
    #[test]
    fn recursive_type_replacements_do_not_bypass_the_owner_api() {
        let source: String = include_str!("evidence.rs")
            .chars()
            .filter(|character| !character.is_whitespace())
            .collect();
        let raw_field = ["replacements", ".values"].concat();
        assert!(!source.contains(&raw_field));
        let raw_insert = [".values", ".insert("].concat();
        let raw_reserve = [".values", ".try_reserve("].concat();
        assert_eq!(source.matches(&raw_insert).count(), 1);
        assert_eq!(source.matches(&raw_reserve).count(), 1);
        let broad_mutation = ["impl", "DerefMut", "for", "ReplacementMap"].concat();
        assert!(!source.contains(&broad_mutation));
    }
}
