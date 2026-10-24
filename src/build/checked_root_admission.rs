//! Actual root-local reconstruction after protected running-image verification.
//! No public entry or caller-created data can manufacture this retained context.
use super::{checked_receipt::{ArtifactPin, pin}, gas, host, image};
use crate::{core::ValidatedEffectProgram, foreign::{checked_source::{admit_executable_foreign_symbol,
    check_executable_foreign_library_in_program}, source_bindings::{SourceNativeBindings, SourceOwnerCallback},
    source_runtime::CheckedOwnerLimits}};
use std::sync::Arc;

#[derive(Debug)]
pub(crate) enum RootRefusal {
    Association,
    Resource,
    Output(ash_trusted_preparation::Refusal),
    Image(image::ImageFailure),
    Foreign(crate::foreign::checked_source::ForeignAdmissionError),
    Runtime(crate::eval::RuntimeFailure),
}

/// Exact root-local originals plus the consumed, non-Clone real verifier result.
/// Fields remain private; ordinary admission cannot borrow a source-created bit.
pub(crate) struct RootProgram {
    program: ValidatedEffectProgram,
    modules: Vec<crate::module::ModuleId>,
    bindings: SourceNativeBindings,
    limits: CheckedOwnerLimits,
    scope: usize,
    minimum_observations: usize,
    roles: Vec<[u32; 8]>,
    verified: ash_trusted_preparation::VerifiedRunning,
    work: crate::types::TypeWorkBudget,
}
impl RootProgram {
    pub(crate) fn restore(
        verified: ash_trusted_preparation::VerifiedRunning,
        bytes: &[u8], facts_bytes: &[u8], policy: &[u8], roles: &[[u32; 8]], profile: u8,
    ) -> Result<Self, RootRefusal> {
        let mut work = gas::startup(bytes.len(), facts_bytes.len()).map_err(|()| RootRefusal::Resource)?;
        let count = match profile { 0 => 4, 1 => 2, _ => return Err(RootRefusal::Association) };
        if roles.len() != count { return Err(RootRefusal::Association); }
        work.charge(count * 32 + 8).map_err(|()|RootRefusal::Resource)?;
        let mut retained_roles = Vec::new();
        retained_roles.try_reserve_exact(count).map_err(|_|RootRefusal::Resource)?;
        retained_roles.extend_from_slice(roles);
        let expected = verified.embedded_pins();
        let mut actual = [ArtifactPin { bytes: 0, sha256: [0; 32] }; 4];
        let runtime = super::runtime_fingerprint();
        for (at, raw) in [bytes, facts_bytes, policy, &runtime].into_iter().enumerate() {
            actual[at] = pin(raw, &mut work).map_err(|_| RootRefusal::Resource)?;
            if (actual[at].bytes, actual[at].sha256) != expected[at] { return Err(RootRefusal::Association); }
        }
        let limits = super::checked_producer::decode_policy(policy, actual[0], actual[1], &mut work)
            .map_err(|error| if error == super::checked_receipt::ReceiptFailure::Resource {
                RootRefusal::Resource
            } else { RootRefusal::Association })?;
        let image = image::PureImage::decode_bytes(bytes, &mut work).map_err(RootRefusal::Image)?;
        let facts = image.admit_expected_native_facts(facts_bytes, &mut work).map_err(RootRefusal::Image)?;
        let restored = image.restore_effect(&mut work).map_err(RootRefusal::Image)?;
        // Recheck the exact supported whole-program census under the same
        // startup meter, rather than treating four same-shaped callbacks as H.
        let (scope, minimum_observations) = super::checked_producer::observation_minimum(&restored.program, &mut work)
            .map_err(|error| if error == super::checked_receipt::ReceiptFailure::Resource {
                RootRefusal::Resource
            } else { RootRefusal::Association })?;
        // decode_policy already admitted the fixed complete framing. Retain the
        // actual census for report prepay and join its declared minimum here;
        // trusted request decoding independently regenerated the entire policy.
        work.charge(8).map_err(|()| RootRefusal::Resource)?;
        if policy[100..108] != (minimum_observations as u64).to_le_bytes()
            || limits.observations < minimum_observations { return Err(RootRefusal::Association); }
        work.charge(4 * 8 * 4 + 32).map_err(|()| RootRefusal::Resource)?;
        let mut bindings = SourceNativeBindings::default();
        let scope_owner = match &restored.program.nodes().get(scope).ok_or(RootRefusal::Association)?.kind {
            crate::core::EffectExprKind::Operation(crate::core::EffectOperation::SourceResourceScope(scope)) => &scope.header().owner,
            _ => return Err(RootRefusal::Association),
        };
        for (index, role) in roles.iter().enumerate() {
            let callback = match (profile, index) {
                (0, 0) => SourceOwnerCallback::CheckedAcquire,
                (0, 1) => SourceOwnerCallback::CheckedQuery,
                (0, 2) => SourceOwnerCallback::CheckedLength,
                (0, 3) => SourceOwnerCallback::CheckedFree,
                (1, 0) => SourceOwnerCallback::CheckedOutputAcquire,
                (1, 1) => SourceOwnerCallback::CheckedStatusFree,
                _ => return Err(RootRefusal::Association),
            };
            let [library_slot, module, ordinal, symbol_slot, symbol_index, operation_module, effect, local] = *role;
            // This profile has one library and its complete distinct role originals.
            if role[..3] != roles[0][..3] { return Err(RootRefusal::Association); }
            let original = restored.prepared.get(library_slot as usize).ok_or(RootRefusal::Association)?;
            let expected = facts.library(library_slot, &restored, &mut work).map_err(RootRefusal::Image)?;
            let identity = restored.relocate_library(module, ordinal, &mut work).map_err(RootRefusal::Image)?;
            let checked = check_executable_foreign_library_in_program(identity, Arc::clone(original), &expected,
                host::NATIVE_TARGET, &restored.program, &mut work).map_err(RootRefusal::Foreign)?;
            let source = restored.symbols.get(symbol_slot as usize).ok_or(RootRefusal::Association)?;
            if !source.owner().is_some_and(|owner| Arc::ptr_eq(owner, scope_owner)) {
                return Err(RootRefusal::Association);
            }
            let operation = restored.relocate_operation(operation_module, effect, local, &mut work)
                .map_err(RootRefusal::Image)?;
            let symbol = admit_executable_foreign_symbol(&checked, source, symbol_index as usize, operation, &mut work)
                .map_err(RootRefusal::Foreign)?;
            bindings.insert_owner_checked(symbol, callback, &mut work).map_err(RootRefusal::Runtime)?;
        }
        drop(facts);
        let (program, modules) = restored.into_program_and_modules();
        Ok(Self { program, modules, bindings, limits, scope, minimum_observations, roles: retained_roles, verified, work })
    }
    /// Consumes the real verified context for exactly one evaluator invocation.
    /// Neither a borrowed grant factory nor a replayable run method is exposed.
    pub(crate) fn run(mut self) -> Result<(), RootRefusal> {
        let mut report = super::checked_root_outcome::RootReportPlan::reserve(
            self.limits.history, self.modules.len(), &mut self.work)?;
        self.verified.reserve_outcome_closings(self.limits.history).map_err(RootRefusal::Output)?;
        self.work.charge(self.program.node_count()).map_err(|()| RootRefusal::Resource)?;
        let scope = match &self.program.nodes().get(self.scope).ok_or(RootRefusal::Association)?.kind {
            crate::core::EffectExprKind::Operation(crate::core::EffectOperation::SourceResourceScope(scope)) => scope,
            _ => return Err(RootRefusal::Association),
        };
        let host = self.program.nodes().iter().find_map(|node| match &node.kind {
            crate::core::EffectExprKind::Operation(crate::core::EffectOperation::NativeInterpret(host)) if host.host().is_some() => Some(host),
            _ => None,
        }).ok_or(RootRefusal::Association)?;
        let selector = scope.header().original.host.ok_or(RootRefusal::Association)?;
        let Some(crate::types::KindedArgument::TypeArg(crate::types::Type::Variable(expected))) = scope.arguments().get(selector.position)
            else { return Err(RootRefusal::Association); };
        if host.host().is_none_or(|actual| actual.identity() != *expected) || !host.interpretations().is_empty() {
            return Err(RootRefusal::Association);
        }
        let admission = RootAdmission { program: &self.program, scope, host, limits: self.limits,
            minimum_observations: self.minimum_observations, roles: &self.roles, _verified: &self.verified };
        let outcome = crate::eval::evaluate_checked_root_program(&admission, &mut self.bindings, &mut self.work)
            .map_err(RootRefusal::Runtime)?;
        // Admission's borrow ends before publication; the owned verifier remains
        // in this consumed run context until every mandatory fact is emitted.
        drop(admission);
        report.publish(&mut self.verified, &self.modules, &outcome)
    }

}

/// Private-constructor source/evaluator receipt. The only constructor is above,
/// after real verification, full local reconstruction and output reservation.
pub(crate) struct RootAdmission<'program> {
    program: &'program ValidatedEffectProgram,
    scope: &'program crate::core::SourceResourceScopeNode,
    host: &'program crate::core::NativeInterpretNode,
    limits: CheckedOwnerLimits,
    minimum_observations: usize,
    roles: &'program [[u32; 8]],
    _verified: &'program ash_trusted_preparation::VerifiedRunning,
}
impl std::fmt::Debug for RootAdmission<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RootAdmission").field("minimum_observations", &self.minimum_observations).finish_non_exhaustive()
    }
}
impl<'program> RootAdmission<'program> {
    pub(crate) fn program(&self) -> &'program ValidatedEffectProgram { self.program }
    pub(crate) fn limits(&self) -> CheckedOwnerLimits { self.limits }
    pub(crate) fn report_capacity(&self) -> usize { self.limits.history }
    pub(crate) fn authorizes_host(&self, boundary: &crate::core::NativeInterpretNode,
        work: &mut crate::types::TypeWorkBudget) -> Result<bool, crate::eval::RuntimeFailure> {
        charge_entry(work, 4)?;
        // Pointer equality is only the last exact-borrow check after the complete
        // supported source census, original H/R vectors and four sealed roles.
        Ok(std::ptr::eq(boundary, self.host) && boundary.host() == self.host.host()
            && boundary.interpretations().is_empty() && matches!(self.roles.len(), 2 | 4))
    }
    pub(crate) fn authorizes_scope(&self, scope: &crate::core::SourceResourceScopeNode,
        work: &mut crate::types::TypeWorkBudget) -> Result<bool, crate::eval::RuntimeFailure> {
        charge_entry(work, 2)?;
        Ok(std::ptr::eq(scope, self.scope))
    }
}

fn charge_entry(work: &mut crate::types::TypeWorkBudget, amount: usize) -> Result<(), crate::eval::RuntimeFailure> {
    work.charge(amount).map_err(|()| crate::eval::RuntimeFailure::EnvironmentCapacity.with_resource_details(
        crate::eval::ResourceFailure::new(crate::eval::ResourceFailureCause::WorkBudgetExhausted,
            crate::eval::RuntimePhase::Access, crate::eval::RuntimeResource::WorkUnits,
            Some(amount), Some(work.remaining()))))
}
