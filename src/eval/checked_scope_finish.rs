//! Source completion consumes an actual closing observation, never a status
//! invented from a source constructor or from host destruction.
use super::{
    Control, EffectTraceEvent, HeapCell, Machine, RuntimeFailure, RuntimePhase,
    SourceResourceBoundary, Value, charge_effect_work, resolve_location_with_work,
};
use crate::{
    eval::{ResourceClosing, ResourceDiagnostic, ResourceNativeFact},
    module::{ForeignCheckedNominalRole as Role, ModuleId},
    types::{ConstructorId, NominalTypeId},
};

enum FinishPayload { Consumed(Value), Retained(usize), Local(Value) }

#[derive(Clone, Copy)]
struct ClosingFacts {
    closing: ResourceClosing,
    native: ResourceNativeFact,
    unresolved: bool,
    status: Option<i128>,
}

fn constructor(module: ModuleId, role: Role, ordinal: u32) -> ConstructorId {
    ConstructorId::new(NominalTypeId::new(module, role.local()), ordinal)
}

// This reader never clones the untrusted constructor payload.
fn read_constructor<'a>(heap: &'a [HeapCell], work: &mut crate::types::TypeWorkBudget, value: &Value)
    -> Result<(ConstructorId, &'a Option<Value>), RuntimeFailure> {
    let Value::Location(location) = value else { return Err(RuntimeFailure::ForeignBinding); };
    let location = resolve_location_with_work(heap, *location, work)?;
    match heap.get(location) {
        Some(HeapCell::Constructor(id, payload)) => Ok((*id, payload)),
        _ => Err(RuntimeFailure::ForeignBinding),
    }
}

impl Machine<'_> {
    fn checked_owned_tuple<const N: usize>(&mut self, values: [Value; N]) -> Result<Value, RuntimeFailure> {
        charge_effect_work(&mut self.instantiation_work, N + 1, RuntimePhase::Cleanup)?;
        let mut fields = Vec::new();
        fields.try_reserve_exact(N).map_err(|_| RuntimeFailure::HeapCapacity)?;
        fields.extend(values);
        self.heap.try_reserve(1).map_err(|_| RuntimeFailure::HeapCapacity)?;
        Ok(Value::Location(super::allocate_heap(&mut self.heap, HeapCell::Tuple(fields.into_boxed_slice()))?))
    }

    fn checked_closing_facts(&mut self, boundary: &SourceResourceBoundary) -> Result<ClosingFacts, RuntimeFailure> {
        charge_effect_work(&mut self.instantiation_work, 16, RuntimePhase::Cleanup)?;
        let record = self.checked_reports.as_ref()
            .and_then(|reports| reports.record_for(boundary.report_slot.as_ref()?))
            .ok_or(RuntimeFailure::ForeignBinding)?;
        // The current fixed owner profile requests no diagnostic callback. Do
        // not silently replace another absence class or text with this one.
        if record.diagnostic() != &ResourceDiagnostic::NotRequested {
            return Err(RuntimeFailure::ForeignBinding);
        }
        let checked = boundary.checked.as_ref().ok_or(RuntimeFailure::ForeignBinding)?;
        let (completion, k, native, unresolved) = checked.closing_record().map_err(|_| RuntimeFailure::ForeignBinding)?;
        let expected = crate::eval::ResourceReport::closing_facts(completion, k, native, unresolved, checked.closing_status())
            .ok_or(RuntimeFailure::ForeignBinding)?;
        if &expected != record || record.closing() == ResourceClosing::Transferred {
            return Err(RuntimeFailure::ForeignBinding);
        }
        Ok(ClosingFacts { closing: record.closing(), native: record.native(),
            unresolved: record.unresolved(), status: record.status() })
    }

    fn checked_record_value(&mut self, module: ModuleId, facts: ClosingFacts) -> Result<Value, RuntimeFailure> {
        self.checked_observation_record(module, facts.native, facts.unresolved, facts.status)
    }

    /// Independent last admitted observation only; this constructs no closing
    /// witness and inserts no supervisor report.
    pub(super) fn checked_observation_record(
        &mut self, module: ModuleId, native: ResourceNativeFact,
        unresolved: bool, status: Option<i128>,
    ) -> Result<Value, RuntimeFailure> {
        let status = if let Some(status) = status {
            // Every selected scalar is at most 64 bits. Pay before constructing
            // the independent mathematical integer used by the source codec.
            charge_effect_work(&mut self.instantiation_work, 8, RuntimePhase::Cleanup)?;
            let integer = if status < 0 {
                crate::integer::Integer::from_i64(i64::try_from(status).map_err(|_| RuntimeFailure::ForeignBinding)?)
            } else {
                crate::integer::Integer::from_u64(u64::try_from(status).map_err(|_| RuntimeFailure::ForeignBinding)?)
            };
            self.foreign_constructor(constructor(module, Role::NativeStatus, 1), Some(Value::Integer(integer)), RuntimePhase::Cleanup)?
        } else {
            self.foreign_constructor(constructor(module, Role::NativeStatus, 0), None, RuntimePhase::Cleanup)?
        };
        let native = match native { ResourceNativeFact::NoOwner => 0, ResourceNativeFact::Owned => 1,
            ResourceNativeFact::Consumed => 2, ResourceNativeFact::Unknown => 3 };
        let native = self.foreign_constructor(constructor(module, Role::NativeFact, native), None, RuntimePhase::Cleanup)?;
        let absence = self.foreign_constructor(constructor(module, Role::DiagnosticAbsence, 0), None, RuntimePhase::Cleanup)?;
        let diagnostic = self.foreign_constructor(constructor(module, Role::Diagnostic, 0), Some(absence), RuntimePhase::Cleanup)?;
        let fields = self.foreign_tuple(&[status, native, Value::Boolean(unresolved), diagnostic], RuntimePhase::Cleanup)?;
        self.foreign_constructor(constructor(module, Role::BoundaryRecord, 0), Some(fields), RuntimePhase::Cleanup)
    }

    fn checked_record_matches(&mut self, module: ModuleId, value: &Value, facts: ClosingFacts) -> Result<bool, RuntimeFailure> {
        let (id, payload) = read_constructor(&self.heap, &mut self.instantiation_work, value)?;
        if id != constructor(module, Role::BoundaryRecord, 0) { return Ok(false); }
        let Some(Value::Location(location)) = payload else { return Ok(false); };
        let location = resolve_location_with_work(&self.heap, *location, &mut self.instantiation_work)?;
        charge_effect_work(&mut self.instantiation_work, 5, RuntimePhase::Cleanup)?;
        let Some(HeapCell::Tuple(fields)) = self.heap.get(location) else { return Ok(false); };
        // Copy only fixed handles and a bool. In particular, an adversarial
        // inline integer is never cloned merely to reject its shape.
        let [Value::Location(status), Value::Location(native), Value::Boolean(unresolved), Value::Location(diagnostic)] = fields.as_ref() else { return Ok(false); };
        let (status, native, unresolved, diagnostic) = (*status, *native, *unresolved, *diagnostic);
        if unresolved != facts.unresolved { return Ok(false); }
        let (id, payload) = read_constructor(&self.heap, &mut self.instantiation_work, &Value::Location(status))?;
        let status_matches = match (facts.status, payload) {
            (None, None) => id == constructor(module, Role::NativeStatus, 0),
            (Some(expected), Some(Value::Integer(actual))) => {
                // Length inspection is constant work; conversion is restricted
                // to the selected fixed ABI range and paid before it runs.
                charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Cleanup)?;
                if id != constructor(module, Role::NativeStatus, 1) || actual.magnitude_byte_length() > 8 { false }
                else {
                    charge_effect_work(&mut self.instantiation_work, 8, RuntimePhase::Cleanup)?;
                    if expected < 0 { actual.to_i64().map(i128::from) == Some(expected) }
                    else { actual.to_u64().map(i128::from) == Some(expected) }
                }
            }
            _ => false,
        };
        if !status_matches { return Ok(false); }
        let ordinal = match facts.native { ResourceNativeFact::NoOwner => 0, ResourceNativeFact::Owned => 1,
            ResourceNativeFact::Consumed => 2, ResourceNativeFact::Unknown => 3 };
        let (id, payload) = read_constructor(&self.heap, &mut self.instantiation_work, &Value::Location(native))?;
        if id != constructor(module, Role::NativeFact, ordinal) || payload.is_some() { return Ok(false); }
        let (id, payload) = read_constructor(&self.heap, &mut self.instantiation_work, &Value::Location(diagnostic))?;
        if id != constructor(module, Role::Diagnostic, 0) { return Ok(false); }
        let Some(Value::Location(absence)) = payload else { return Ok(false); };
        let absence = *absence;
        let (id, payload) = read_constructor(&self.heap, &mut self.instantiation_work, &Value::Location(absence))?;
        Ok(id == constructor(module, Role::DiagnosticAbsence, 0) && payload.is_none())
    }

    pub(super) fn return_checked_source_finish(
        &mut self, mut boundary: Box<SourceResourceBoundary>, value: Value,
        finish: [ConstructorId; 3], report: [ConstructorId; 2], completion: [ConstructorId; 3],
    ) -> Result<(), RuntimeFailure> {
        let facts = self.checked_closing_facts(&boundary)?;
        let module = finish[0].owner().module();
        if !module.is_builtin_foreign() || boundary.checked.is_none() { return Err(RuntimeFailure::ForeignBinding); }
        let (id, payload) = read_constructor(&self.heap, &mut self.instantiation_work, &value)?;
        let Some(Value::Location(payload)) = payload else { return Err(RuntimeFailure::ForeignBinding); };
        let payload = Value::Location(*payload);
        let (completion_value, source_failed) = match facts.closing {
            ResourceClosing::NativeConsumed => {
                if id != finish[0] || !boundary.consumed || boundary.owner.is_some()
                    || facts.native != ResourceNativeFact::Consumed || facts.unresolved {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                let (result, error) = read_constructor(&self.heap, &mut self.instantiation_work, &payload)?;
                let failed = if result == constructor(module, Role::FinishResult, 0) && error.is_none() { false }
                    else if result == constructor(module, Role::FinishResult, 1) && error.is_some() { true }
                    else { return Err(RuntimeFailure::ForeignBinding); };
                (FinishPayload::Consumed(payload), failed)
            }
            ResourceClosing::NativeRetained => {
                if id != finish[1] || boundary.consumed || facts.native != ResourceNativeFact::Owned || facts.unresolved {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                let Value::Location(location) = payload else { return Err(RuntimeFailure::ForeignBinding); };
                let location = resolve_location_with_work(&self.heap, location, &mut self.instantiation_work)?;
                charge_effect_work(&mut self.instantiation_work, 2, RuntimePhase::Cleanup)?;
                let Some(HeapCell::Tuple(fields)) = self.heap.get(location) else { return Err(RuntimeFailure::ForeignBinding); };
                let [Value::NativeStateView(key), _error] = fields.as_ref() else { return Err(RuntimeFailure::ForeignBinding); };
                if *key != boundary.key { return Err(RuntimeFailure::ForeignBinding); }
                boundary.owner.as_mut().ok_or(RuntimeFailure::ForeignBinding)?.quarantine();
                // Keep the immutable field coordinate until source completion
                // is admitted. A later proportional copy is output work.
                (FinishPayload::Retained(location), true)
            }
            ResourceClosing::SessionLost | ResourceClosing::DependencyBlocked | ResourceClosing::Quarantined => {
                if id != finish[2] || boundary.consumed { return Err(RuntimeFailure::ForeignBinding); }
                let reason = match facts.closing { ResourceClosing::SessionLost => 0,
                    ResourceClosing::DependencyBlocked => 1, _ => 2 };
                let (id, record) = read_constructor(&self.heap, &mut self.instantiation_work, &payload)?;
                let Some(Value::Location(record)) = record else { return Err(RuntimeFailure::ForeignBinding); };
                let record = Value::Location(*record);
                if id != constructor(module, Role::BoundaryFailure, reason)
                    || !self.checked_record_matches(module, &record, facts)? {
                    return Err(RuntimeFailure::ForeignBinding);
                }
                (FinishPayload::Local(payload), true)
            }
            ResourceClosing::Transferred => return Err(RuntimeFailure::ForeignBinding),
        };
        // The authored Finish has returned and its exact codec/private witness
        // relation is now admitted. Completion survives later host discard or
        // optional wrapper/output failure; neither event can rerun source code.
        boundary.checked.as_ref().ok_or(RuntimeFailure::ForeignBinding)?
            .source_continued(boundary.key.0 as usize, boundary.node)
            .map_err(|_| RuntimeFailure::ForeignBinding)?;
        self.live_resources = self.live_resources.checked_sub(1).ok_or(RuntimeFailure::InvalidControlState)?;
        self.trace_effect(EffectTraceEvent::ResourceReleased(boundary.key.0));
        let returned = if boundary.discarded {
            if source_failed { return Err(RuntimeFailure::ResourceCompletion); }
            Value::Unit
        } else {
            let completion_value = match completion_value {
                FinishPayload::Consumed(result) => {
                    let record = self.checked_record_value(module, facts)?;
                    let fields = self.checked_owned_tuple([result, record])?;
                    self.foreign_constructor(completion[0], Some(fields), RuntimePhase::Cleanup)?
                }
                FinishPayload::Retained(location) => {
                    let Some(HeapCell::Tuple(fields)) = self.heap.get(location) else { return Err(RuntimeFailure::ForeignBinding); };
                    let error = super::copy_generic_cell_value(&fields[1], &mut self.instantiation_work)?;
                    let record = self.checked_record_value(module, facts)?;
                    let fields = self.checked_owned_tuple([error, record])?;
                    self.foreign_constructor(completion[1], Some(fields), RuntimePhase::Cleanup)?
                }
                FinishPayload::Local(reason) => self.foreign_constructor(completion[2], Some(reason), RuntimePhase::Cleanup)?,
            };
            let body = boundary.saved.take().ok_or(RuntimeFailure::InvalidControlState)?;
            let fields = self.checked_owned_tuple([body, completion_value])?;
            self.foreign_constructor(report[1], Some(fields), RuntimePhase::Cleanup)?
        };
        self.control = Some(Control::Return(returned));
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foreign::source_bindings::{ClosingStage, with_eight_byte_closing_for_test};
    use crate::foreign::source_runtime::{CheckedLocalCompletion as K, CheckedNativeFact as Native, CheckedOwnerContinuation};
    use crate::types::TypeWorkBudget;

    fn with_case(stage: ClosingStage, test: impl FnOnce(Machine<'_>, Box<SourceResourceBoundary>, [ConstructorId; 3])) {
        with_eight_byte_closing_for_test(stage, |program, node, checked, owner| {
            let mut machine = Machine::new_effect(program);
            machine.control = None;
            machine.live_resources = 1;
            let mut setup = TypeWorkBudget::default();
            let mut reports = crate::eval::checked_reports::ResourceReports::reserve(1, &mut setup).unwrap();
            let slot = reports.reserve_owner(&mut setup).unwrap();
            let (completion, k, native, unresolved) = checked.closing_record().unwrap();
            if let Some(record) = crate::eval::ResourceReport::closing_facts(completion, k, native, unresolved, checked.closing_status()) {
                reports.commit_owner(&slot, record);
            }
            machine.checked_reports = Some(reports);
            let finish = machine.source_resource_scope(node).unwrap().header().codec.finish;
            let boundary = Box::new(SourceResourceBoundary {
                checked: Some(checked), report_slot: Some(slot), node, key: super::super::ActivationKey(111),
                environment: super::super::Environment::new(), owner, dependencies: Vec::new(),
                phase: super::super::ProviderPhase::Finish, payload: None, saved: Some(Value::Unit),
                consumed: native == Native::Consumed, blocked: false, discarded: false,
            });
            test(machine, boundary, finish);
        });
    }

    fn outcome(machine: &mut Machine<'_>, boundary: &SourceResourceBoundary, finish: [ConstructorId; 3]) -> Value {
        let module = finish[0].owner().module();
        let facts = machine.checked_closing_facts(boundary).unwrap();
        match facts.closing {
            ResourceClosing::NativeConsumed => {
                let ok = machine.foreign_constructor(constructor(module, Role::FinishResult, 0), None, RuntimePhase::Cleanup).unwrap();
                machine.foreign_constructor(finish[0], Some(ok), RuntimePhase::Cleanup).unwrap()
            }
            ResourceClosing::NativeRetained => {
                let pair = machine.foreign_tuple(&[Value::NativeStateView(boundary.key), Value::Unit], RuntimePhase::Cleanup).unwrap();
                machine.foreign_constructor(finish[1], Some(pair), RuntimePhase::Cleanup).unwrap()
            }
            ResourceClosing::Quarantined => {
                let record = machine.checked_record_value(module, facts).unwrap();
                let failure = machine.foreign_constructor(constructor(module, Role::BoundaryFailure, 2), Some(record), RuntimePhase::Cleanup).unwrap();
                machine.foreign_constructor(finish[2], Some(failure), RuntimePhase::Cleanup).unwrap()
            }
            _ => panic!("fixture is an actual native or synthetic closing"),
        }
    }

    #[test]
    fn checked_scope_uses_actual_closing_and_completes_source_once() {
        for stage in [ClosingStage::Consumed, ClosingStage::Retained, ClosingStage::Synthetic] {
            with_case(stage, |mut machine, boundary, finish| {
                let checked = boundary.checked.as_ref().unwrap().prepaid_scope_observer();
                let node = boundary.node;
                let slot = boundary.report_slot.as_ref().unwrap().observer();
                let value = outcome(&mut machine, &boundary, finish);
                machine.return_source_resource(boundary, value).unwrap();
                assert_eq!(checked.snapshot().continuation, CheckedOwnerContinuation::Completed);
                assert_eq!(checked.snapshot().k, K::Discharged);
                assert_eq!(machine.checked_reports.as_ref().unwrap().record_count(), 1);
                assert!(machine.checked_reports.as_ref().unwrap().record_for(&slot).is_some());
                assert!(checked.source_continued(111, node).is_err());
                assert!(matches!(machine.control, Some(Control::Return(_))));
                assert_eq!(machine.live_resources, 0);
                let before = checked.snapshot();
                machine.settle_checked_observer(&checked, Some(&slot), crate::eval::GuardInspectionPoint::ReturnFailureAfterDisposal);
                assert_eq!(machine.checked_reports.as_ref().unwrap().record_count(), 1);
                assert_eq!(checked.snapshot().native, before.native);
            });
        }
    }

    #[test]
    fn checked_scope_rejects_wrong_finish_pair_and_keeps_committed_record() {
        for stage in [ClosingStage::Consumed, ClosingStage::Retained, ClosingStage::Synthetic] {
            with_case(stage, |mut machine, boundary, finish| {
                let checked = boundary.checked.as_ref().unwrap().prepaid_scope_observer();
                let slot = boundary.report_slot.as_ref().unwrap().observer();
                let original = machine.checked_reports.as_ref().unwrap().record_for(&slot).unwrap().clone();
                let wrong = machine.foreign_constructor(finish[if matches!(stage, ClosingStage::Consumed) { 1 } else { 0 }], Some(Value::Unit), RuntimePhase::Cleanup).unwrap();
                assert_eq!(machine.return_source_resource(boundary, wrong), Err(RuntimeFailure::ForeignBinding));
                assert_eq!(machine.checked_reports.as_ref().unwrap().record_for(&slot), Some(&original));
                assert_eq!(machine.checked_reports.as_ref().unwrap().record_count(), 1);
                assert_eq!(checked.snapshot().continuation, CheckedOwnerContinuation::Required);
                assert!(checked.snapshot().terminal);
                assert!(machine.control.is_none());
            });
        }
    }

    #[test]
    fn checked_scope_rejects_forged_synthetic_record_and_missing_request_witness() {
        for requested in [true, false] {
            with_case(if requested { ClosingStage::Synthetic } else { ClosingStage::SyntheticNotRequested }, |mut machine, boundary, finish| {
                let checked = boundary.checked.as_ref().unwrap().prepaid_scope_observer();
                let module = finish[0].owner().module();
                let mut facts = machine.checked_closing_facts(&boundary).unwrap();
                if requested { facts.status = Some(0); } // Absence is not zero.
                let record = machine.checked_record_value(module, facts).unwrap();
                let failure = machine.foreign_constructor(constructor(module, Role::BoundaryFailure, 2), Some(record), RuntimePhase::Cleanup).unwrap();
                let value = machine.foreign_constructor(finish[2], Some(failure), RuntimePhase::Cleanup).unwrap();
                assert_eq!(machine.return_source_resource(boundary, value), Err(RuntimeFailure::ForeignBinding));
                assert_eq!(checked.snapshot().continuation, CheckedOwnerContinuation::Required);
                assert!(machine.control.is_none());
                assert_eq!(machine.checked_reports.as_ref().unwrap().record_count(), 1);
            });
        }
    }

    #[test]
    fn checked_discarded_finish_error_completes_source_before_host_failure() {
        with_case(ClosingStage::Consumed, |mut machine, mut boundary, finish| {
            let checked = boundary.checked.as_ref().unwrap().prepaid_scope_observer();
            let slot = boundary.report_slot.as_ref().unwrap().observer();
            boundary.discarded = true;
            boundary.saved = None;
            let error = machine.foreign_constructor(constructor(finish[0].owner().module(), Role::FinishResult, 1), Some(Value::Unit), RuntimePhase::Cleanup).unwrap();
            let value = machine.foreign_constructor(finish[0], Some(error), RuntimePhase::Cleanup).unwrap();
            assert_eq!(machine.return_source_resource(boundary, value), Err(RuntimeFailure::ResourceCompletion));
            assert_eq!(checked.snapshot().continuation, CheckedOwnerContinuation::Completed);
            assert_eq!(checked.snapshot().k, K::Discharged);
            assert_eq!(checked.snapshot().native, Native::Consumed);
            assert!(checked.snapshot().terminal);
            assert!(machine.control.is_none());
            assert_eq!(machine.checked_reports.as_ref().unwrap().record_count(), 1);
            assert_eq!(machine.checked_reports.as_ref().unwrap().record_for(&slot).unwrap().status(), None);
        });
    }

    #[test]
    fn checked_optional_wrapper_failure_keeps_completed_source_and_native_record() {
        with_case(ClosingStage::Consumed, |mut machine, boundary, finish| {
            let checked = boundary.checked.as_ref().unwrap().prepaid_scope_observer();
            let slot = boundary.report_slot.as_ref().unwrap().observer();
            let value = outcome(&mut machine, &boundary, finish);
            // Sixteen fixed fact checks plus the two direct constructor reads
            // admit Finish. The next unit is optional wrapper construction.
            machine.instantiation_work = TypeWorkBudget::with_limit(18);
            assert!(machine.return_source_resource(boundary, value).is_err());
            assert_eq!(machine.instantiation_work.used(), 18);
            assert_eq!(checked.snapshot().continuation, CheckedOwnerContinuation::Completed);
            assert_eq!(checked.snapshot().k, K::Discharged);
            assert_eq!(checked.snapshot().native, Native::Consumed);
            assert!(checked.snapshot().terminal);
            assert!(machine.control.is_none());
            assert_eq!(machine.checked_reports.as_ref().unwrap().record_count(), 1);
            assert_eq!(machine.checked_reports.as_ref().unwrap().record_for(&slot).unwrap().status(), None);
        });
    }

    fn huge_integer() -> Value {
        Value::Integer(crate::integer::Integer::parse_decimal(&"9".repeat(10_000)).unwrap())
    }

    #[test]
    fn huge_native_status_is_borrowed_and_refused_before_source_completion() {
        with_case(ClosingStage::Synthetic, |mut machine, boundary, finish| {
            let checked = boundary.checked.as_ref().unwrap().prepaid_scope_observer();
            let module = finish[0].owner().module();
            let facts = machine.checked_closing_facts(&boundary).unwrap();
            let status = machine.foreign_constructor(constructor(module, Role::NativeStatus, 1), Some(huge_integer()), RuntimePhase::Cleanup).unwrap();
            let native = machine.foreign_constructor(constructor(module, Role::NativeFact, 1), None, RuntimePhase::Cleanup).unwrap();
            let absence = machine.foreign_constructor(constructor(module, Role::DiagnosticAbsence, 0), None, RuntimePhase::Cleanup).unwrap();
            let diagnostic = machine.foreign_constructor(constructor(module, Role::Diagnostic, 0), Some(absence), RuntimePhase::Cleanup).unwrap();
            let fields = machine.checked_owned_tuple([status, native, Value::Boolean(facts.unresolved), diagnostic]).unwrap();
            let record = machine.foreign_constructor(constructor(module, Role::BoundaryRecord, 0), Some(fields), RuntimePhase::Cleanup).unwrap();
            machine.instantiation_work = TypeWorkBudget::default();
            assert!(!machine.checked_record_matches(module, &record, facts).unwrap());
            let cost = machine.instantiation_work.used();
            assert!(cost < 32); // No magnitude-sized clone or conversion.
            machine.instantiation_work = TypeWorkBudget::with_limit(cost - 1);
            assert!(machine.checked_record_matches(module, &record, facts).is_err());
            machine.instantiation_work = TypeWorkBudget::with_limit(cost);
            assert!(!machine.checked_record_matches(module, &record, facts).unwrap());
            assert!(machine.checked_record_matches(module, &record, facts).is_err());
            // A genuine absent status and a claimed present status take
            // different guards. Exercise the actual bounded-conversion arm.
            let present = ClosingFacts { status: Some(7), ..facts };
            machine.instantiation_work = TypeWorkBudget::default();
            assert!(!machine.checked_record_matches(module, &record, present).unwrap());
            let present_cost = machine.instantiation_work.used();
            assert_eq!(present_cost, cost + 1);
            machine.instantiation_work = TypeWorkBudget::with_limit(present_cost - 1);
            assert!(machine.checked_record_matches(module, &record, present).is_err());
            machine.instantiation_work = TypeWorkBudget::with_limit(present_cost);
            assert!(!machine.checked_record_matches(module, &record, present).unwrap());
            assert!(machine.checked_record_matches(module, &record, present).is_err());
            machine.instantiation_work = TypeWorkBudget::default();
            let failure = machine.foreign_constructor(constructor(module, Role::BoundaryFailure, 2), Some(record), RuntimePhase::Cleanup).unwrap();
            let value = machine.foreign_constructor(finish[2], Some(failure), RuntimePhase::Cleanup).unwrap();
            assert_eq!(machine.return_source_resource(boundary, value), Err(RuntimeFailure::ForeignBinding));
            assert_eq!(checked.snapshot().continuation, CheckedOwnerContinuation::Required);
            assert_eq!(checked.snapshot().k, K::Discharged);
            assert_eq!(machine.checked_reports.as_ref().unwrap().record_count(), 1);
        });
    }

    #[test]
    fn retained_huge_error_copy_is_paid_after_finish_admission() {
        let mut measured = 0;
        for pass in 0..4 {
            with_case(ClosingStage::Retained, |mut machine, boundary, finish| {
                let checked = boundary.checked.as_ref().unwrap().prepaid_scope_observer();
                let slot = boundary.report_slot.as_ref().unwrap().observer();
                let fields = machine.checked_owned_tuple([Value::NativeStateView(boundary.key), huge_integer()]).unwrap();
                let value = machine.foreign_constructor(finish[1], Some(fields), RuntimePhase::Cleanup).unwrap();
                machine.instantiation_work = TypeWorkBudget::with_limit(match pass {
                    0 => 32_768, 1 => 20, 2 => measured - 1, _ => measured,
                });
                let result = machine.return_source_resource(boundary, value);
                if pass == 0 {
                    result.unwrap();
                    measured = machine.instantiation_work.used();
                    assert!(measured > 4_000);
                } else if pass == 3 {
                    result.unwrap();
                    assert_eq!(machine.instantiation_work.used(), measured);
                    assert!(charge_effect_work(&mut machine.instantiation_work, 1, RuntimePhase::Cleanup).is_err());
                } else {
                    assert!(result.is_err());
                    assert!(machine.control.is_none());
                    assert!(checked.snapshot().terminal);
                }
                assert_eq!(checked.snapshot().continuation, CheckedOwnerContinuation::Completed);
                assert_eq!(checked.snapshot().k, K::Discharged);
                assert_eq!(checked.snapshot().native, Native::Owned);
                assert_eq!(machine.checked_reports.as_ref().unwrap().record_count(), 1);
                assert_eq!(machine.checked_reports.as_ref().unwrap().record_for(&slot).unwrap().status(), None);
            });
        }
    }

    #[test]
    fn opaque_body_and_consumed_error_move_without_magnitude_copy() {
        let mut unit_cost = 0;
        for huge in [false, true] {
            with_case(ClosingStage::Consumed, |mut machine, mut boundary, finish| {
                let checked = boundary.checked.as_ref().unwrap().prepaid_scope_observer();
                boundary.saved = Some(if huge { huge_integer() } else { Value::Unit });
                let error = machine.foreign_constructor(constructor(finish[0].owner().module(), Role::FinishResult, 1), Some(if huge { huge_integer() } else { Value::Unit }), RuntimePhase::Cleanup).unwrap();
                let value = machine.foreign_constructor(finish[0], Some(error), RuntimePhase::Cleanup).unwrap();
                machine.instantiation_work = TypeWorkBudget::with_limit(if huge { unit_cost } else { 256 });
                machine.return_source_resource(boundary, value).unwrap();
                if huge { assert_eq!(machine.instantiation_work.used(), unit_cost); }
                else { unit_cost = machine.instantiation_work.used(); }
                assert!(matches!(machine.control, Some(Control::Return(_))));
                assert_eq!(checked.snapshot().continuation, CheckedOwnerContinuation::Completed);
                assert_eq!(checked.snapshot().k, K::Discharged);
                assert_eq!(machine.checked_reports.as_ref().unwrap().record_count(), 1);
            });
        }
        with_case(ClosingStage::Consumed, |mut machine, mut boundary, finish| {
            let checked = boundary.checked.as_ref().unwrap().prepaid_scope_observer();
            boundary.saved = Some(huge_integer());
            let value = outcome(&mut machine, &boundary, finish);
            machine.instantiation_work = TypeWorkBudget::with_limit(18);
            assert!(machine.return_source_resource(boundary, value).is_err());
            assert_eq!(checked.snapshot().continuation, CheckedOwnerContinuation::Completed);
            assert_eq!(machine.checked_reports.as_ref().unwrap().record_count(), 1);
        });
    }

    #[cfg(not(ash_checked_owner_root = "v1"))]
    #[test]
    fn genuine_output_status_refusal_preserves_acquisition_and_disposal_inspections() {
        use crate::foreign::{checked_leaf_reset as reset, checked_leaf_calls as calls,
            checked_leaf_output_status as output_status, checked_leaf_disposal as disposal,
            source_bindings::with_output_status_unpublished_for_test};
        for (consumed, denied, output_failed) in [(true,false,false),(false,false,false),(true,true,false),(true,false,true)] {
            reset(); output_status(-11); disposal(Some(consumed), Some(if consumed {0}else{7}), true);
            with_output_status_unpublished_for_test(|program, node, checked, owner| {
                if denied { owner.as_ref().unwrap().install_shared_denial_for_test(); }
                let mut machine = Machine::new_effect(program);
                machine.control = None; machine.live_resources = 1;
                let mut setup = TypeWorkBudget::default();
                let mut reports = crate::eval::checked_reports::ResourceReports::reserve(1, &mut setup).unwrap();
                let slot = reports.reserve_owner(&mut setup).unwrap(); machine.checked_reports = Some(reports);
                let codec = machine.source_resource_scope(node).unwrap().header().codec;
                let value = machine.foreign_constructor(codec.acquire[1], Some(Value::Unit), RuntimePhase::Acquisition).unwrap();
                if output_failed {
                    let Value::Location(location) = &value else { unreachable!() };
                    let mut probe = TypeWorkBudget::default();
                    super::super::resolve_location_with_work(&machine.heap, *location, &mut probe).unwrap();
                    machine.instantiation_work = TypeWorkBudget::with_limit(probe.used());
                }
                let boundary = Box::new(SourceResourceBoundary {
                    checked: Some(checked.prepaid_scope_observer()), report_slot: Some(slot), node,
                    key: super::super::ActivationKey(111), environment: super::super::Environment::new(),
                    owner, dependencies: Vec::new(), phase: super::super::ProviderPhase::Acquire,
                    payload: None, saved: None, consumed: false, blocked: false, discarded: false,
                });
                assert_eq!(machine.return_source_resource(boundary, value).is_err(), output_failed);
                assert_eq!(checked.snapshot().k, K::Absent);
                assert_eq!(checked.snapshot().native, if consumed && !denied {Native::Consumed}else{Native::Owned});
                assert_eq!(checked.snapshot().continuation, CheckedOwnerContinuation::Absent);
                assert_eq!(calls(), [1,0,0,0,usize::from(!denied)]);
                let (closings, guards) = machine.checked_reports.take().unwrap().into_inspections();
                assert!(closings.is_empty()); assert_eq!(guards.len(),1);
                assert_eq!(guards[0].acquisition_status(),Some(-11));
                assert_eq!(guards[0].status(),Some(if denied {-11}else if consumed {0}else{7}));
            });
        }
    }

    #[test]
    fn successful_unpublished_refusal_and_discard_keep_separate_guard_inspection() {
        for discarded in [false, true] {
            with_case(ClosingStage::Armed, |mut machine, mut boundary, _finish| {
                let checked = boundary.checked.as_ref().unwrap().prepaid_scope_observer();
                let slot = boundary.report_slot.as_ref().unwrap().observer();
                boundary.phase = super::super::ProviderPhase::Acquire;
                boundary.discarded = discarded;
                boundary.saved = None;
                let codec = machine.source_resource_scope(boundary.node).unwrap().header().codec;
                let value = if discarded { Value::Unit } else {
                    machine.foreign_constructor(codec.acquire[1], Some(Value::Unit), RuntimePhase::Acquisition).unwrap()
                };
                machine.return_source_resource(boundary, value).unwrap();
                assert_eq!(checked.snapshot().k, K::Absent);
                assert_eq!(checked.snapshot().native, Native::Owned); // Do not invent a C observation.
                assert!(slot.published().is_none());
                assert_eq!(checked.snapshot().continuation, CheckedOwnerContinuation::Absent);
                assert!(slot.settled());
                assert_eq!(machine.live_resources, 0);
                assert!(matches!(machine.control, Some(Control::Return(_))));
                let reports = machine.checked_reports.take().unwrap();
                let (records, guards) = reports.into_inspections();
                assert!(records.is_empty());
                assert_eq!(guards.len(), 1);
                assert_eq!(guards[0].point(), crate::eval::GuardInspectionPoint::AfterUnpublishedDisposal);
                assert_eq!(guards[0].native(), ResourceNativeFact::Owned);
                assert_eq!(guards[0].status(), None);
                assert!(!guards[0].unresolved());
                // Inspect the actual post-disposal slot; absence alone is not
                // a separately admitted native-consumption observation.
                assert_eq!(guards[0].backing(), if checked.retains_backing() {
                    crate::eval::GuardBackingObservation::Retained
                } else { crate::eval::GuardBackingObservation::Unknown });
            });
        }
    }

    #[cfg(not(ash_checked_owner_root = "v1"))]
    #[test]
    fn unpublished_leaf_refusal_discard_and_output_failure_dispose_before_reporting() {
        use crate::foreign::{checked_leaf_calls as leaf_calls, checked_leaf_reset as leaf_reset,
            checked_leaf_null_next as leaf_null_next,
            source_bindings::with_unpublished_leaf_for_test};
        for (discarded, output_failed, blocked, shared_denied, null) in [
            (false, false, false, false, false), (true, false, false, false, false),
            (false, true, false, false, false), (false, false, true, false, false),
            (false, false, false, true, false), (false, false, false, false, true),
        ] {
            leaf_reset();
            if null { leaf_null_next(); }
            with_unpublished_leaf_for_test(|program, node, checked, owner| {
                if shared_denied { owner.as_ref().unwrap().install_shared_denial_for_test(); }
                let mut machine = Machine::new_effect(program);
                machine.control = None;
                machine.live_resources = 1;
                let mut setup = TypeWorkBudget::default();
                let mut reports = crate::eval::checked_reports::ResourceReports::reserve(1, &mut setup).unwrap();
                let slot = reports.reserve_owner(&mut setup).unwrap();
                machine.checked_reports = Some(reports);
                let codec = machine.source_resource_scope(node).unwrap().header().codec;
                let value = if discarded { Value::Unit } else {
                    machine.foreign_constructor(codec.acquire[1], Some(Value::Unit), RuntimePhase::Acquisition).unwrap()
                };
                if output_failed {
                    let Value::Location(location) = &value else { unreachable!() };
                    let mut probe = TypeWorkBudget::default();
                    super::super::resolve_location_with_work(&machine.heap, *location, &mut probe).unwrap();
                    machine.instantiation_work = TypeWorkBudget::with_limit(probe.used());
                }
                let boundary = Box::new(SourceResourceBoundary {
                    checked: Some(checked.prepaid_scope_observer()), report_slot: Some(slot), node,
                    key: super::super::ActivationKey(111), environment: super::super::Environment::new(),
                    owner, dependencies: Vec::new(), phase: super::super::ProviderPhase::Acquire,
                    payload: None, saved: None, consumed: false, blocked, discarded,
                });
                let result = machine.return_source_resource(boundary, value);
                assert_eq!(result.is_err(), output_failed);
                let called = !blocked && !shared_denied && !null;
                assert_eq!(leaf_calls(), [1, 0, 0, 0, usize::from(called)]);
                let snapshot = checked.snapshot();
                assert_eq!(snapshot.k, K::Absent);
                assert_eq!(snapshot.native, if null { Native::NoOwner } else if called { Native::Consumed } else { Native::Owned });
                assert!(!snapshot.unresolved);
                assert_eq!(snapshot.continuation, CheckedOwnerContinuation::Absent);
                let (scope, guards) = machine.checked_reports.take().unwrap().into_inspections();
                assert!(scope.is_empty());
                assert_eq!(guards.len(), usize::from(!null));
                if let Some(guard) = guards.first() {
                    assert_eq!(guard.native(), if called { ResourceNativeFact::Consumed } else { ResourceNativeFact::Owned });
                    assert_eq!(guard.status(), None);
                    assert_eq!(guard.acquisition_status(), None);
                }
                assert_eq!(checked.retains_backing(), blocked || shared_denied);
                // Dropping remaining evaluator metadata cannot retry Free.
                drop(machine);
                assert_eq!(leaf_calls()[4], usize::from(called));
            });
        }
    }

    #[cfg(not(ash_checked_owner_root = "v1"))]
    #[test]
    fn huge_typed_refusal_copy_is_funded_after_disposal_and_survives_one_short() {
        use crate::foreign::{checked_leaf_calls as leaf_calls, checked_leaf_reset as leaf_reset,
            source_bindings::with_unpublished_int_refusal_for_test};
        let mut measured = 0;
        for pass in 0..4 {
            leaf_reset();
            with_unpublished_int_refusal_for_test(|program, node, checked, owner| {
                let mut machine = Machine::new_effect(program);
                machine.control = None; machine.live_resources = 1;
                let mut setup = TypeWorkBudget::default();
                let mut reports = crate::eval::checked_reports::ResourceReports::reserve(1, &mut setup).unwrap();
                let slot = reports.reserve_owner(&mut setup).unwrap();
                machine.checked_reports = Some(reports);
                let codec = machine.source_resource_scope(node).unwrap().header().codec;
                let huge = huge_integer();
                let Value::Integer(integer) = &huge else { unreachable!() };
                let magnitude = usize::try_from(integer.magnitude_byte_length()).unwrap();
                let value = machine.foreign_constructor(codec.acquire[1], Some(huge), RuntimePhase::Acquisition).unwrap();
                let prefix = usize::from(pass == 3) * 7;
                machine.instantiation_work = TypeWorkBudget::with_limit(match pass {
                    0 => 327_680, 1 => measured - 1, _ => measured + prefix,
                });
                machine.instantiation_work.charge(prefix).unwrap();
                let boundary = Box::new(SourceResourceBoundary {
                    checked: Some(checked.prepaid_scope_observer()), report_slot: Some(slot), node,
                    key: super::super::ActivationKey(111), environment: super::super::Environment::new(),
                    owner, dependencies: Vec::new(), phase: super::super::ProviderPhase::Acquire,
                    payload: None, saved: None, consumed: false, blocked: false, discarded: false,
                });
                let result = machine.return_source_resource(boundary, value);
                assert_eq!(result.is_err(), pass == 1);
                if pass == 0 {
                    measured = machine.instantiation_work.used();
                    assert!(measured > magnitude, "magnitude copy is funded, not only its field slot");
                } else if pass != 1 {
                    assert_eq!(machine.instantiation_work.used(), measured + prefix);
                }
                assert_eq!(checked.snapshot().native, Native::Consumed);
                assert_eq!(checked.snapshot().k, K::Absent);
                assert!(!checked.snapshot().unresolved);
                let (scope, guards) = machine.checked_reports.take().unwrap().into_inspections();
                assert!(scope.is_empty()); assert_eq!(guards.len(), 1);
                assert_eq!(guards[0].native(), ResourceNativeFact::Consumed);
                drop(machine);
                assert_eq!(leaf_calls(), [1, 0, 0, 0, 1]);
            });
        }
    }

    #[test]
    fn failed_unpublished_return_has_after_disposal_point_and_no_scope_closing() {
        with_case(ClosingStage::Armed, |mut machine, mut boundary, _finish| {
            let checked = boundary.checked.as_ref().unwrap().prepaid_scope_observer();
            boundary.phase = super::super::ProviderPhase::Acquire;
            assert_eq!(machine.return_source_resource(boundary, Value::Unit), Err(RuntimeFailure::ForeignBinding));
            let (records, guards) = machine.checked_reports.take().unwrap().into_inspections();
            assert!(records.is_empty());
            assert_eq!(guards.len(), 1);
            assert_eq!(guards[0].point(), crate::eval::GuardInspectionPoint::ReturnFailureAfterDisposal);
            assert_eq!(checked.snapshot().k, K::Absent);
            assert_eq!(checked.snapshot().continuation, CheckedOwnerContinuation::Absent);
        });
    }

    #[test]
    fn terminal_machine_settles_published_owner_and_separates_unpublished_guard() {
        for stage in [ClosingStage::Reserved, ClosingStage::Armed, ClosingStage::Body] {
            with_case(stage, |mut machine, mut boundary, _finish| {
                let checked = boundary.checked.as_ref().unwrap().prepaid_scope_observer();
                boundary.phase = if matches!(stage, ClosingStage::Body) { super::super::ProviderPhase::Body }
                    else { super::super::ProviderPhase::Acquire };
                machine.frames.push(super::super::Frame::SourceResourceBoundary(boundary));
                // No executable/binding/context is installed. This actual run
                // reaches InvalidControlState and structural terminal disposal.
                machine.control = None;
                let result = machine.run_with_reports();
                assert_eq!(result.result().unwrap_err(), RuntimeFailure::InvalidControlState);
                assert_eq!(result.resource_reports().len(), usize::from(matches!(stage, ClosingStage::Body)));
                assert_eq!(result.unpublished_guards().len(), usize::from(matches!(stage, ClosingStage::Armed)));
                assert_eq!(checked.snapshot().k, if matches!(stage, ClosingStage::Body) { K::Transferred } else { K::Absent });
                assert!(checked.snapshot().terminal);
                if matches!(stage, ClosingStage::Armed) {
                    let guard = &result.unpublished_guards()[0];
                    assert_eq!(guard.native(), ResourceNativeFact::Owned);
                    assert_eq!(guard.point(), crate::eval::GuardInspectionPoint::TerminalBeforeQuarantine);
                    assert_eq!(guard.backing(), crate::eval::GuardBackingObservation::Retained);
                    assert_eq!(guard.status(), None);
                    assert!(!guard.unresolved());
                }
                if matches!(stage, ClosingStage::Body) {
                    assert_eq!(result.resource_reports()[0].closing(), ResourceClosing::Transferred);
                    assert_eq!(result.resource_reports()[0].native(), ResourceNativeFact::Owned);
                    assert_eq!(result.resource_reports()[0].status(), None);
                }
            });
        }
    }

    #[test]
    fn terminal_captured_forest_uses_funded_slots_in_structural_order_when_work_spent() {
        crate::foreign::source_bindings::with_eight_byte_body_pair_for_test(|program, node, pair| {
            let mut machine = Machine::new_effect(program);
            machine.control = None;
            machine.live_resources = 2;
            let mut work = TypeWorkBudget::default();
            let mut reports = crate::eval::checked_reports::ResourceReports::reserve(2, &mut work).unwrap();
            let [(first, first_owner), (second, second_owner)] = pair;
            let first_slot = reports.reserve_owner(&mut work).unwrap();
            let second_slot = reports.reserve_owner(&mut work).unwrap();
            let first_observer = first_slot.observer();
            let second_observer = second_slot.observer();
            let first_native = first.prepaid_scope_observer();
            let second_native = second.prepaid_scope_observer();
            machine.checked_reports = Some(reports);
            let frame = |checked, owner, report_slot, key| super::super::Frame::SourceResourceBoundary(Box::new(SourceResourceBoundary {
                checked: Some(checked), report_slot: Some(report_slot), node,
                key: super::super::ActivationKey(key), environment: super::super::Environment::new(),
                owner: Some(owner), dependencies: Vec::new(), phase: super::super::ProviderPhase::Body,
                payload: Some(Value::Unit), saved: None, consumed: false, blocked: false, discarded: false,
            }));
            machine.frames.push(frame(first, first_owner, first_slot, 111));
            // The clause coordinates are inert in this disposal-only fixture;
            // no handler, resume or admission operation executes them.
            machine.frames.push(super::super::Frame::ClauseBoundary {
                handler: crate::core::HandlerId::new(0), owner: crate::resolved::ResumeId::new(0), registration: None,
                continuation: Some(super::super::CapturedContinuation { frames: vec![frame(second, second_owner, second_slot, 112)] }),
            });
            machine.captured_cells = 1;
            machine.reserve_checked_terminal_spare(1, RuntimePhase::Acquisition).unwrap();
            let capacity = machine.frames.capacity();
            machine.instantiation_work = TypeWorkBudget::with_limit(0);
            machine.quarantine_abandoned_providers().unwrap();
            assert_eq!(machine.frames.capacity(), capacity);
            assert!(machine.frames.is_empty());
            let reports = machine.checked_reports.take().unwrap();
            assert_eq!(reports.record_count(), 2);
            assert_eq!(second_observer.published(), Some(0));
            assert_eq!(first_observer.published(), Some(1));
            assert_eq!(first_native.snapshot().k, K::Transferred);
            assert_eq!(second_native.snapshot().k, K::Transferred);
            assert_eq!(machine.instantiation_work.used(), 0);
            drop(machine);
            let (records, guards) = reports.into_inspections();
            assert_eq!(records.len(), 2);
            assert!(guards.is_empty());
            assert!(records.iter().all(|record| record.closing() == ResourceClosing::Transferred && record.native() == ResourceNativeFact::Owned));
        });
    }
}
