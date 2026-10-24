//! Prepaid fixed v3 outcome encoding. No arbitrary Display/JSON/value cloning.
use super::checked_root_admission::RootRefusal;
use crate::{eval::{CheckedEvaluation, EffectTraceEvent, ResourceDiagnostic, ResourceNativeFact, Value},
    module::ModuleId, types::TypeWorkBudget};
use ash_trusted_preparation::{OutcomeFrameKind as Kind, VerifiedRunning};
const BYTES: usize = 4096;
const TRACE_PREFIX: usize = 64;
const VALUE_STEPS: usize = 64;

pub(super) struct RootReportPlan { scratch: [u8; BYTES] }
impl RootReportPlan {
    pub(super) fn reserve(capacity: usize, modules: usize, work: &mut TypeWorkBudget) -> Result<Self, RootRefusal> {
        // Mandatory records fit fixed64-byte payloads; optional result/trace has
        // a separate fixed prefix allowance. All scans/copies/storage are paid
        // before Machine entry, including bounded module-identity searches.
        // The largest guard payload is42 bytes: encoding+write copies84 bytes
        // plus its24-byte header fit the128-per-record prepaid envelope.
        let cost = capacity.checked_mul(128).and_then(|n| n.checked_add((TRACE_PREFIX + 1) * BYTES * 2))
            .and_then(|n| n.checked_add(modules.checked_mul((VALUE_STEPS + TRACE_PREFIX) * 2)?))
            .and_then(|n| n.checked_add(VALUE_STEPS * 4 + BYTES)).ok_or(RootRefusal::Resource)?;
        work.charge(cost).map_err(|()| RootRefusal::Resource)?;
        Ok(Self { scratch: [0; BYTES] })
    }
    pub(super) fn publish(&mut self, verified: &mut VerifiedRunning, modules: &[ModuleId], outcome: &CheckedEvaluation)
        -> Result<(), RootRefusal> {
        // Mandatory facts precede optional source/result/Trace encoding. Never
        // turn an unrepresentable A/E or output failure into a second native call.
        for (index, record) in outcome.resource_reports().iter().enumerate() {
            let mut p = Payload::new(&mut self.scratch);
            p.u32(index as u32)?;
            p.byte(match record.closing() { crate::eval::ResourceClosing::NativeConsumed=>0,
                crate::eval::ResourceClosing::NativeRetained=>1, crate::eval::ResourceClosing::SessionLost=>2,
                crate::eval::ResourceClosing::DependencyBlocked=>3, crate::eval::ResourceClosing::Quarantined=>4,
                crate::eval::ResourceClosing::Transferred=>5 })?;
            p.native(record.native())?; p.byte(u8::from(record.unresolved()))?;
            p.status(record.status())?;
            p.byte(match record.diagnostic() { ResourceDiagnostic::NotRequested=>0, ResourceDiagnostic::AllowanceRefused=>1,
                ResourceDiagnostic::NativeAbsent=>2, ResourceDiagnostic::ScanBoundExceeded=>3,
                ResourceDiagnostic::InvalidEncoding=>4, ResourceDiagnostic::Lost=>5, ResourceDiagnostic::Text(_)=>6 })?;
            // Text class is retained, but no optional diagnostic bytes are
            // silently claimed to have crossed this fixed-record wire format.
            p.byte(0)?;
            verified.write_outcome_frame(Kind::ScopeClosing, p.bytes()).map_err(RootRefusal::Output)?;
        }
        for (index, record) in outcome.unpublished_guards().iter().enumerate() {
            let mut p = Payload::new(&mut self.scratch); p.u32(index as u32)?;
            p.native(record.native())?; p.byte(u8::from(record.unresolved()))?; p.status(record.status())?;
            p.status(record.acquisition_status())?;
            p.byte(match record.backing() { crate::eval::GuardBackingObservation::Retained=>0, crate::eval::GuardBackingObservation::Unknown=>1 })?;
            p.byte(match record.point() { crate::eval::GuardInspectionPoint::AfterUnpublishedDisposal=>0,
                crate::eval::GuardInspectionPoint::TerminalBeforeQuarantine=>1, crate::eval::GuardInspectionPoint::ReturnFailureAfterDisposal=>2 })?;
            verified.write_outcome_frame(Kind::UnpublishedGuard, p.bytes()).map_err(RootRefusal::Output)?;
        }
        verified.finish_outcome_closings().map_err(RootRefusal::Output)?;
        let traces = outcome.effect_trace();
        let trace_complete = traces.is_some_and(|trace| trace.len() <= TRACE_PREFIX);
        let mut p = Payload::new(&mut self.scratch);
        let mut represented = true;
        match outcome.result() {
            Err(error) => { p.byte(0)?; p.byte(u8::from(trace_complete))?; p.failure(error)?; }
            Ok(evaluation) => {
                p.byte(1)?; p.byte(u8::from(trace_complete))?;
                if p.value(&evaluation.value, modules).is_err() {
                    represented = false;
                    p.used = 0; p.byte(2)?; p.byte(u8::from(trace_complete))?;
                }
            }
        }
        let optional = verified.write_outcome_frame(Kind::Result, p.bytes());
        // Once IO poisons the authenticated writer, a terminal write refuses;
        // quota refusal leaves its reserved terminal slot intact.
        if optional.is_ok() {
            if let Some(trace) = traces {
                for (index, event) in trace.iter().take(TRACE_PREFIX).enumerate() {
                    let mut p = Payload::new(&mut self.scratch); p.u32(index as u32)?;
                    if p.trace(*event, modules).is_err() { represented = false; break; }
                    if verified.write_outcome_frame(Kind::Trace, p.bytes()).is_err() { represented = false; break; }
                }
            }
        }
        verified.write_outcome_frame(Kind::Terminal, &[]).map_err(RootRefusal::Output)?;
        optional.map_err(RootRefusal::Output)?;
        if !represented || !trace_complete { return Err(RootRefusal::Association); }
        outcome.result().map(|_| ()).map_err(RootRefusal::Runtime)
    }
}
struct Payload<'a> { bytes: &'a mut [u8; BYTES], used: usize }
impl<'a> Payload<'a> {
    fn new(bytes: &'a mut [u8; BYTES]) -> Self { Self { bytes, used: 0 } }
    fn bytes(&self) -> &[u8] { &self.bytes[..self.used] }
    fn raw(&mut self, bytes: &[u8]) -> Result<(), RootRefusal> {
        let end = self.used.checked_add(bytes.len()).filter(|n| *n <= BYTES).ok_or(RootRefusal::Resource)?;
        self.bytes[self.used..end].copy_from_slice(bytes); self.used = end; Ok(())
    }
    fn byte(&mut self, byte: u8) -> Result<(), RootRefusal> { self.raw(&[byte]) }
    fn u32(&mut self, value: u32) -> Result<(), RootRefusal> { self.raw(&value.to_le_bytes()) }
    fn blob(&mut self, bytes: &[u8]) -> Result<(), RootRefusal> {
        self.u32(u32::try_from(bytes.len()).map_err(|_| RootRefusal::Resource)?)?; self.raw(bytes)
    }
    fn failure(&mut self, error: crate::eval::RuntimeFailure) -> Result<(), RootRefusal> {
        self.blob(error.reason_code().as_bytes())?;
        if let crate::eval::RuntimeFailure::Report(report) = error {
            self.byte(1)?;
            self.resource(report.primary.resource())?;
            self.resource(report.teardown)?;
            self.blob(report.cleanup.label().as_bytes())
        } else { self.byte(0) }
    }
    fn resource(&mut self, value: Option<crate::eval::ResourceFailure>) -> Result<(), RootRefusal> {
        self.byte(u8::from(value.is_some()))?;
        if let Some(value) = value {
            self.blob(value.cause.reason_code().as_bytes())?;
            self.blob(value.phase.label().as_bytes())?;
            self.blob(value.resource.label().as_bytes())?;
            for count in [value.requested, value.available] {
                self.byte(u8::from(count.is_some()))?;
                self.raw(&u64::try_from(count.unwrap_or(0)).map_err(|_|RootRefusal::Resource)?.to_le_bytes())?;
            }
        }
        Ok(())
    }
    fn native(&mut self, fact: ResourceNativeFact) -> Result<(), RootRefusal> {
        self.byte(match fact { ResourceNativeFact::NoOwner=>0, ResourceNativeFact::Owned=>1,
            ResourceNativeFact::Consumed=>2, ResourceNativeFact::Unknown=>3 })
    }
    fn status(&mut self, value: Option<i128>) -> Result<(), RootRefusal> {
        self.byte(u8::from(value.is_some()))?; self.raw(&value.unwrap_or(0).to_le_bytes())
    }
    fn module(&mut self, module: ModuleId, modules: &[ModuleId]) -> Result<(), RootRefusal> {
        self.u32(u32::try_from(modules.iter().position(|m| *m == module).ok_or(RootRefusal::Association)?)
            .map_err(|_| RootRefusal::Resource)?)
    }
    fn operation(&mut self, op: crate::types::OperationId, modules: &[ModuleId]) -> Result<(), RootRefusal> {
        self.module(op.owner().module(), modules)?; self.u32(op.owner().declaration())?; self.u32(op.operation())
    }
    fn trace(&mut self, event: EffectTraceEvent, modules: &[ModuleId]) -> Result<(), RootRefusal> {
        match event {
            EffectTraceEvent::ResourceAcquired(n)=>{self.byte(0)?;self.u32(n)},
            EffectTraceEvent::ResourceRead(n)=>{self.byte(1)?;self.u32(n)},
            EffectTraceEvent::ResourceWritten(n)=>{self.byte(2)?;self.u32(n)},
            EffectTraceEvent::ResourceReleased(n)=>{self.byte(3)?;self.u32(n)},
            EffectTraceEvent::HandlerActivated(n)=>{self.byte(4)?;self.u32(n.value())},
            EffectTraceEvent::Request(op)=>{self.byte(5)?;self.operation(op,modules)},
            EffectTraceEvent::HandlerSelected(n)=>{self.byte(6)?;self.u32(n.value())},
            EffectTraceEvent::ClauseEntered(n,op)=>{self.byte(7)?;self.u32(n.value())?;self.operation(op,modules)},
            EffectTraceEvent::Resume(n)=>{self.byte(8)?;self.u32(n.value())},
            EffectTraceEvent::Discard(n)=>{self.byte(9)?;self.u32(n.value())},
            EffectTraceEvent::HandlerRestored(n)=>{self.byte(10)?;self.u32(n.value())},
            EffectTraceEvent::ClauseReturned(n)=>{self.byte(11)?;self.u32(n.value())},
        }
    }
    fn value(&mut self, value: &Value, modules: &[ModuleId]) -> Result<(), RootRefusal> {
        use crate::eval::{HeapCell, ObservedHeap};
        #[derive(Clone, Copy)]
        enum Task<'v> { Value(&'v Value, Option<&'v ObservedHeap>), Cell(&'v ObservedHeap, usize) }
        let mut stack = [None; VALUE_STEPS]; let mut length = 1; let mut steps = 0;
        stack[0] = Some(Task::Value(value,None));
        while length != 0 {
            steps += 1; if steps > VALUE_STEPS { return Err(RootRefusal::Resource); }
            length -= 1;
            let task = stack[length].take().ok_or(RootRefusal::Association)?;
            let mut push = |task| { if length == stack.len() { return Err(RootRefusal::Resource); }
                stack[length] = Some(task); length += 1; Ok(()) };
            match task {
                Task::Value(value,heap) => match value {
                    Value::Integer(integer)=>{
                        // This fixed scratch/traversal envelope was paid before
                        // entry. Check the whole magnitude before any copy; no
                        // narrowing, decimal formatting or BigInt clone.
                        let used = super::checked_integer_result::encode(integer, &mut self.bytes[self.used..BYTES])
                            .ok_or(RootRefusal::Resource)?;
                        self.used += used;
                    },
                    Value::Unit=>self.byte(0)?, Value::Boolean(v)=>{self.byte(1)?;self.byte(u8::from(*v))?;},
                    Value::Bytes(b)=>{self.byte(2)?;self.blob(b)?;}, Value::BytePrefix(b)=>{self.byte(2)?;self.blob(b.as_bytes())?;},
                    Value::String(s)=>{self.byte(3)?;self.blob(s.as_bytes())?;},
                    Value::Data(data)=>{let (heap,location)=data.root_parts();push(Task::Cell(heap,location))?;},
                    Value::Location(location)=>push(Task::Cell(heap.ok_or(RootRefusal::Association)?,*location))?,
                    _=>return Err(RootRefusal::Association),
                },
                Task::Cell(heap,location)=>match heap.cell(location).ok_or(RootRefusal::Association)? {
                    HeapCell::Uninitialized=>return Err(RootRefusal::Association),
                    HeapCell::Alias(target)=>push(Task::Cell(heap,*target))?,
                    HeapCell::Tuple(fields)=>{self.byte(4)?;self.u32(u32::try_from(fields.len()).map_err(|_|RootRefusal::Resource)?)?;
                        for field in fields.iter().rev() { push(Task::Value(field,Some(heap)))?; }},
                    HeapCell::Constructor(id,payload)=>{self.byte(5)?;self.module(id.owner().module(),modules)?;
                        self.byte(u8::from(id.owner().is_lexical()))?;self.u32(id.owner().declaration())?;self.u32(id.constructor())?;
                        self.byte(u8::from(payload.is_some()))?;if let Some(v)=payload {push(Task::Value(v,Some(heap)))?;}},
                },
            }
        }
        Ok(())
    }
}


#[cfg(test)]
mod output_status_tests {
    use super::*;
    #[test]
    fn integer_result_keeps_sign_magnitude_and_scratch_boundary() {
        let integer = crate::integer::Integer::parse_decimal(&"9".repeat(3000)).unwrap();
        let negative = &integer * &crate::integer::Integer::from_i64(-1);
        let mut scratch = [0; BYTES];
        let mut p = Payload::new(&mut scratch);
        p.value(&Value::Integer(negative), &[]).unwrap();
        assert_eq!(p.bytes()[0..2], [6, 1]);
        let count = u32::from_le_bytes(p.bytes()[2..6].try_into().unwrap()) as usize;
        assert_eq!(count as u64, integer.magnitude_byte_length());
        assert_eq!(p.bytes().len(), count + 6);
        let size = p.used;
        let mut short = Payload::new(&mut scratch); short.used = BYTES - size + 1;
        let before = short.used;
        assert!(short.value(&Value::Integer(integer), &[]).is_err());
        assert_eq!(short.used, before, "whole integer bound is checked before encoding");
    }
}
