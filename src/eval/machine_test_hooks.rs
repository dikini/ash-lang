//! Test-only generic machine storage/refusal observations.
use std::cell::Cell;

type TransformerEvaluationObserver =
    fn(&crate::core::validate::ValidatedMacroEntry, &super::Evaluation);
type IdentifierCaptureObserver = fn(usize, &mut super::Value);
type AdvanceCallableObserver = fn(&crate::source::Origin);
#[derive(Clone, Copy, Debug)]
pub(crate) struct AdvanceCaptureObservation {
    pub selected: usize,
    pub depth: usize,
    pub first_direct_guard: Option<usize>,
    pub live_guards: usize,
    pub captured_guards: usize,
    pub handler_effect: Option<crate::types::EffectId>,
    pub operation: crate::types::OperationId,
    pub canonical_default: bool,
}
type CaptureRangeObserver = fn(AdvanceCaptureObservation);
type AdvanceTraceObserver = fn(&'static str, usize, usize, usize);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum AdvanceCutPoint {
    Install,
    CompletionLookup,
    ApplicationLookup,
    FramePayment,
    GuardCreation,
    ReferenceCreation,
    ReferenceVerification,
    OriginProjection,
    GuardReturn,
}

pub(crate) const ADVANCE_INSTALLED: u32 = 1;
pub(crate) const ADVANCE_LOOKED_UP: u32 = 2;
pub(crate) const ADVANCE_FRAME_PAID: u32 = 4;
pub(crate) const ADVANCE_GUARD_CREATED: u32 = 8;
pub(crate) const ADVANCE_ORIGIN_PUBLISHED: u32 = 16;
pub(crate) const ADVANCE_GUARD_VERIFIED: u32 = 32;
pub(crate) const ADVANCE_TRANSFER_REACHED: u32 = 64;
pub(crate) const ADVANCE_APPLICATION_LOOKED_UP: u32 = 128;
pub(crate) const ADVANCE_REFERENCE_CREATED: u32 = 256;
pub(crate) const ADVANCE_REFERENCE_VERIFIED: u32 = 512;

std::thread_local! {
    pub(crate) static TRANSFORMER_EVALUATION_OBSERVER: Cell<Option<TransformerEvaluationObserver>> = const { Cell::new(None) };
    pub(crate) static IDENTIFIER_CAPTURE_OBSERVER: Cell<Option<IdentifierCaptureObserver>> = const { Cell::new(None) };
    pub(crate) static ADVANCE_CALLABLE_OBSERVER: Cell<Option<AdvanceCallableObserver>> = const { Cell::new(None) };
    pub(crate) static CAPTURE_RANGE_OBSERVER: Cell<Option<CaptureRangeObserver>> = const { Cell::new(None) };
    pub(crate) static ADVANCE_TRACE_OBSERVER: Cell<Option<AdvanceTraceObserver>> = const { Cell::new(None) };
    pub(crate) static ADVANCE_CUT: Cell<Option<(AdvanceCutPoint, usize)>> = const { Cell::new(None) };
    pub(crate) static ADVANCE_CUT_BEFORE: Cell<Option<usize>> = const { Cell::new(None) };
    pub(crate) static ADVANCE_STAGES: Cell<u32> = const { Cell::new(0) };
    pub(crate) static FAIL_ADVANCE_ARC: Cell<bool> = const { Cell::new(false) };
    pub(crate) static FAIL_ADVANCE_BOX: Cell<bool> = const { Cell::new(false) };
    pub(crate) static FAIL_ADVANCE_TRANSFER: Cell<bool> = const { Cell::new(false) };
    pub(crate) static ADVANCE_GUARD_DROPS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static FAIL_DISPOSAL_GROWTH: Cell<bool> = const { Cell::new(false) };
    pub(crate) static FAIL_CONTROL_RESERVATION: Cell<Option<crate::eval::ResourceFailureCause>> = const { Cell::new(None) };
    pub(crate) static ROOT_CLOSES: Cell<usize> = const { Cell::new(0) };
    pub(crate) static FAIL_ROOT_CLOSE: Cell<bool> = const { Cell::new(false) };
    pub(crate) static TRANSFORMER_DROPS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static ACTIVE_ROOT_DROPS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static ACTIVE_ROOT_RECORDS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static SYNTAX_REQUESTS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static QUOTE_REACHES: Cell<usize> = const { Cell::new(0) };
    pub(crate) static QUOTE_COMPLETIONS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static FIRST_QUOTE_COMPLETION_WORK: Cell<Option<usize>> = const { Cell::new(None) };
    pub(crate) static TRANSFER_ATTEMPTS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static TRANSFER_FAILURES: Cell<usize> = const { Cell::new(0) };
    pub(crate) static TRANSFER_GROUPS_COMPLETED: Cell<usize> = const { Cell::new(0) };
    pub(crate) static DECLARATION_CAPTURES: Cell<usize> = const { Cell::new(0) };
    pub(crate) static DECLARATION_UNWRAPS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static DECLARATION_TRANSFERS_BEFORE_DROP: Cell<usize> = const { Cell::new(0) };
    pub(crate) static SCALAR_LEX_STARTS: Cell<usize> = const { Cell::new(0) };
    pub(crate) static SCALAR_UTF8_SCANS: Cell<usize> = const { Cell::new(0) };
}

pub(crate) fn reset() {
    TRANSFORMER_EVALUATION_OBSERVER.set(None);
    IDENTIFIER_CAPTURE_OBSERVER.set(None);
    ADVANCE_CALLABLE_OBSERVER.set(None);
    CAPTURE_RANGE_OBSERVER.set(None);
    ADVANCE_TRACE_OBSERVER.set(None);
    ADVANCE_CUT.set(None);
    ADVANCE_CUT_BEFORE.set(None);
    ADVANCE_STAGES.set(0);
    FAIL_ADVANCE_ARC.set(false);
    FAIL_ADVANCE_BOX.set(false);
    FAIL_ADVANCE_TRANSFER.set(false);
    ADVANCE_GUARD_DROPS.set(0);
    FAIL_DISPOSAL_GROWTH.set(false);
    FAIL_CONTROL_RESERVATION.set(None);
    ROOT_CLOSES.set(0);
    FAIL_ROOT_CLOSE.set(false);
    TRANSFORMER_DROPS.set(0);
    ACTIVE_ROOT_DROPS.set(0);
    ACTIVE_ROOT_RECORDS.set(0);
    SYNTAX_REQUESTS.set(0);
    QUOTE_REACHES.set(0);
    QUOTE_COMPLETIONS.set(0);
    FIRST_QUOTE_COMPLETION_WORK.set(None);
    TRANSFER_ATTEMPTS.set(0);
    TRANSFER_FAILURES.set(0);
    TRANSFER_GROUPS_COMPLETED.set(0);
    DECLARATION_CAPTURES.set(0);
    DECLARATION_UNWRAPS.set(0);
    DECLARATION_TRANSFERS_BEFORE_DROP.set(0);
    SCALAR_LEX_STARTS.set(0);
    SCALAR_UTF8_SCANS.set(0);
}
