//! Complete bounded byte replies admitted before a read or mutation.

use super::{HeapCell, Location, RuntimeFailure, RuntimePhase, Value};
use crate::{
    foreign::{
        source_contract::PreparedScalarRepresentation,
        source_runtime::{
            NativeByteAccess, NativeScalarConversionError, NativeScalarValue, narrow_gnu_scalar,
        },
    },
    integer::Integer,
    types::{ConstructorId, TypeWorkBudget},
};

#[derive(Debug, Eq, PartialEq)]
pub(super) enum ByteOperands {
    Read(usize),
    Write(usize, u8),
}

/// The original guard supplies extent; private payload data never participates.
/// A failed index must not inspect or pay for the already evaluated byte value.
pub(super) fn prepare_byte_operands(
    index: &Integer,
    byte: Option<&Integer>,
    extent: usize,
    work: &mut TypeWorkBudget,
) -> Result<ByteOperands, NativeScalarConversionError> {
    let NativeScalarValue::USize(index) =
        narrow_gnu_scalar(index, PreparedScalarRepresentation::SizeT, work)?
    else {
        return Err(NativeScalarConversionError::InvalidRepresentation);
    };
    if index >= extent {
        return Err(NativeScalarConversionError::OutOfRange);
    }
    if let Some(byte) = byte {
        prepare_byte_write_value(index, byte, work)
    } else {
        Ok(ByteOperands::Read(index))
    }
}

fn prepare_byte_write_value(
    index: usize,
    byte: &Integer,
    work: &mut TypeWorkBudget,
) -> Result<ByteOperands, NativeScalarConversionError> {
    let NativeScalarValue::U8(byte) =
        narrow_gnu_scalar(byte, PreparedScalarRepresentation::Unsigned(8), work)?
    else {
        return Err(NativeScalarConversionError::InvalidRepresentation);
    };
    Ok(ByteOperands::Write(index, byte))
}

/// Exclusive access to an initialized, unpublished report cell. The caller has
/// authenticated the canonical call, complete instance and live original guard.
/// Neither callback can charge work or grow the heap through this receipt.
pub(super) struct ByteReplyReady<'heap> {
    cell: &'heap mut HeapCell,
    location: Location,
}

fn reserve_report_cells(heap: &mut Vec<HeapCell>, requested: usize) -> Result<(), RuntimeFailure> {
    let failure = || {
        super::resource_failure(
            super::ResourceFailureCause::StorageReservationFailed,
            RuntimePhase::Access,
            super::RuntimeResource::ResultHeapCells,
            Some(requested),
            None,
        )
    };
    #[cfg(test)]
    if report_reservation_fault::reject() {
        return Err(failure());
    }
    heap.try_reserve(requested).map_err(|_| failure())
}

// This test-only witness refuses the same staging boundary as a failed Vec
// reservation. It never forces an allocator failure or changes release policy.
#[cfg(test)]
pub(super) mod report_reservation_fault {
    use std::cell::Cell;

    thread_local! {
        static REFUSE_NEXT: Cell<bool> = const { Cell::new(false) };
        static HITS: Cell<usize> = const { Cell::new(0) };
    }

    pub(in crate::eval::machine) struct Fault;

    pub(in crate::eval::machine) fn fail_next() -> Fault {
        assert!(
            !REFUSE_NEXT.replace(true),
            "reservation witness already armed"
        );
        HITS.set(0);
        Fault
    }

    pub(in crate::eval::machine) fn hits() -> usize {
        HITS.get()
    }

    pub(super) fn reject() -> bool {
        if REFUSE_NEXT.replace(false) {
            HITS.set(HITS.get() + 1);
            true
        } else {
            false
        }
    }

    impl Drop for Fault {
        fn drop(&mut self) {
            REFUSE_NEXT.set(false);
        }
    }
}

impl<'heap> ByteReplyReady<'heap> {
    pub(super) fn admit(
        heap: &'heap mut Vec<HeapCell>,
        work: &mut TypeWorkBudget,
        returned: ConstructorId,
        read: bool,
    ) -> Result<Self, RuntimeFailure> {
        // Callback/recording, the constructor cell, and bounded one-digit
        // numeric reply work (reads only) are paid before native access.
        super::charge_effect_work(work, 2 + usize::from(read), RuntimePhase::Access)?;
        heap.len()
            .checked_add(1)
            .ok_or(RuntimeFailure::HeapCapacity)?;
        reserve_report_cells(heap, 1)?;
        let location = heap.len();
        heap.push(HeapCell::Constructor(returned, Some(Value::Unit)));
        Ok(Self {
            cell: &mut heap[location],
            location,
        })
    }

    pub(super) fn refusal(
        heap: &mut Vec<HeapCell>,
        work: &mut TypeWorkBudget,
        failed: ConstructorId,
        error: ConstructorId,
    ) -> Result<Value, RuntimeFailure> {
        super::charge_effect_work(work, 2, RuntimePhase::Access)?;
        heap.len()
            .checked_add(2)
            .ok_or(RuntimeFailure::HeapCapacity)?;
        reserve_report_cells(heap, 2)?;
        let error_location = heap.len();
        heap.push(HeapCell::Constructor(error, None));
        let location = heap.len();
        heap.push(HeapCell::Constructor(
            failed,
            Some(Value::Location(error_location)),
        ));
        Ok(Value::Location(location))
    }

    pub(super) fn read(self, access: NativeByteAccess<'_>) -> Value {
        let byte = access.read();
        // num-bigint 0.5.1 stores every u8 in its inline digit. This conversion
        // allocates nothing and has no refusal; report storage is already live.
        let HeapCell::Constructor(_, payload) = self.cell else {
            unreachable!("readiness exclusively owns its initialized report cell")
        };
        *payload = Some(Value::Integer(Integer::from_u64(u64::from(byte))));
        Value::Location(self.location)
    }

    pub(super) fn write(self, access: NativeByteAccess<'_>, byte: u8) -> Value {
        access.write(byte);
        Value::Location(self.location)
    }
}

impl super::Machine<'_> {
    pub(super) fn return_source_byte_call(
        &mut self,
        apply: super::NodeId,
        callable: super::SourceByteCallable,
        caller: super::Instantiation,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        use crate::{
            core::{EffectExprKind, EffectOperation, PureComputation, PureExprKind},
            foreign::scalar_preflight::ForeignScalarPreflightRole,
            types::{IterativeTypeOwner, Type},
        };
        let (function, role) = match callable.intrinsic.operation() {
            crate::core::packed::Intrinsic::ForeignByteRead { function } => {
                (function, ForeignScalarPreflightRole::ByteRead)
            }
            crate::core::packed::Intrinsic::ForeignByteWrite { function } => {
                (function, ForeignScalarPreflightRole::ByteWrite)
            }
            _ => return Err(RuntimeFailure::ForeignBinding),
        };
        let program = self.program.clone();
        let fact = program
            .registry()
            .scalar_preflight(function)
            .ok_or(RuntimeFailure::ForeignBinding)?;
        if fact.role() != role || fact.module() != callable.intrinsic.module() {
            return Err(RuntimeFailure::ForeignBinding);
        }
        let parameter = role
            .byte_parameter(fact.module())
            .ok_or(RuntimeFailure::ForeignBinding)?;
        let ids = fact.call_codec().ids();
        let error = fact
            .conversion_error_constructor()
            .ok_or(RuntimeFailure::ForeignBinding)?;
        let write = role == ForeignScalarPreflightRole::ByteWrite;
        let Value::Location(location) = value else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let location =
            super::resolve_location_with_work(&self.heap, location, &mut self.instantiation_work)?;
        let Some(HeapCell::Tuple(fields)) = self.heap.get(location) else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        super::charge_effect_work(
            &mut self.instantiation_work,
            fields.len(),
            RuntimePhase::Access,
        )?;
        if fields.len() != 2 + usize::from(write) {
            return Err(RuntimeFailure::ForeignBinding);
        }
        let Value::NativeStateView(key) = fields[0] else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let mut selected = None;
        for (index, frame) in self.frames.iter().enumerate().rev() {
            super::charge_effect_work(&mut self.instantiation_work, 1, RuntimePhase::Access)?;
            let super::Frame::SourceResourceBoundary(boundary) = frame else {
                continue;
            };
            if boundary.key != key {
                continue;
            }
            if selected.is_some() || boundary.consumed || boundary.owner.is_none() {
                return Err(RuntimeFailure::ForeignBinding);
            }
            let Some(super::ExecutableNode::Effect(stored)) = program.node(boundary.node) else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) =
                &stored.kind
            else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let owner = boundary
                .owner
                .as_ref()
                .ok_or(RuntimeFailure::ForeignBinding)?;
            if !std::sync::Arc::ptr_eq(owner.owner(), &scope.header().owner)
                || owner.initialized_bytes().is_none()
                || !scope
                    .contains_byte_call(
                        match boundary.phase {
                            super::ProviderPhase::Acquire => {
                                crate::core::source_resource::SourceResourcePhase::Acquire
                            }
                            super::ProviderPhase::Body => {
                                crate::core::source_resource::SourceResourcePhase::Handler
                            }
                            super::ProviderPhase::Finish => {
                                crate::core::source_resource::SourceResourcePhase::Finish
                            }
                        },
                        apply,
                        callable.application,
                        function,
                        &mut self.instantiation_work,
                    )
                    .map_err(|failure| {
                        if failure.reason() == crate::core::ValidationReason::Resource {
                            super::effect_work_failure(
                                &self.instantiation_work,
                                None,
                                RuntimePhase::Access,
                            )
                        } else {
                            RuntimeFailure::ForeignBinding
                        }
                    })?
            {
                return Err(RuntimeFailure::ForeignBinding);
            }
            // Every ordered Type/Row argument is retained independently of S.
            // The selected alternative's defining caller cannot be replaced by
            // the current Apply's merely compatible State value type.
            for argument in scope.arguments() {
                let expected = boundary
                    .environment
                    .instantiation
                    .argument(argument, &mut self.instantiation_work)?;
                for actual_context in [&callable.caller, &caller] {
                    let actual = actual_context.argument(argument, &mut self.instantiation_work)?;
                    if !crate::types::same_kinded_argument_with_budget(
                        &expected,
                        &actual,
                        &mut self.instantiation_work,
                    )
                    .map_err(|()| {
                        super::effect_work_failure(
                            &self.instantiation_work,
                            None,
                            RuntimePhase::Access,
                        )
                    })? {
                        return Err(RuntimeFailure::ForeignBinding);
                    }
                }
            }
            let PureExprKind::Computation(PureComputation::TypeApplication(application)) =
                super::pure_expression(&program, callable.application)?
            else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            if application.arguments().len() != 1 || !application.row_arguments().is_empty() {
                return Err(RuntimeFailure::ForeignBinding);
            }
            let Type::Tuple(state_data) = scope.finish.parameter.ty() else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let original_state = IterativeTypeOwner::new(boundary.environment.instantiation.ty(
                state_data.first().ok_or(RuntimeFailure::ForeignBinding)?,
                &mut self.instantiation_work,
            )?);
            let PureExprKind::Computation(PureComputation::Apply(call)) =
                super::pure_expression(&program, apply)?
            else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let operand_type = match program
                .node(call.argument())
                .ok_or(RuntimeFailure::ForeignBinding)?
            {
                super::ExecutableNode::Pure(node) => &node.ty,
                super::ExecutableNode::Effect(node) => &node.ty,
            };
            let Type::Tuple(operand_fields) = operand_type else {
                return Err(RuntimeFailure::ForeignBinding);
            };
            let operand_state = IterativeTypeOwner::new(
                caller.ty(&operand_fields[0], &mut self.instantiation_work)?,
            );
            let applied_state = IterativeTypeOwner::new(
                callable
                    .caller
                    .ty(&application.arguments()[0], &mut self.instantiation_work)?,
            );
            let defining_state = IterativeTypeOwner::new(
                callable
                    .defining
                    .ty(&Type::Variable(parameter), &mut self.instantiation_work)?,
            );
            // Full copying authority was checked independently. Original header
            // formals can differ from caller formals, so use the copied operand
            // as the executable State coordinate and compare all carrier views.
            for state in [&original_state, &applied_state, &defining_state] {
                if !crate::types::same_type_with_budget(
                    &operand_state,
                    state,
                    &mut self.instantiation_work,
                )
                .map_err(|()| {
                    super::effect_work_failure(&self.instantiation_work, None, RuntimePhase::Access)
                })? {
                    return Err(RuntimeFailure::ForeignBinding);
                }
            }
            selected = Some(index);
        }
        let selected = selected.ok_or(RuntimeFailure::ForeignBinding)?;
        // Dispose owned specialization metadata before admission and native
        // access. The infallible callback finish retains only scalar receipts,
        // the already initialized report cell, and a borrowed unique guard.
        drop(callable);
        drop(caller);
        let super::Frame::SourceResourceBoundary(boundary) = &self.frames[selected] else {
            return Err(RuntimeFailure::ForeignBinding);
        };
        let owner = boundary
            .owner
            .as_ref()
            .ok_or(RuntimeFailure::ForeignBinding)?;
        let extent = owner
            .initialized_bytes()
            .ok_or(RuntimeFailure::ForeignBinding)?;
        let tuple = Value::Location(location);
        let index = super::source_scalar_phases::source_integer_leaf(
            &self.heap,
            &tuple,
            &[1],
            &mut self.instantiation_work,
        )?;
        // Admit and refuse the index before inspecting the byte leaf or
        // charging its conversion. Both Ash arguments are already evaluated.
        let operands =
            match prepare_byte_operands(index, None, extent, &mut self.instantiation_work) {
                Ok(ByteOperands::Read(index)) if write => {
                    let byte = super::source_scalar_phases::source_integer_leaf(
                        &self.heap,
                        &tuple,
                        &[2],
                        &mut self.instantiation_work,
                    )?;
                    prepare_byte_write_value(index, byte, &mut self.instantiation_work)
                }
                other => other,
            };
        let operands = match operands {
            Ok(operands) => operands,
            Err(NativeScalarConversionError::OutOfRange) => {
                let result = ByteReplyReady::refusal(
                    &mut self.heap,
                    &mut self.instantiation_work,
                    ids.conversion_failed,
                    error,
                )?;
                self.control = Some(super::Control::Return(result));
                return Ok(());
            }
            Err(NativeScalarConversionError::WorkExhausted) => {
                return Err(super::effect_work_failure(
                    &self.instantiation_work,
                    None,
                    RuntimePhase::Access,
                ));
            }
            Err(_) => return Err(RuntimeFailure::ForeignBinding),
        };
        let index = match operands {
            ByteOperands::Read(index) | ByteOperands::Write(index, _) => index,
        };
        let access = if boundary.phase == super::ProviderPhase::Finish {
            owner.completion_byte_access(index)
        } else {
            owner.byte_access(index)
        }
        .ok_or(RuntimeFailure::ForeignBinding)?;
        let ready = ByteReplyReady::admit(
            &mut self.heap,
            &mut self.instantiation_work,
            ids.returned,
            !write,
        )?;
        let result = match operands {
            ByteOperands::Read(_) => ready.read(access),
            ByteOperands::Write(_, byte) => ready.write(access, byte),
        };
        self.control = Some(super::Control::Return(result));
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn invalid_index_refuses_without_admitting_byte_conversion_work() {
        let invalid_index = Integer::from_u64(7);
        let invalid_byte =
            Integer::parse_decimal("18446744073709551616000000000000000000").unwrap();
        // Four units admit index conversion plus its complete refusal report,
        // but cannot admit the large byte's conversion. OutOfRange followed by
        // that report distinguishes bounds-first refusal from simultaneous bad
        // values. A valid index with the same byte/ledger instead exhausts work.
        let mut exact = TypeWorkBudget::with_limit(4);
        assert_eq!(
            prepare_byte_operands(&invalid_index, Some(&invalid_byte), 7, &mut exact),
            Err(NativeScalarConversionError::OutOfRange)
        );
        assert_eq!(exact.used(), 2);
        let module = crate::module::ModuleId::new(1);
        let failed = ConstructorId::new(crate::types::NominalTypeId::new(module, 1), 1);
        let error = ConstructorId::new(crate::types::NominalTypeId::new(module, 0), 0);
        let mut heap = Vec::new();
        let Value::Location(report) =
            ByteReplyReady::refusal(&mut heap, &mut exact, failed, error).unwrap()
        else {
            panic!("prepared conversion refusal")
        };
        assert_eq!(exact.remaining(), 0);
        assert!(
            matches!(&heap[report], HeapCell::Constructor(found, Some(Value::Location(payload))) if *found == failed && matches!(&heap[*payload], HeapCell::Constructor(found, None) if *found == error))
        );
        let mut byte_short = TypeWorkBudget::with_limit(4);
        assert_eq!(
            prepare_byte_operands(
                &Integer::from_u64(0),
                Some(&invalid_byte),
                7,
                &mut byte_short
            ),
            Err(NativeScalarConversionError::WorkExhausted)
        );
        assert_eq!(byte_short.used(), 3);
        let mut index_short = TypeWorkBudget::with_limit(1);
        assert_eq!(
            prepare_byte_operands(&invalid_index, Some(&invalid_byte), 7, &mut index_short),
            Err(NativeScalarConversionError::WorkExhausted)
        );
        assert_eq!(index_short.used(), 1);
        for _ in 0..2 {
            let mut work = TypeWorkBudget::with_limit(4);
            assert_eq!(
                prepare_byte_operands(
                    &Integer::from_u64(0),
                    Some(&Integer::from_u64(255)),
                    1,
                    &mut work
                ),
                Ok(ByteOperands::Write(0, 255))
            );
            assert_eq!(work.remaining(), 0);
        }
        let mut work = TypeWorkBudget::default();
        assert_eq!(
            prepare_byte_operands(&Integer::from_u64(0), None, 0, &mut work),
            Err(NativeScalarConversionError::OutOfRange)
        );
        assert_eq!(
            prepare_byte_operands(&Integer::from_i64(-1), None, 7, &mut work),
            Err(NativeScalarConversionError::OutOfRange)
        );
        assert_eq!(
            prepare_byte_operands(
                &Integer::from_u64(0),
                Some(&Integer::from_u64(256)),
                1,
                &mut work
            ),
            Err(NativeScalarConversionError::OutOfRange)
        );
    }

    #[test]
    fn byte_reply_exact_work_and_one_short_preserve_heap_before_callback() {
        let returned = ConstructorId::new(
            crate::types::NominalTypeId::new(crate::module::ModuleId::new(1), 1),
            0,
        );
        for read in [false, true] {
            let exact = 2 + usize::from(read);
            let mut heap = Vec::new();
            let mut short = TypeWorkBudget::with_limit(exact - 1);
            assert!(ByteReplyReady::admit(&mut heap, &mut short, returned, read).is_err());
            assert_eq!(short.used(), 0, "the complete report charge is atomic");
            assert!(heap.is_empty());
            for _ in 0..2 {
                let mut work = TypeWorkBudget::with_limit(exact);
                let before = heap.len();
                let ready = ByteReplyReady::admit(&mut heap, &mut work, returned, read).unwrap();
                assert_eq!(ready.location, before);
                assert!(
                    matches!(ready.cell, HeapCell::Constructor(found, Some(Value::Unit)) if *found == returned)
                );
                assert_eq!(work.used(), exact);
                assert_eq!(work.charge(1), Err(()));
            }
        }
    }

    #[test]
    fn byte_refusal_storage_failure_preserves_heap_and_retries_at_exact_work() {
        let module = crate::module::ModuleId::new(1);
        let failed = ConstructorId::new(crate::types::NominalTypeId::new(module, 1), 1);
        let error = ConstructorId::new(crate::types::NominalTypeId::new(module, 0), 0);
        let mut heap = vec![HeapCell::Constructor(error, None)];
        {
            let _fault = report_reservation_fault::fail_next();
            let mut work = TypeWorkBudget::with_limit(2);
            assert!(ByteReplyReady::refusal(&mut heap, &mut work, failed, error).is_err());
            assert_eq!(
                work.remaining(),
                0,
                "report work precedes storage admission"
            );
            assert_eq!(report_reservation_fault::hits(), 1);
            assert_eq!(heap.len(), 1, "no partially published refusal");
            assert!(matches!(&heap[0], HeapCell::Constructor(found, None) if *found == error));
        }
        for _ in 0..2 {
            let mut work = TypeWorkBudget::with_limit(2);
            let before = heap.len();
            let Value::Location(location) =
                ByteReplyReady::refusal(&mut heap, &mut work, failed, error).unwrap()
            else {
                panic!("prepaid refusal report")
            };
            assert_eq!(location, before + 1);
            assert_eq!(heap.len(), before + 2);
            assert_eq!(work.remaining(), 0);
        }
    }
}
