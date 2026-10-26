//! Region ownership and target-directed service at its structural owner frame.
use super::*;
use crate::eval::value::{Address, RegionInvocation, RegionStorage};

/// Registration facts only. Physical validity and isolation remain the binding
/// module's assumptions; initialization must consume the pending token.
#[derive(Debug)]
pub(super) struct BackingRecord {
    pub(super) locator: Address,
    pub(super) extent: usize,
    pub(super) usable_bytes: usize,
    pub(super) alignment: usize,
    pub(super) invocation: RegionInvocation,
    pub(super) location: Option<Location>,
    pub(super) initialized: bool,
}

/// The fixed host root's records, moved to the existing shared observation owner.
/// This retains no evaluator, source release action or ownership of another heap.
#[derive(Debug)]
pub(in crate::eval) struct HostRootCompletion {
    records: Vec<BackingRecord>,
}

impl HostRootCompletion {
    pub(in crate::eval) fn close(&mut self, heap: &mut [HeapCell]) {
        // Preparation authenticated every location and paid these two flat passes.
        // Empty the Rust representation before freeing any root backing. Existing
        // metadata disposal reports through the ambient Scope, if one is active.
        for record in &mut self.records {
            if let HeapCell::Tuple(fields) =
                &mut heap[record.location.expect("prepared host root location")]
            {
                for field in fields.iter_mut() {
                    drop(std::mem::replace(field, Value::Unit));
                }
            }
            record.initialized = false;
        }
        for record in &self.records {
            heap[record.location.expect("prepared host root location")] = HeapCell::Uninitialized;
        }
        self.records.clear();
    }
}

#[derive(Debug)]
pub(super) struct BufferProgress {
    node: NodeId,
    environment: Environment,
    owner: Option<ActivationKey>,
    step: u8,
    prepared: Option<PreparedBuffer>,
    left: Option<Value>,
}
#[derive(Debug)]
struct PreparedBuffer {
    bytes: Option<Vec<u8>>,
    string: bool,
    constructor: Option<crate::types::ConstructorId>,
    payload: Option<Value>,
    integer_sign: Option<bool>,
}

impl Machine<'_> {
    /// Prepare and move only the validated fixed host entry owner. Refusal leaves
    /// its frame, records and initialized cells untouched for existing teardown.
    pub(super) fn retain_root_completion(&mut self) -> Result<(), RuntimeFailure> {
        let Some(Frame::RegionBoundary {
            node,
            key,
            allocate,
            release,
            preceding,
            records,
        }) = self.frames.last()
        else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        if self.root_completion.is_some()
            || !self
                .region_scope(*node)
                .ok_or(RuntimeFailure::InvalidControlState)?
                .entry
            || !matches!(allocate, Value::RegionHostFunction { owner, release: false } if owner == key)
            || !matches!(release, Value::RegionHostFunction { owner, release: true } if owner == key)
            || !matches!(preceding, Value::Unit)
        {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let record_work = records
            .len()
            .checked_mul(3)
            .ok_or(RuntimeFailure::HeapCapacity)?;
        charge_effect_work(
            &mut self.instantiation_work,
            record_work,
            RuntimePhase::Cleanup,
        )?;
        let mut previous = None;
        let mut fields = 0usize;
        for record in records {
            let location = record.location.ok_or(RuntimeFailure::InvalidControlState)?;
            if record.invocation.owner != *key
                || previous.is_some_and(|previous| location <= previous)
                || record.extent != record.usable_bytes
                || record.extent > isize::MAX as usize
            {
                return Err(RuntimeFailure::InvalidControlState);
            }
            previous = Some(location);
            let cell = self
                .heap
                .get(location)
                .ok_or(RuntimeFailure::InvalidControlState)?;
            let valid = match cell {
                HeapCell::Tuple(values) => {
                    fields = fields
                        .checked_add(values.len())
                        .ok_or(RuntimeFailure::HeapCapacity)?;
                    record.alignment == core::mem::align_of::<Value>()
                        && values.len().checked_mul(core::mem::size_of::<Value>())
                            == Some(record.usable_bytes)
                        && values.as_ptr().cast::<core::ffi::c_void>().cast_mut()
                            == record.locator.as_ptr()
                }
                HeapCell::Bytes(bytes, len, _) => {
                    record.alignment == 1
                        && bytes.len() == record.usable_bytes
                        && *len <= bytes.len()
                        && bytes.as_ptr().cast::<core::ffi::c_void>().cast_mut()
                            == record.locator.as_ptr()
                }
                _ => false,
            };
            if !valid {
                return Err(RuntimeFailure::InvalidControlState);
            }
        }
        charge_effect_work(&mut self.instantiation_work, fields, RuntimePhase::Cleanup)?;
        let Some(Frame::RegionBoundary { records, .. }) = self.frames.pop() else {
            unreachable!()
        };
        self.root_completion = Some(HostRootCompletion { records });
        Ok(())
    }

    fn buffer_node(&self, node: NodeId) -> Option<&crate::core::region::RegionBufferNode> {
        let Some(ExecutableNode::Effect(expression)) = self.program.node(node) else {
            return None;
        };
        if let EffectExprKind::Operation(EffectOperation::RegionBuffer(buffer)) = &expression.kind {
            Some(buffer)
        } else {
            None
        }
    }

    fn prepare_buffer(
        &mut self,
        node: NodeId,
        argument: Value,
        right: Option<Value>,
    ) -> Result<PreparedBuffer, RuntimeFailure> {
        use crate::core::{packed::Intrinsic, region::RegionBufferOperation};
        let operation = self
            .buffer_node(node)
            .ok_or(RuntimeFailure::InvalidControlState)?
            .operation
            .clone();
        let mut prepared = PreparedBuffer {
            bytes: None,
            string: false,
            constructor: None,
            payload: None,
            integer_sign: None,
        };
        fn copy(
            bytes: &[u8],
            append: Option<u8>,
            work: &mut crate::types::TypeWorkBudget,
        ) -> Result<Vec<u8>, RuntimeFailure> {
            let len = bytes
                .len()
                .checked_add(usize::from(append.is_some()))
                .filter(|len| *len <= isize::MAX as usize)
                .ok_or(RuntimeFailure::HeapCapacity)?;
            charge_effect_work(work, len, RuntimePhase::Evaluation)?;
            let mut output = Vec::new();
            reserve_control(&mut output, len, RuntimeResource::HeapCells, true)?;
            output.extend_from_slice(bytes);
            if let Some(byte) = append {
                output.push(byte);
            }
            Ok(output)
        }
        match operation {
            RegionBufferOperation::IntegerLiteral(integer) => {
                charge_effect_work(
                    &mut self.instantiation_work,
                    usize::try_from(integer.magnitude_byte_length())
                        .map_err(|_| RuntimeFailure::HeapCapacity)?,
                    RuntimePhase::Evaluation,
                )?;
                let (negative, bytes) = integer.sign_magnitude();
                prepared.bytes = Some(bytes);
                prepared.integer_sign = Some(negative);
            }
            RegionBufferOperation::IntegerArithmetic(primitive) => {
                let left = read_integer(&argument, &self.heap, &mut self.instantiation_work)?;
                let right = read_integer(
                    &right.ok_or(RuntimeFailure::InvalidControlState)?,
                    &self.heap,
                    &mut self.instantiation_work,
                )?;
                let left_len = usize::try_from(left.magnitude_byte_length())
                    .map_err(|_| RuntimeFailure::HeapCapacity)?;
                let right_len = usize::try_from(right.magnitude_byte_length())
                    .map_err(|_| RuntimeFailure::HeapCapacity)?;
                let work = if primitive == crate::core::Primitive::Multiply {
                    left_len.checked_mul(right_len)
                } else {
                    left_len.checked_add(right_len)
                }
                .ok_or(RuntimeFailure::HeapCapacity)?;
                charge_effect_work(
                    &mut self.instantiation_work,
                    work.saturating_add(1),
                    RuntimePhase::Evaluation,
                )?;
                let result = match primitive {
                    crate::core::Primitive::Add => &left + &right,
                    crate::core::Primitive::Multiply => &left * &right,
                    _ => return Err(RuntimeFailure::InvalidControlState),
                };
                if let Some(value) = result.to_i128() {
                    prepared.payload = Some(Value::SmallInteger(value));
                } else {
                    let (negative, bytes) = result.sign_magnitude();
                    prepared.bytes = Some(bytes);
                    prepared.integer_sign = Some(negative);
                }
            }
            RegionBufferOperation::StringLiteral(bytes) => {
                prepared.bytes = Some(copy(&bytes, None, &mut self.instantiation_work)?);
                prepared.string = true;
            }
            RegionBufferOperation::Intrinsic(intrinsic) => match intrinsic.operation() {
                Intrinsic::BytesEmpty => prepared.bytes = Some(Vec::new()),
                Intrinsic::StringToUtf8 => {
                    let (bytes, string) =
                        borrowed_bytes(&argument, &self.heap, &mut self.instantiation_work)?;
                    if !string {
                        return Err(RuntimeFailure::InvalidControlState);
                    }
                    prepared.bytes = Some(copy(bytes, None, &mut self.instantiation_work)?);
                }
                Intrinsic::StringFromUtf8 { decoded, invalid } => {
                    let (bytes, string) =
                        borrowed_bytes(&argument, &self.heap, &mut self.instantiation_work)?;
                    if string {
                        return Err(RuntimeFailure::InvalidControlState);
                    }
                    charge_effect_work(
                        &mut self.instantiation_work,
                        bytes.len(),
                        RuntimePhase::Evaluation,
                    )?;
                    if std::str::from_utf8(bytes).is_ok() {
                        prepared.bytes = Some(copy(bytes, None, &mut self.instantiation_work)?);
                        prepared.string = true;
                        prepared.constructor = Some(decoded);
                    } else {
                        prepared.constructor = Some(invalid);
                    }
                }
                op @ (Intrinsic::BytesAt { .. } | Intrinsic::BytesAppendByte { .. }) => {
                    let Value::Location(location) = argument else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    let location =
                        packed_tuple_location(&self.heap, location, &mut self.instantiation_work)?;
                    let Some(fields) = self.heap[location].tuple_fields() else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    let [bytes, integer] = fields else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    let integer = read_integer(integer, &self.heap, &mut self.instantiation_work)?;
                    let (bytes, string) =
                        borrowed_bytes(bytes, &self.heap, &mut self.instantiation_work)?;
                    if string {
                        return Err(RuntimeFailure::InvalidControlState);
                    }
                    match op {
                        Intrinsic::BytesAt { found, invalid } => {
                            if let Some(byte) = integer.to_usize().and_then(|i| bytes.get(i)) {
                                prepared.constructor = Some(found);
                                prepared.payload = Some(Value::SmallInteger(i128::from(*byte)));
                            } else {
                                prepared.constructor = Some(invalid);
                            }
                        }
                        Intrinsic::BytesAppendByte { appended, invalid } => {
                            if let Some(byte) = integer.to_i64().and_then(|i| u8::try_from(i).ok())
                            {
                                prepared.constructor = Some(appended);
                                prepared.bytes =
                                    Some(copy(bytes, Some(byte), &mut self.instantiation_work)?);
                            } else {
                                prepared.constructor = Some(invalid);
                            }
                        }
                        _ => unreachable!(),
                    }
                }
                _ => return Err(RuntimeFailure::InvalidControlState),
            },
        }
        Ok(prepared)
    }

    pub(super) fn return_region_buffer(
        &mut self,
        mut progress: BufferProgress,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        if progress.step == 0 {
            let Value::RegionView(owner) = value else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            progress.owner = Some(owner);
            if let Some(operand) = self
                .buffer_node(progress.node)
                .ok_or(RuntimeFailure::InvalidControlState)?
                .operand
            {
                progress.step = 1;
                let environment = progress.environment.clone();
                self.frames.push(Frame::RegionBuffer(progress));
                self.control = Some(Control::Evaluate(operand, environment));
                return Ok(());
            }
            progress.prepared = Some(self.prepare_buffer(progress.node, Value::Unit, None)?);
        } else if progress.step == 1 {
            if let Some(right) = self
                .buffer_node(progress.node)
                .ok_or(RuntimeFailure::InvalidControlState)?
                .right
            {
                progress.left = Some(value);
                progress.step = 4;
                let environment = progress.environment.clone();
                self.frames.push(Frame::RegionBuffer(progress));
                self.control = Some(Control::Evaluate(right, environment));
                return Ok(());
            }
            progress.prepared = Some(self.prepare_buffer(progress.node, value, None)?);
        } else if progress.step == 4 {
            progress.prepared = Some(
                self.prepare_buffer(
                    progress.node,
                    progress
                        .left
                        .take()
                        .ok_or(RuntimeFailure::InvalidControlState)?,
                    Some(value),
                )?,
            );
        } else {
            let Value::RegionStorage(storage) = value else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            if Some(storage.invocation.owner) != progress.owner {
                return Err(RuntimeFailure::InvalidControlState);
            }
            let prepared = progress
                .prepared
                .as_mut()
                .ok_or(RuntimeFailure::InvalidControlState)?;
            if progress.step == 2 {
                let bytes = prepared
                    .bytes
                    .take()
                    .ok_or(RuntimeFailure::InvalidControlState)?;
                let mut initialized =
                    self.initialize_region_bytes(storage, &bytes, prepared.string)?;
                if let Some(negative) = prepared.integer_sign {
                    let Value::Location(digits) = initialized else {
                        return Err(RuntimeFailure::InvalidControlState);
                    };
                    initialized = Value::RegionInteger { digits, negative };
                }
                if prepared.constructor.is_none() {
                    self.control = Some(Control::Return(initialized));
                    return Ok(());
                }
                prepared.payload = Some(initialized);
            } else {
                let mut fields = Vec::new();
                reserve_control(&mut fields, 2, RuntimeResource::HeapCells, true)?;
                fields.push(Value::ConstructorTag(
                    prepared
                        .constructor
                        .ok_or(RuntimeFailure::InvalidControlState)?,
                ));
                fields.extend(prepared.payload.take());
                let initialized = self.initialize_region_tuple(storage, fields)?;
                self.control = Some(Control::Return(initialized));
                return Ok(());
            }
        }
        let prepared = progress
            .prepared
            .as_ref()
            .ok_or(RuntimeFailure::InvalidControlState)?;
        if prepared.bytes.is_none() && prepared.constructor.is_none() {
            self.control = Some(Control::Return(
                progress
                    .prepared
                    .as_mut()
                    .and_then(|p| p.payload.take())
                    .ok_or(RuntimeFailure::InvalidControlState)?,
            ));
            return Ok(());
        }
        let (usable_bytes, alignment, step) = if let Some(bytes) = &prepared.bytes {
            (bytes.len().max(1), 1, 2)
        } else {
            (
                (1 + usize::from(prepared.payload.is_some())) * core::mem::size_of::<Value>(),
                core::mem::align_of::<Value>(),
                3,
            )
        };
        progress.step = step;
        let owner = progress.owner.ok_or(RuntimeFailure::InvalidControlState)?;
        reserve_control(&mut self.frames, 1, RuntimeResource::FrameStorage, false)?;
        self.frames.push(Frame::RegionBuffer(progress));
        self.invoke_region_allocate(
            Value::RegionView(owner),
            Value::RegionRequest(crate::eval::value::RegionRequest {
                usable_bytes,
                alignment,
                invocation: None,
            }),
        )
    }

    pub(super) fn region_scope(
        &self,
        node: NodeId,
    ) -> Option<&crate::core::region::RegionScopeNode> {
        let ExecutableNode::Effect(expression) = self.program.node(node)? else {
            return None;
        };
        let EffectExprKind::Operation(EffectOperation::Region(scope)) = &expression.kind else {
            return None;
        };
        Some(scope)
    }

    pub(super) fn region_allocation(
        &self,
        node: NodeId,
    ) -> Option<&crate::core::region::RegionAllocateNode> {
        let ExecutableNode::Effect(expression) = self.program.node(node)? else {
            return None;
        };
        let EffectExprKind::Operation(EffectOperation::RegionAllocate(allocation)) =
            &expression.kind
        else {
            return None;
        };
        Some(allocation)
    }

    fn region_tuple(&self, node: NodeId) -> Option<&crate::core::region::RegionTupleNode> {
        let ExecutableNode::Effect(expression) = self.program.node(node)? else {
            return None;
        };
        let EffectExprKind::Operation(EffectOperation::RegionTuple(tuple)) = &expression.kind
        else {
            return None;
        };
        Some(tuple)
    }

    fn region_closure(&self, node: NodeId) -> Option<&crate::core::region::RegionClosureNode> {
        let ExecutableNode::Effect(expression) = self.program.node(node)? else {
            return None;
        };
        let EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) = &expression.kind
        else {
            return None;
        };
        Some(closure)
    }

    #[allow(
        clippy::too_many_arguments,
        reason = "one explicit tuple initializer frame is moved through the existing machine"
    )]
    pub(super) fn return_region_tuple(
        &mut self,
        node: NodeId,
        abstraction: Option<NodeId>,
        environment: Environment,
        mut context: Option<ActivationKey>,
        next: usize,
        mut fields: Vec<Value>,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        let (operands, storage_node, constructor, closure) =
            if let Some(tuple) = self.region_tuple(node) {
                (
                    tuple.fields.as_ref(),
                    tuple.storage,
                    tuple.constructor,
                    false,
                )
            } else if let Some(closure) = self.region_closure(node) {
                (closure.captures.as_ref(), closure.storage, None, true)
            } else {
                return Err(RuntimeFailure::InvalidControlState);
            };
        let following = if next == 0 {
            let Value::RegionView(owner) = value else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            context = Some(owner);
            operands.first().copied().or(Some(storage_node))
        } else if next <= operands.len() {
            fields.push(value);
            Some(operands.get(next).copied().unwrap_or(storage_node))
        } else {
            let Value::RegionStorage(storage) = value else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            if Some(storage.invocation.owner) != context {
                return Err(RuntimeFailure::InvalidControlState);
            }
            if let Some(constructor) = constructor {
                fields.insert(0, Value::ConstructorTag(constructor));
            }
            if closure {
                fields.insert(
                    0,
                    Value::ClosureCode(crate::eval::value::ClosureCode {
                        abstraction,
                        node,
                        program: self.program.clone(),
                        instantiation: environment.instantiation.clone(),
                    }),
                );
            }
            let initialized = self.initialize_region_tuple(storage, fields)?;
            let initialized = if closure {
                let Value::Location(record) = initialized else {
                    return Err(RuntimeFailure::InvalidControlState);
                };
                Value::RegionFunction(crate::eval::value::RegionFunction {
                    record,
                    instantiation: None,
                    abstraction: None,
                })
            } else {
                initialized
            };
            self.control = Some(Control::Return(initialized));
            return Ok(());
        };
        if let Some(following) = following {
            self.frames.push(Frame::RegionTuple {
                abstraction,
                node,
                environment: environment.clone(),
                context,
                next: next + 1,
                fields,
            });
            self.control = Some(Control::Evaluate(following, environment));
        } else {
            return Err(RuntimeFailure::InvalidControlState);
        }
        Ok(())
    }

    pub(super) fn read_callable(
        &mut self,
        value: &Value,
    ) -> Result<crate::eval::Closure, RuntimeFailure> {
        self.read_callable_metadata(value)
            .map(|(callable, _)| callable)
    }

    pub(super) fn read_callable_metadata(
        &mut self,
        value: &Value,
    ) -> Result<(crate::eval::Closure, Option<NodeId>), RuntimeFailure> {
        if let Value::Function(function) = value {
            return Ok((function.clone(), None));
        }
        let (code, environment, abstraction) = self.read_stored_callable(value)?;
        let Some(ExecutableNode::Effect(expression)) = code.program.node(code.node) else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) = &expression.kind
        else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let function = closure
            .code
            .function()
            .ok_or(RuntimeFailure::UnexpectedFunctionValue)?;
        Ok((
            crate::eval::Closure {
                parameter: function.parameter().id(),
                body: function.body(),
                program: code.program.clone(),
                environment,
                origin: expression.origin.clone(),
            },
            abstraction,
        ))
    }

    pub(super) fn read_stored_callable(
        &mut self,
        value: &Value,
    ) -> Result<(crate::eval::value::ClosureCode, Environment, Option<NodeId>), RuntimeFailure>
    {
        let (record, view) = match value {
            Value::RegionFunction(callable) => (callable.record, callable.instantiation.as_ref()),
            Value::Location(record) => (*record, None),
            _ => return Err(RuntimeFailure::UnexpectedFunctionValue),
        };
        let location = packed_tuple_location(&self.heap, record, &mut self.instantiation_work)?;
        let fields = self
            .heap
            .get(location)
            .and_then(HeapCell::stored_fields)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let Some(Value::ClosureCode(code)) = fields.first() else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let Some(ExecutableNode::Effect(expression)) = code.program.node(code.node) else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) = &expression.kind
        else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        if fields.len() != closure.captures.len() + 1 {
            return Err(RuntimeFailure::InvalidControlState);
        }
        charge_effect_work(
            &mut self.instantiation_work,
            fields.len(),
            RuntimePhase::Access,
        )?;
        let mut environment = Environment::new();
        environment.instantiation = view.unwrap_or(&code.instantiation).clone();
        for (capture, value) in closure.captures.iter().zip(&fields[1..]) {
            let Some(ExecutableNode::Effect(expression)) = code.program.node(*capture) else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            let EffectExprKind::Pure(PureExprKind::Variable(variable)) = &expression.kind else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            environment = environment.extend_in_phase(
                variable.binder(),
                value.clone(),
                RuntimePhase::Access,
            )?;
        }
        Ok((
            code.clone(),
            environment,
            match value {
                Value::RegionFunction(view) => view.abstraction.or(code.abstraction),
                _ => code.abstraction,
            },
        ))
    }

    pub(super) fn enter_region(
        &mut self,
        node: NodeId,
        environment: &Environment,
    ) -> Result<bool, RuntimeFailure> {
        if let Some(ExecutableNode::Effect(expression)) = self.program.node(node)
            && let EffectExprKind::Operation(EffectOperation::RegionValueRequest(request)) =
                &expression.kind
        {
            let usable_bytes = request
                .fields
                .checked_mul(core::mem::size_of::<Value>())
                .filter(|bytes| *bytes <= isize::MAX as usize)
                .ok_or(RuntimeFailure::HeapCapacity)?;
            self.control = Some(Control::Return(Value::RegionRequest(
                crate::eval::value::RegionRequest {
                    usable_bytes,
                    alignment: core::mem::align_of::<Value>(),
                    invocation: None,
                },
            )));
            return Ok(true);
        }
        if let Some(buffer) = self.buffer_node(node) {
            let context = buffer.context;
            reserve_control(&mut self.frames, 1, RuntimeResource::FrameStorage, false)?;
            self.frames.push(Frame::RegionBuffer(BufferProgress {
                node,
                environment: environment.clone(),
                owner: None,
                step: 0,
                prepared: None,
                left: None,
            }));
            self.control = Some(Control::Evaluate(context, environment.clone()));
            return Ok(true);
        }
        if let Some(closure) = self.region_closure(node) {
            let (context, count) = (closure.context, closure.captures.len() + 1);
            let mut fields = Vec::new();
            reserve_control(&mut fields, count, RuntimeResource::HeapCells, true)?;
            reserve_control(&mut self.frames, 1, RuntimeResource::FrameStorage, false)?;
            let abstraction = match self.frames.last() {
                Some(Frame::RegionAbstraction {
                    abstraction,
                    closure,
                }) if *closure == node => Some(*abstraction),
                _ => None,
            };
            if abstraction.is_some() {
                self.frames.pop();
            }
            self.frames.push(Frame::RegionTuple {
                abstraction,
                node,
                environment: environment.clone(),
                context: None,
                next: 0,
                fields,
            });
            self.control = Some(Control::Evaluate(context, environment.clone()));
            return Ok(true);
        }
        if let Some(tuple) = self.region_tuple(node) {
            let (context, count) = (
                tuple.context,
                tuple.fields.len() + usize::from(tuple.constructor.is_some()),
            );
            let mut fields = Vec::new();
            reserve_control(&mut fields, count, RuntimeResource::HeapCells, true)?;
            reserve_control(&mut self.frames, 1, RuntimeResource::FrameStorage, false)?;
            self.frames.push(Frame::RegionTuple {
                abstraction: None,
                node,
                environment: environment.clone(),
                context: None,
                next: 0,
                fields,
            });
            self.control = Some(Control::Evaluate(context, environment.clone()));
            return Ok(true);
        }
        if let Some(scope) = self.region_scope(node) {
            let entry = scope.entry;
            let preceding = scope.preceding();
            if entry {
                self.prepare_region_provider(node, environment.clone(), Value::Unit)?;
            } else {
                self.frames
                    .try_reserve(1)
                    .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
                self.frames.push(Frame::RegionPreceding {
                    node,
                    environment: environment.clone(),
                });
                self.control = Some(Control::Evaluate(preceding, environment.clone()));
            }
            return Ok(true);
        }
        if let Some(allocation) = self.region_allocation(node) {
            let context = allocation.context();
            self.frames
                .try_reserve(1)
                .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
            self.frames.push(Frame::RegionContext {
                node,
                environment: environment.clone(),
            });
            self.control = Some(Control::Evaluate(context, environment.clone()));
            return Ok(true);
        }
        if let Ok(PureExprKind::Value(PureValue::Intrinsic(intrinsic))) =
            pure_expression(&self.program, node)
        {
            use crate::core::packed::Intrinsic;
            if let Intrinsic::RegionFromBacking { owner, .. } = intrinsic.operation() {
                if !intrinsic.authentic_module() {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                let owner = environment
                    .instantiation
                    .owner(owner, &mut self.instantiation_work)?;
                self.control = Some(Control::Return(Value::RegionBackingFunction(owner)));
                return Ok(true);
            }
            if let Intrinsic::RegionHostAllocate { owner, .. }
            | Intrinsic::RegionHostRelease { owner, .. } = intrinsic.operation()
            {
                if !intrinsic.authentic_module() {
                    return Err(RuntimeFailure::InvalidControlState);
                }
                let key = environment
                    .instantiation
                    .owner(owner, &mut self.instantiation_work)?;
                self.control = Some(Control::Return(Value::RegionHostFunction {
                    owner: key,
                    release: matches!(intrinsic.operation(), Intrinsic::RegionHostRelease { .. }),
                }));
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) fn prepare_region_provider(
        &mut self,
        node: NodeId,
        mut environment: Environment,
        preceding: Value,
    ) -> Result<(), RuntimeFailure> {
        let scope = self
            .region_scope(node)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let (identity, provider, entry) = (scope.identity(), scope.provider(), scope.entry);
        if !(matches!(preceding, Value::RegionView(_)) || entry && matches!(preceding, Value::Unit))
        {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let next = self
            .next_activation
            .checked_add(1)
            .ok_or(RuntimeFailure::ResourceCapacity)?;
        let key = ActivationKey(self.next_activation);
        environment.instantiation = environment.instantiation.acquire(
            identity,
            key,
            &mut self.instantiation_work,
            Some(RuntimePhase::Acquisition),
        )?;
        self.frames
            .try_reserve(1)
            .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
        self.frames.push(Frame::RegionProvider {
            node,
            environment: environment.clone(),
            key,
            preceding,
        });
        self.next_activation = next;
        self.control = Some(Control::Evaluate(provider, environment));
        Ok(())
    }

    pub(super) fn publish_region(
        &mut self,
        node: NodeId,
        environment: Environment,
        key: ActivationKey,
        preceding: Value,
        provider: Value,
    ) -> Result<(), RuntimeFailure> {
        let scope = self
            .region_scope(node)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let (access, body) = (scope.access().id(), scope.body());
        let Value::Location(location) = provider else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let location = packed_tuple_location(&self.heap, location, &mut self.instantiation_work)?;
        let Some(fields) = self.heap.get(location).and_then(HeapCell::tuple_fields) else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let [allocate, release] = fields.as_ref() else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let (allocate, release) = (allocate.clone(), release.clone());
        let environment = environment.extend_in_phase(
            access,
            Value::RegionView(key),
            RuntimePhase::Acquisition,
        )?;
        self.frames
            .try_reserve(1)
            .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
        self.frames.push(Frame::RegionBoundary {
            node,
            key,
            allocate,
            release,
            preceding,
            records: Vec::new(),
        });
        self.control = Some(Control::Evaluate(body, environment));
        Ok(())
    }

    pub(super) fn invoke_region_allocate(
        &mut self,
        context: Value,
        request: Value,
    ) -> Result<(), RuntimeFailure> {
        let Value::RegionView(key) = context else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let Value::RegionRequest(mut request) = request else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        if request.invocation.is_some()
            || request.alignment == 0
            || !request.alignment.is_power_of_two()
        {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let invocation = RegionInvocation {
            owner: key,
            serial: self.next_region_invocation,
        };
        let next = self
            .next_region_invocation
            .checked_add(1)
            .ok_or(RuntimeFailure::ResourceCapacity)?;
        charge_effect_work(
            &mut self.instantiation_work,
            self.frames.len(),
            RuntimePhase::Access,
        )?;
        let index = self.frames.iter().rposition(|frame| matches!(frame, Frame::RegionBoundary { key: owner, .. } | Frame::RegionCompletion { key: owner, .. } if *owner == key))
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let (allocate, node, preceding) = match &self.frames[index] {
            Frame::RegionBoundary {
                allocate,
                node,
                preceding,
                ..
            }
            | Frame::RegionCompletion {
                allocate,
                node,
                preceding,
                ..
            } => (allocate.clone(), *node, preceding),
            _ => return Err(RuntimeFailure::InvalidControlState),
        };
        let entry = self
            .region_scope(node)
            .ok_or(RuntimeFailure::InvalidControlState)?
            .entry;
        if !(matches!(preceding, Value::RegionView(_)) || entry && matches!(preceding, Value::Unit))
        {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let captured_len = self.frames.len() - index - 1;
        let retained = self
            .captured_cells
            .checked_add(captured_len)
            .filter(|count| *count <= self.capture_limit)
            .ok_or_else(|| {
                control_failure(
                    ResourceFailureCause::ConfiguredCapacity,
                    RuntimeResource::FrameStorage,
                    Some(captured_len),
                    Some(self.capture_limit.saturating_sub(self.captured_cells)),
                )
            })?;
        let mut segment = Vec::new();
        segment
            .try_reserve_exact(self.frames.len() - index - 1)
            .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
        self.frames
            .try_reserve(2)
            .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
        segment.extend(self.frames.drain(index + 1..));
        self.captured_cells = retained;
        self.frames.push(Frame::RegionAllocated {
            segment: CapturedContinuation { frames: segment },
            invocation,
            registered: false,
        });
        request.invocation = Some(invocation);
        self.next_region_invocation = next;
        self.frames
            .push(Frame::ApplyArgument { function: allocate });
        self.control = Some(Control::Return(Value::RegionRequest(request)));
        Ok(())
    }
    pub(super) fn validate_region_storage(
        &mut self,
        storage: RegionStorage,
    ) -> Result<(), RuntimeFailure> {
        charge_effect_work(
            &mut self.instantiation_work,
            self.frames.len(),
            RuntimePhase::Access,
        )?;
        let record = self
            .frames
            .iter()
            .rev()
            .find_map(|frame| match frame {
                Frame::RegionBoundary { key, records, .. }
                | Frame::RegionCompletion { key, records, .. }
                    if *key == storage.invocation.owner =>
                {
                    records.get(storage.record)
                }
                _ => None,
            })
            .ok_or(RuntimeFailure::InvalidControlState)?;
        if record.invocation != storage.invocation
            || record.locator.as_ptr().is_null()
            || record.alignment == 0
            || !record.alignment.is_power_of_two()
            || record.extent > isize::MAX as usize
        {
            return Err(RuntimeFailure::InvalidControlState);
        }
        Ok(())
    }

    pub(super) fn allocate_host_region_storage(
        &mut self,
        owner: ActivationKey,
        request: Value,
    ) -> Result<Value, RuntimeFailure> {
        let Value::RegionRequest(request) = request else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let invocation = request
            .invocation
            .ok_or(RuntimeFailure::InvalidControlState)?;
        if invocation.owner == owner
            && request.alignment == 1
            && request.usable_bytes <= isize::MAX as usize
        {
            charge_effect_work(
                &mut self.instantiation_work,
                request.usable_bytes,
                RuntimePhase::Evaluation,
            )?;
            let mut bytes = Vec::new();
            reserve_control(
                &mut bytes,
                request.usable_bytes,
                RuntimeResource::HeapCells,
                true,
            )?;
            bytes.resize(request.usable_bytes, 0);
            let mut bytes = bytes.into_boxed_slice();
            let locator = Address::new(bytes.as_mut_ptr().cast());
            reserve_control(&mut self.heap, 1, RuntimeResource::HeapCells, false)?;
            let location = allocate_heap(&mut self.heap, HeapCell::Bytes(bytes, 0, false))?;
            return self.register_pending_backing(BackingRecord {
                locator,
                extent: request.usable_bytes,
                usable_bytes: request.usable_bytes,
                alignment: 1,
                invocation,
                location: Some(location),
                initialized: false,
            });
        }
        let cell_bytes = core::mem::size_of::<Value>();
        if invocation.owner != owner
            || request.alignment != core::mem::align_of::<Value>()
            || request.usable_bytes > isize::MAX as usize
            || request.usable_bytes % cell_bytes != 0
        {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let count = request.usable_bytes / cell_bytes;
        charge_effect_work(
            &mut self.instantiation_work,
            count,
            RuntimePhase::Evaluation,
        )?;
        let mut fields = Vec::new();
        reserve_control(&mut fields, count, RuntimeResource::HeapCells, true)?;
        fields.resize(count, Value::Unit);
        let mut fields = fields.into_boxed_slice();
        let locator = Address::new(fields.as_mut_ptr().cast());
        reserve_control(&mut self.heap, 1, RuntimeResource::HeapCells, false)?;
        let location = allocate_heap(&mut self.heap, HeapCell::Tuple(fields))?;
        self.register_pending_backing(BackingRecord {
            locator,
            extent: request.usable_bytes,
            usable_bytes: request.usable_bytes,
            alignment: request.alignment,
            invocation,
            location: Some(location),
            initialized: false,
        })
    }

    fn initialize_region_bytes(
        &mut self,
        storage: RegionStorage,
        bytes: &[u8],
        string: bool,
    ) -> Result<Value, RuntimeFailure> {
        self.validate_region_storage(storage)?;
        charge_effect_work(
            &mut self.instantiation_work,
            self.frames
                .len()
                .saturating_add(bytes.len().saturating_mul(1 + usize::from(string))),
            RuntimePhase::Access,
        )?;
        let record = self
            .frames
            .iter_mut()
            .rev()
            .find_map(|frame| match frame {
                Frame::RegionBoundary { key, records, .. }
                | Frame::RegionCompletion { key, records, .. }
                    if *key == storage.invocation.owner =>
                {
                    records.get_mut(storage.record)
                }
                _ => None,
            })
            .ok_or(RuntimeFailure::InvalidControlState)?;
        if record.initialized
            || record.usable_bytes != bytes.len().max(1)
            || record.extent < record.usable_bytes
            || (string && std::str::from_utf8(bytes).is_err())
        {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let location = if let Some(location) = record.location {
            let Some(HeapCell::Bytes(fields, len, kind)) = self.heap.get_mut(location) else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            fields[..bytes.len()].copy_from_slice(bytes);
            *len = bytes.len();
            *kind = string;
            location
        } else {
            let adapter = self
                .source_bindings
                .and_then(|b| b.tuple_storage)
                .ok_or(RuntimeFailure::ForeignBinding)?;
            reserve_control(&mut self.heap, 1, RuntimeResource::HeapCells, true)?;
            let backing = super::super::value::NativeByteStorage::initialize(
                record.locator.clone(),
                bytes,
                adapter,
            );
            let location = allocate_heap(&mut self.heap, HeapCell::NativeBytes(backing, string))?;
            record.location = Some(location);
            location
        };
        record.initialized = true;
        Ok(Value::Location(location))
    }

    /// Consume one pending record by moving evaluated fields into its actual
    /// supplied storage. Native access remains at the generated host boundary.
    pub(super) fn initialize_region_tuple(
        &mut self,
        storage: RegionStorage,
        values: Vec<Value>,
    ) -> Result<Value, RuntimeFailure> {
        self.validate_region_storage(storage)?;
        charge_effect_work(
            &mut self.instantiation_work,
            self.frames.len().saturating_add(values.len()),
            RuntimePhase::Access,
        )?;
        let target = self
            .frames
            .iter()
            .rposition(|frame| {
                matches!(frame,
            Frame::RegionBoundary { key, .. } | Frame::RegionCompletion { key, .. }
                if *key == storage.invocation.owner)
            })
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let records = match &mut self.frames[target] {
            Frame::RegionBoundary { records, .. } | Frame::RegionCompletion { records, .. } => {
                records
            }
            _ => return Err(RuntimeFailure::InvalidControlState),
        };
        let record = records
            .get_mut(storage.record)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        if record.initialized {
            return Err(RuntimeFailure::InvalidControlState);
        }
        if values.len().checked_mul(core::mem::size_of::<Value>()) != Some(record.usable_bytes)
            || record.extent < record.usable_bytes
            || record.alignment < core::mem::align_of::<Value>()
            || (record.locator.as_ptr() as usize) % core::mem::align_of::<Value>() != 0
        {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let location = if let Some(location) = record.location {
            let Some(HeapCell::Tuple(fields)) = self.heap.get_mut(location) else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            if fields.len() != values.len() {
                return Err(RuntimeFailure::InvalidControlState);
            }
            for (field, value) in fields.iter_mut().zip(values) {
                *field = value;
            }
            location
        } else {
            let adapter = self
                .source_bindings
                .and_then(|bindings| bindings.tuple_storage)
                .ok_or(RuntimeFailure::ForeignBinding)?;
            reserve_control(&mut self.heap, 1, RuntimeResource::HeapCells, true)?;
            let fields = super::super::value::NativeTupleStorage::initialize(
                record.locator.clone(),
                values,
                adapter,
            );
            let location = allocate_heap(&mut self.heap, HeapCell::NativeTuple(fields))?;
            record.location = Some(location);
            location
        };
        record.initialized = true;
        Ok(Value::Location(location))
    }

    /// Release Rust-owned fields in the current Value representation while
    /// backing is live. The provider frees backing separately; logical records
    /// retire only after the paired release returns.
    pub(super) fn drop_region_rust_fields_before_release(&mut self) -> Result<(), RuntimeFailure> {
        let index = self
            .frames
            .len()
            .checked_sub(2)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let Some(Frame::RegionCompletion { node, .. }) = self.frames.get(index) else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        // run_loop transfers the fixed host entry before ordinary close.
        if self
            .region_scope(*node)
            .ok_or(RuntimeFailure::InvalidControlState)?
            .entry
        {
            return Ok(());
        }
        let Frame::RegionCompletion { records, .. } = &mut self.frames[index] else {
            unreachable!()
        };
        charge_effect_work(
            &mut self.instantiation_work,
            records
                .len()
                .checked_mul(2)
                .ok_or(RuntimeFailure::HeapCapacity)?,
            RuntimePhase::Cleanup,
        )?;
        let mut cells = 0usize;
        for record in records.iter().filter(|record| record.initialized) {
            let cell = record
                .location
                .and_then(|location| self.heap.get(location))
                .ok_or(RuntimeFailure::InvalidControlState)?;
            let count = if matches!(cell, HeapCell::Bytes(..) | HeapCell::NativeBytes(..)) {
                0
            } else {
                cell.stored_fields()
                    .ok_or(RuntimeFailure::InvalidControlState)?
                    .len()
            };
            cells = cells
                .checked_add(count)
                .ok_or(RuntimeFailure::HeapCapacity)?;
        }
        // Charge the whole drop before changing any ownership state. Both the
        // completion and paired release frames remain owned on refusal.
        charge_effect_work(&mut self.instantiation_work, cells, RuntimePhase::Cleanup)?;
        for record in records.iter_mut().filter(|record| record.initialized) {
            let cell = self
                .heap
                .get_mut(record.location.ok_or(RuntimeFailure::InvalidControlState)?)
                .ok_or(RuntimeFailure::InvalidControlState)?;
            record.initialized = false;
            match cell {
                HeapCell::Tuple(fields) => {
                    for field in fields.iter_mut() {
                        drop(std::mem::replace(field, Value::Unit));
                    }
                }
                HeapCell::NativeTuple(_) => {
                    drop(std::mem::replace(cell, HeapCell::Uninitialized));
                }
                HeapCell::Bytes(..) | HeapCell::NativeBytes(..) => {}
                _ => return Err(RuntimeFailure::InvalidControlState),
            }
        }
        disposal::check()
    }

    pub(super) fn register_region_backing(
        &mut self,
        owner: ActivationKey,
        value: Value,
    ) -> Result<Value, RuntimeFailure> {
        let Value::Location(location) = value else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let location = packed_tuple_location(&self.heap, location, &mut self.instantiation_work)?;
        let Some(fields) = self.heap.get(location).and_then(HeapCell::tuple_fields) else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let [
            Value::RegionRequest(request),
            Value::Address(locator),
            extent,
            alignment,
        ] = fields.as_ref()
        else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let invocation = request
            .invocation
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let extent = read_integer(extent, &self.heap, &mut self.instantiation_work)?
            .to_usize()
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let alignment = read_integer(alignment, &self.heap, &mut self.instantiation_work)?
            .to_usize()
            .ok_or(RuntimeFailure::InvalidControlState)?;
        if invocation.owner != owner
            || locator.as_ptr().is_null()
            || alignment == 0
            || !alignment.is_power_of_two()
            || request.alignment == 0
            || !request.alignment.is_power_of_two()
            || alignment < request.alignment
            || extent > isize::MAX as usize
            || extent < request.usable_bytes
            || (locator.as_ptr() as usize) % request.alignment != 0
        {
            return Err(RuntimeFailure::InvalidControlState);
        }
        let locator = locator.clone();
        self.register_pending_backing(BackingRecord {
            locator,
            extent,
            usable_bytes: request.usable_bytes,
            alignment,
            invocation,
            location: None,
            initialized: false,
        })
    }

    fn register_pending_backing(
        &mut self,
        backing: BackingRecord,
    ) -> Result<Value, RuntimeFailure> {
        let invocation = backing.invocation;
        let owner = invocation.owner;
        charge_effect_work(
            &mut self.instantiation_work,
            self.frames.len().saturating_mul(2),
            RuntimePhase::Access,
        )?;
        let call = self.frames.iter().rposition(|frame| matches!(frame, Frame::RegionAllocated { invocation: expected, registered: false, .. } if *expected == invocation))
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let target = self.frames[..call].iter().rposition(|frame| matches!(frame,
            Frame::RegionBoundary { key, .. } | Frame::RegionCompletion { key, .. } if *key == owner)).ok_or(RuntimeFailure::InvalidControlState)?;
        let records = match &mut self.frames[target] {
            Frame::RegionBoundary { records, .. } | Frame::RegionCompletion { records, .. } => {
                records
            }
            _ => return Err(RuntimeFailure::InvalidControlState),
        };
        records
            .try_reserve(1)
            .map_err(|_| RuntimeFailure::EnvironmentCapacity)?;
        let record = records.len();
        records.push(backing);
        let Frame::RegionAllocated { registered, .. } = &mut self.frames[call] else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        *registered = true;
        Ok(Value::RegionStorage(RegionStorage { invocation, record }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        core::{EffectCoreBuilder, validate_effect},
        eval::value::RegionRequest,
        source::{ByteRange, Origin, SourceFile},
        types::Type,
    };

    fn root_driver(payload: Value) -> Machine<'static> {
        let program = super::super::tests::effect_program("main : Unit -> Unit\nmain () = ()\n");
        let mut pending = vec![program.root()];
        let node = loop {
            let id = pending.pop().expect("generated root");
            let kind = &program.node(id).unwrap().kind;
            if matches!(kind, EffectExprKind::Operation(EffectOperation::Region(scope)) if scope.entry)
            {
                break id;
            }
            pending.extend((0..kind.child_count()).filter_map(|index| kind.child_at(index)));
        };
        let mut fields = vec![payload].into_boxed_slice();
        let locator = Address::new(fields.as_mut_ptr().cast());
        let mut machine = Machine::new_effect(&program);
        machine.heap.push(HeapCell::Tuple(fields));
        machine.frames.push(Frame::RegionBoundary {
            node,
            key: ActivationKey(9),
            allocate: Value::RegionHostFunction {
                owner: ActivationKey(9),
                release: false,
            },
            release: Value::RegionHostFunction {
                owner: ActivationKey(9),
                release: true,
            },
            preceding: Value::Unit,
            records: vec![BackingRecord {
                locator,
                extent: core::mem::size_of::<Value>(),
                usable_bytes: core::mem::size_of::<Value>(),
                alignment: core::mem::align_of::<Value>(),
                invocation: RegionInvocation {
                    owner: ActivationKey(9),
                    serial: 5,
                },
                location: Some(0),
                initialized: true,
            }],
        });
        machine.control = Some(Control::Return(Value::Unit));
        machine
    }

    #[test]
    fn root_completion_preparation_is_exact_atomic_and_retryable() {
        for prefix in [0, 7] {
            let payload: Arc<[u8]> = Arc::from([1_u8, 2, 3]);
            let mut machine = root_driver(Value::Bytes(Arc::clone(&payload)));
            // Two authentication/field passes plus record retirement: 3 + 1.
            for allowance in [0, 3] {
                machine.instantiation_work = TypeWorkBudget::with_limit(prefix + allowance);
                machine.instantiation_work.charge(prefix).unwrap();
                machine.control = Some(Control::Return(Value::Unit));
                let RuntimeFailure::Report(report) = machine.run_loop().unwrap_err() else {
                    panic!("structured root preparation refusal");
                };
                let resource = report.primary.resource().unwrap();
                assert_eq!(resource.cause, ResourceFailureCause::WorkBudgetExhausted);
                assert_eq!(resource.phase, RuntimePhase::Cleanup);
                assert_eq!(resource.resource, RuntimeResource::WorkUnits);
                assert_eq!(resource.requested, Some(if allowance == 0 { 3 } else { 1 }));
                assert_eq!(resource.available, Some(0));
                assert!(
                    matches!(machine.frames.as_slice(), [Frame::RegionBoundary { records, .. }] if records[0].initialized)
                );
                assert!(machine.root_completion.is_none());
                assert_eq!(
                    Arc::strong_count(&payload),
                    2,
                    "refusal retains initialized fields"
                );
            }
            machine.instantiation_work = TypeWorkBudget::with_limit(prefix + 4);
            machine.instantiation_work.charge(prefix).unwrap();
            machine.control = Some(Control::Return(Value::Unit));
            let evaluation = machine.run_loop().unwrap();
            assert_eq!(machine.instantiation_work.used(), prefix + 4);
            assert!(machine.frames.is_empty() && machine.root_completion.is_none());
            assert_eq!(
                Arc::strong_count(&payload),
                2,
                "completion moves to the observation"
            );
            drop(evaluation);
            assert_eq!(Arc::strong_count(&payload), 1);
            for _ in 0..2 {
                let mut retry = root_driver(Value::Unit);
                retry.instantiation_work = TypeWorkBudget::with_limit(4);
                assert_eq!(retry.run_loop().unwrap().value.to_string(), "()");
                assert_eq!(retry.instantiation_work.used(), 4);
            }
        }
    }

    #[test]
    fn root_completion_rejects_forged_pair_owner_layout_and_duplicate_location() {
        for mutation in [
            "pair",
            "owner",
            "locator",
            "extent",
            "location",
            "cell",
            "duplicate",
        ] {
            let payload: Arc<[u8]> = Arc::from([1_u8, 2, 3]);
            let mut machine = root_driver(Value::Bytes(Arc::clone(&payload)));
            let Frame::RegionBoundary {
                release, records, ..
            } = &mut machine.frames[0]
            else {
                unreachable!()
            };
            match mutation {
                "pair" => {
                    *release = Value::RegionHostFunction {
                        owner: ActivationKey(10),
                        release: true,
                    }
                }
                "owner" => records[0].invocation.owner = ActivationKey(10),
                "locator" => records[0].locator = Address::new(core::ptr::null_mut()),
                "extent" => records[0].extent += 1,
                "location" => records[0].location = None,
                "cell" => {
                    machine.heap.push(HeapCell::Uninitialized);
                    records[0].location = Some(1);
                }
                "duplicate" => records.push(BackingRecord {
                    locator: records[0].locator.clone(),
                    extent: records[0].extent,
                    usable_bytes: records[0].usable_bytes,
                    alignment: records[0].alignment,
                    invocation: RegionInvocation {
                        owner: ActivationKey(9),
                        serial: 6,
                    },
                    location: Some(0),
                    initialized: true,
                }),
                _ => unreachable!(),
            }
            assert_eq!(
                machine.retain_root_completion(),
                Err(RuntimeFailure::InvalidControlState),
                "{mutation}"
            );
            assert!(machine.root_completion.is_none());
            assert!(
                matches!(machine.frames.as_slice(), [Frame::RegionBoundary { records, .. }] if records[0].initialized)
            );
            assert_eq!(Arc::strong_count(&payload), 2);
        }
    }

    #[test]
    fn root_completion_is_retained_by_evaluation_clones_until_the_last_owner() {
        let payload: Arc<[u8]> = Arc::from([1_u8, 2, 3]);
        let weak_payload = Arc::downgrade(&payload);
        let evaluation = root_driver(Value::Bytes(payload)).run().unwrap();
        let weak_heap = Arc::downgrade(&evaluation.heap);
        let clone = evaluation.clone();
        drop(evaluation);
        assert!(weak_heap.upgrade().is_some() && weak_payload.upgrade().is_some());
        drop(clone);
        assert!(weak_heap.upgrade().is_none() && weak_payload.upgrade().is_none());

        let payload: Arc<[u8]> = Arc::from([4_u8]);
        let weak = Arc::downgrade(&payload);
        let mut machine = root_driver(Value::Bytes(payload));
        machine.retain_root_completion().unwrap();
        let mut root = machine.root_completion.take().unwrap();
        root.close(&mut machine.heap);
        assert!(weak.upgrade().is_none());
        assert!(root.records.is_empty());
        assert!(matches!(machine.heap[0], HeapCell::Uninitialized));
        root.close(&mut machine.heap);
        assert!(
            root.records.is_empty(),
            "completion cannot retire the same backing twice"
        );
    }

    #[test]
    fn root_completion_is_disposed_if_the_outer_boundary_fails_before_observation() {
        let payload: Arc<[u8]> = Arc::from([1_u8, 2, 3]);
        let weak = Arc::downgrade(&payload);
        let mut machine = root_driver(Value::Bytes(payload));
        machine.retain_root_completion().unwrap();
        machine.frames.push(Frame::CloseCompletion);
        machine.control = Some(Control::Return(Value::Boolean(true)));
        assert_eq!(
            machine.run().unwrap_err(),
            RuntimeFailure::InvalidControlState
        );
        assert!(
            weak.upgrade().is_none(),
            "an unpublished owner cannot strand its fields/backing"
        );

        let mut machine = root_disposal_pressure_driver();
        machine.retain_root_completion().unwrap();
        machine.frames.push(Frame::CloseCompletion);
        machine.control = Some(Control::Return(Value::Boolean(true)));
        disposal::reset_growth_attempts();
        super::super::machine_test_hooks::FAIL_DISPOSAL_GROWTH.set(true);
        let RuntimeFailure::Report(report) = machine.run().unwrap_err() else {
            panic!("primary error with root teardown failure");
        };
        assert_eq!(
            report.primary.reason_code(),
            RuntimeFailure::InvalidControlState.reason_code()
        );
        let teardown = report.teardown.unwrap();
        assert_eq!(teardown.cause, ResourceFailureCause::AllocatorRefused);
        assert_eq!(teardown.phase, RuntimePhase::Teardown);
        assert_eq!(teardown.resource, RuntimeResource::EnvironmentDisposal);
        assert_eq!(report.cleanup, crate::eval::CleanupStatus::Incomplete);
        assert_eq!(disposal::growth_attempts(), 1);
    }

    fn root_disposal_pressure_driver() -> Machine<'static> {
        let mut machine = root_driver(Value::Unit);
        let template = Closure {
            parameter: crate::resolved::BinderId::new(1),
            body: machine.program.root(),
            program: machine.program.clone(),
            environment: Environment::new(),
            origin: Origin::Source(
                SourceFile::new("root-disposal", "()")
                    .unwrap()
                    .span(ByteRange::new(0, 2).unwrap())
                    .unwrap(),
            ),
        };
        let mut frontier = (0..512).map(|_| Environment::new()).collect::<Vec<_>>();
        while frontier.len() > 1 {
            let mut next = Vec::new();
            while let Some(right) = frontier.pop() {
                let left = frontier.pop().unwrap();
                let mut function = template.clone();
                function.environment = right;
                next.push(
                    left.extend(crate::resolved::BinderId::new(1), Value::Function(function))
                        .unwrap(),
                );
            }
            frontier = next;
        }
        let mut function = template;
        function.environment = frontier.pop().unwrap();
        let HeapCell::Tuple(fields) = &mut machine.heap[0] else {
            unreachable!()
        };
        fields[0] = Value::Function(function);
        machine
    }

    #[test]
    fn root_completion_disposal_failure_remains_visible_in_the_ambient_scope() {
        let machine = root_disposal_pressure_driver();
        let evaluation = machine.run().unwrap();
        let weak = Arc::downgrade(&evaluation.heap);
        let scope = disposal::Scope::enter();
        disposal::reset_growth_attempts();
        super::super::machine_test_hooks::FAIL_DISPOSAL_GROWTH.set(true);
        drop(evaluation);
        assert!(weak.upgrade().is_none());
        assert!(
            disposal::check().is_err(),
            "root disposal must not hide failure in a fresh Scope"
        );
        assert_eq!(disposal::growth_attempts(), 1);
        let RuntimeFailure::Report(report) = scope.finish(Ok::<_, RuntimeFailure>(())).unwrap_err()
        else {
            panic!("ambient teardown failure")
        };
        assert_eq!(
            report.primary.resource().unwrap().cause,
            ResourceFailureCause::AllocatorRefused
        );
    }

    fn prepared_driver() -> Machine<'static> {
        let source = SourceFile::new("region-driver.ash", "()").unwrap();
        let span = source.span(ByteRange::new(0, 2).unwrap()).unwrap();
        let mut builder = EffectCoreBuilder::with_effect_registry(Arc::new(
            crate::resolved::ResolvedRegistry::default(),
        ));
        let root = builder.unit(Type::Unit, Origin::Source(span)).unwrap();
        let program = validate_effect(builder.finish(root).unwrap(), &[&source]).unwrap();
        let mut machine = Machine::new_effect(&program);
        let key = ActivationKey(9);
        machine.frames.push(Frame::RegionBoundary {
            node: root,
            key,
            allocate: Value::Unit,
            release: Value::Unit,
            preceding: Value::Unit,
            records: Vec::new(),
        });
        machine.frames.push(Frame::RegionAllocated {
            segment: CapturedContinuation { frames: Vec::new() },
            invocation: RegionInvocation {
                owner: key,
                serial: 5,
            },
            registered: false,
        });
        machine
    }

    fn reply(
        machine: &mut Machine<'_>,
        pointer: *mut core::ffi::c_void,
        extent: usize,
        alignment: usize,
        serial: u64,
    ) -> Value {
        let location = machine.heap.len();
        machine.heap.push(HeapCell::Tuple(Box::new([
            Value::RegionRequest(RegionRequest {
                usable_bytes: 32,
                alignment: 8,
                invocation: Some(RegionInvocation {
                    owner: ActivationKey(9),
                    serial,
                }),
            }),
            Value::Address(Address::new(pointer)),
            Value::Integer(crate::integer::Integer::from_usize(extent)),
            Value::Integer(crate::integer::Integer::from_usize(alignment)),
        ])));
        Value::Location(location)
    }

    #[test]
    fn backing_registration_binds_one_pending_record_and_rejects_replay() {
        let mut memory = [0_u64; 8];
        let mut machine = prepared_driver();
        let reply = reply(&mut machine, memory.as_mut_ptr().cast(), 64, 8, 5);
        let storage = machine
            .register_region_backing(ActivationKey(9), reply.clone())
            .unwrap();
        let Value::RegionStorage(storage) = storage else {
            panic!("pending token");
        };
        machine.validate_region_storage(storage).unwrap();
        assert!(
            machine
                .register_region_backing(ActivationKey(9), reply)
                .is_err()
        );
        let Frame::RegionBoundary { records, .. } = &machine.frames[0] else {
            panic!("owner retained");
        };
        assert_eq!(records.len(), 1);
    }

    #[test]
    fn backing_registration_rejects_wrong_owner_invocation_and_layout() {
        let mut memory = [0_u64; 8];
        let pointer = memory.as_mut_ptr().cast();
        for (owner, serial, pointer, extent, alignment) in [
            (8, 5, pointer, 64, 8),
            (9, 6, pointer, 64, 8),
            (9, 5, pointer, 31, 8),
            (9, 5, pointer, 64, 4),
            (9, 5, pointer, 64, 3),
            (9, 5, core::ptr::null_mut(), 64, 8),
        ] {
            let mut machine = prepared_driver();
            let reply = reply(&mut machine, pointer, extent, alignment, serial);
            assert!(
                machine
                    .register_region_backing(ActivationKey(owner), reply)
                    .is_err()
            );
            let Frame::RegionBoundary { records, .. } = &machine.frames[0] else {
                panic!("owner retained");
            };
            assert!(records.is_empty());
        }
    }
    #[test]
    fn byte_initialization_consumes_actual_backing_atomically_and_rejects_replay() {
        fn allocated() -> (Machine<'static>, RegionStorage) {
            let mut machine = prepared_driver();
            let storage = machine
                .allocate_host_region_storage(
                    ActivationKey(9),
                    Value::RegionRequest(RegionRequest {
                        usable_bytes: 3,
                        alignment: 1,
                        invocation: Some(RegionInvocation {
                            owner: ActivationKey(9),
                            serial: 5,
                        }),
                    }),
                )
                .unwrap();
            let Value::RegionStorage(storage) = storage else {
                panic!("pending storage");
            };
            machine.instantiation_work = TypeWorkBudget::default();
            (machine, storage)
        }
        let (mut measured, token) = allocated();
        measured
            .initialize_region_bytes(token, b"hey", true)
            .unwrap();
        let required = measured.instantiation_work.used();
        for bad in [b"hi".as_slice(), &[255, 255, 255]] {
            let (mut machine, token) = allocated();
            assert!(machine.initialize_region_bytes(token, bad, true).is_err());
            let Frame::RegionBoundary { records, .. } = &machine.frames[0] else {
                unreachable!()
            };
            assert!(!records[0].initialized);
            assert!(
                matches!(&machine.heap[records[0].location.unwrap()],HeapCell::Bytes(bytes,0,false) if bytes.as_ref()==[0,0,0])
            );
        }
        for prefix in [0, 17] {
            let (mut machine, token) = allocated();
            machine.instantiation_work = TypeWorkBudget::with_limit(prefix + required - 1);
            machine.instantiation_work.charge(prefix).unwrap();
            assert!(
                machine
                    .initialize_region_bytes(token, b"hey", true)
                    .is_err()
            );
            let Frame::RegionBoundary { records, .. } = &machine.frames[0] else {
                unreachable!()
            };
            let location = records[0].location.unwrap();
            assert!(!records[0].initialized);
            let pointer = records[0].locator.as_ptr();
            assert!(
                matches!(&machine.heap[location],HeapCell::Bytes(bytes,0,false) if bytes.as_ref()==[0,0,0])
            );
            machine.instantiation_work = TypeWorkBudget::with_limit(prefix + required);
            machine.instantiation_work.charge(prefix).unwrap();
            let value = machine
                .initialize_region_bytes(token, b"hey", true)
                .unwrap();
            assert_eq!(machine.instantiation_work.used(), prefix + required);
            assert!(matches!(value,Value::Location(found) if found==location));
            let HeapCell::Bytes(bytes, 3, true) = &machine.heap[location] else {
                panic!("same byte backing");
            };
            assert_eq!(bytes.as_ref(), b"hey");
            assert_eq!(
                bytes.as_ptr().cast_mut().cast::<core::ffi::c_void>(),
                pointer
            );
            machine.instantiation_work = TypeWorkBudget::default();
            assert!(
                machine
                    .initialize_region_bytes(token, b"hey", true)
                    .is_err()
            );
        }
    }

    #[test]
    fn host_allocate_reserves_actual_typed_fields_before_initialization() {
        let mut machine = prepared_driver();
        let request = RegionRequest {
            usable_bytes: 2 * core::mem::size_of::<Value>(),
            alignment: core::mem::align_of::<Value>(),
            invocation: Some(RegionInvocation {
                owner: ActivationKey(9),
                serial: 5,
            }),
        };
        machine
            .return_from(
                Frame::ApplyArgument {
                    function: Value::RegionHostFunction {
                        owner: ActivationKey(9),
                        release: false,
                    },
                },
                Value::RegionRequest(request),
            )
            .unwrap();
        let Some(Control::Return(Value::RegionStorage(storage))) = machine.control.take() else {
            panic!("the fixed host provider must return one registered pending record");
        };
        machine.validate_region_storage(storage).unwrap();
        assert!(
            machine
                .heap
                .iter()
                .any(|cell| matches!(cell, HeapCell::Tuple(fields) if fields.len() == 2))
        );
    }
    #[test]
    fn source_tuple_backings_retire_with_their_owners_and_root_stays_observable() {
        let path =
            std::env::temp_dir().join(format!("ash-region-retirement-{}.ash", std::process::id()));
        std::fs::write(
            &path,
            concat!(
                "main : Unit -> (Int, Int)\nmain () = {\n",
                "let answer = region<R> outer {\nlet kept = region<S> inner {\n",
                "let local = (1, 2)\nlet ignored = match local {\n(a, b) => a + b\n}\n",
                "using outer {\n(20, 22)\n}\n}\nmatch kept {\n(a, b) => match (a + b) == 42 {\ntrue => 42\nfalse => 0\n}\n}\n}\n",
                "(answer, 1)\n}\n",
            ),
        )
        .unwrap();
        let compiled = crate::driver::compile_path(crate::driver::RunConfiguration {
            entry: path.clone(),
            roots: crate::module::ModuleRoots::empty(),
        });
        std::fs::remove_file(path).unwrap();
        let compiled = compiled.unwrap();
        let (program, _) = compiled.effect_build_input().unwrap();
        assert_eq!(
            program
                .nodes()
                .iter()
                .filter(|node| matches!(
                    node.kind,
                    EffectExprKind::Operation(EffectOperation::RegionTuple(_))
                ))
                .count(),
            3
        );
        let inner = program
            .nodes()
            .iter()
            .find_map(|node| match &node.kind {
                EffectExprKind::Operation(EffectOperation::Region(scope))
                    if !scope.entry && matches!(node.ty, Type::Tuple(_)) =>
                {
                    Some(scope)
                }
                _ => None,
            })
            .unwrap();
        let EffectExprKind::Pure(crate::core::PureExprKind::Computation(
            crate::core::PureComputation::Match(provider),
        )) = &program.node(inner.provider).unwrap().kind
        else {
            panic!("provider keeps its checked pair projection");
        };
        let [arm] = provider.arms() else {
            panic!("one provider pair");
        };
        let EffectExprKind::Pure(crate::core::PureExprKind::Computation(
            crate::core::PureComputation::Tuple(pair),
        )) = &program.node(arm.body()).unwrap().kind
        else {
            panic!("provider adapters remain an ordinary pair");
        };
        let adapters = pair
            .elements()
            .iter()
            .map(|field| {
                let (node, closure) =
                    crate::core::region::closure_initializer::<
                        crate::core::effect::EffectOperationFamily,
                    >(*field, |node| program.node(node).map(|node| &node.kind))
                    .unwrap();
                assert!(closure.code.function().is_some());
                node
            })
            .collect::<Vec<_>>();
        assert_eq!(
            adapters.len(),
            2,
            "inner allocate/release adapters are created under outer"
        );
        let evaluation = evaluate_effect(program).unwrap();
        assert_eq!(evaluation.value.to_string(), "(42, 1)");
        for node in program.nodes() {
            let EffectExprKind::Operation(EffectOperation::RegionTuple(tuple)) = &node.kind else {
                continue;
            };
            let positions = |child| {
                evaluation
                    .trace
                    .iter()
                    .enumerate()
                    .filter_map(|(position, event)| {
                        (*event == TraceEvent::Enter(child)).then_some(position)
                    })
                    .collect::<Vec<_>>()
            };
            let storage = positions(tuple.storage);
            assert_eq!(storage.len(), 1);
            let mut previous = None;
            for field in &tuple.fields {
                let field = positions(*field);
                assert_eq!(field.len(), 1, "each original operand runs once");
                assert!(previous.is_none_or(|position| position < field[0]));
                assert!(field[0] < storage[0], "fields precede the storage request");
                previous = Some(field[0]);
            }
        }
        for adapter in &adapters {
            assert_eq!(
                evaluation
                    .trace
                    .iter()
                    .filter(|event| **event == TraceEvent::Enter(*adapter))
                    .count(),
                1,
                "each provider closure is initialized once"
            );
        }
        let cells = evaluation.heap.cells_for_test();
        assert_eq!(
            cells
                .iter()
                .filter(|cell| matches!(cell, HeapCell::Uninitialized))
                .count(),
            2 + adapters.len(),
            "both tuple arrays and the inner provider's two outer-owned closure records retire"
        );
        let fields = cells
            .iter()
            .find_map(|cell| match cell {
                HeapCell::Tuple(fields)
                    if fields.len() == 2
                        && fields[0].to_string() == "42"
                        && fields[1].to_string() == "1" =>
                {
                    Some(fields)
                }
                _ => None,
            })
            .expect("root backing retained");
        assert_eq!(fields[0].to_string(), "42");
        assert_eq!(fields[1].to_string(), "1");
    }
    #[test]
    fn polymorphic_evidence_captures_have_no_persistent_host_environment() {
        let (program, _, _) = crate::core::validate::generic_cell_source_fixture_for_test(
            concat!(
                "type Box<A> = Box(A)\n",
                "interface Functor<F : Type -> Type> {\nmap<A, B> : (A -> B, F<A>) -> F<B>\n}\n",
                "impl Functor<Box> {\nmap (function, Box(value)) = Box(function(value))\n}\n",
                "to_bool : Int -> Bool\nto_bool value = value == 42\n",
                "to_int : Bool -> Int\nto_int true = 42\nto_int false = 0\n",
                "map_pair<F : Type -> Type> : (F<Int>, F<Bool>) -> (F<Bool>, F<Int>) where Functor<F>\n",
                "map_pair (numbers, flags) = (map((to_bool, numbers)), map((to_int, flags)))\n",
                "main : Unit -> (Box<Bool>, Box<Int>)\nmain () = map_pair((Box(42), Box(true)))\n",
            ),
            None,
        );
        let evaluation = evaluate_effect(&program).unwrap();
        assert_eq!(evaluation.value.to_string(), "(Box(true), Box(42))");
        for cell in evaluation.heap.cells_for_test() {
            let Some(fields) = cell.stored_fields() else {
                continue;
            };
            for value in fields {
                if let Value::Polymorphic {
                    abstraction,
                    environment,
                } = value
                {
                    let EffectExprKind::Pure(PureExprKind::Computation(
                        PureComputation::TypeAbstraction(metadata),
                    )) = &program.node(*abstraction).unwrap().kind
                    else {
                        panic!("retained abstraction");
                    };
                    assert!(
                        environment.is_empty(),
                        "a supplied capture slot hides {} host environment entries; abstraction={abstraction:?}; body={:?}",
                        environment.len(),
                        program.node(metadata.body()).unwrap().kind
                    );
                }
            }
        }
    }

    #[test]
    fn prerequisite_adapter_captures_have_no_persistent_host_environment() {
        let source = concat!(
            "type Option<A> =\nNone\n| Some(A)\n",
            "interface Score<A> {\nscore<X> : (A, X) -> Int\n}\n",
            "impl Score<Int> {\nscore (value, ignored) = value\n}\n",
            "impl Score<Option<A>> where Score<A> {\nscore (None, ignored) = 4\n",
            "score (Some(value), ignored) = {\nlet empty : Option<A> = None\n",
            "score((empty, ignored)) * 10 + score((value, ignored))\n}\n}\n",
            "forward<A> : A -> Int where Score<A>\nforward value = score((value, true))\n",
            "main : Unit -> Int\nmain () = forward(Some(2))\n",
        );
        let (program, _, _) =
            crate::core::validate::generic_cell_source_fixture_for_test(source, None);
        let evaluation = evaluate_effect(&program).unwrap();
        assert_eq!(evaluation.value.to_string(), "42");
        for cell in evaluation.heap.cells_for_test() {
            let Some(fields) = cell.stored_fields() else {
                continue;
            };
            for value in fields {
                if let Value::Polymorphic {
                    abstraction,
                    environment,
                } = value
                {
                    assert!(
                        environment.is_empty(),
                        "deferred adapter {abstraction:?} hides {} term captures",
                        environment.len()
                    );
                }
            }
        }
    }

    #[test]
    fn deferred_method_prefix_finishes_before_source_argument_discard() {
        let source = concat!(
            "type Option<A> =\nNone\n| Some(A)\ninterface Score<A> {\nscore<X> : (A, X) -> Int\n}\n",
            "impl Score<Int> {\nscore (value, ignored) = value\n}\nimpl Score<Option<A>> where Score<A> {\nscore (None, ignored) = 4\nscore (Some(value), ignored) = {\nlet empty : Option<A> = None\nscore((empty, ignored)) * 10 + score((value, ignored))\n}\n}\n",
            "effect Argument {\nget : Unit -> (Option<Int>, Bool)\n}\nmain : Unit -> Int\nmain () = region<R> r {\nhandle score(perform Argument.get ()) with Argument {\nget ignored => {\nlet done = discard\n42\n}\n}\n}\n",
        );
        let (program, _, _) =
            crate::core::validate::generic_cell_source_fixture_for_test(source, None);
        let argument = program
            .registry()
            .effects()
            .iter()
            .find(|effect| effect.spelling == "Argument")
            .unwrap()
            .id;
        let region = program
            .nodes()
            .iter()
            .find_map(|node| match &node.kind {
                EffectExprKind::Operation(EffectOperation::Region(region)) if !region.entry => {
                    Some(region)
                }
                _ => None,
            })
            .unwrap();
        let evaluation = evaluate_effect(&program).unwrap();
        assert_eq!(evaluation.value.to_string(), "42");
        let start = evaluation
            .trace
            .iter()
            .position(|event| *event == TraceEvent::Enter(region.body))
            .unwrap();
        let argument = evaluation.trace.iter().position(|event| {
            let TraceEvent::Enter(node) = *event;
            matches!(&program.node(node).unwrap().kind, EffectExprKind::Operation(EffectOperation::Request(request)) if request.operation().owner() == argument)
        }).unwrap();
        let records = evaluation.trace[start..argument]
            .iter()
            .filter_map(|event| {
                let TraceEvent::Enter(node) = *event;
                let EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) =
                    &program.node(node).unwrap().kind
                else {
                    return None;
                };
                Some(closure)
            })
            .collect::<Vec<_>>();
        assert_eq!(
            records.len(),
            2,
            "adapter capture record and prerequisite-produced function finish before the source argument"
        );
        assert!(matches!(
            records[0].code,
            crate::core::region::RegionClosureCode::Adapter { .. }
        ));
        let function = records[1]
            .code
            .function()
            .expect("prerequisite term application creates the actual method function");
        assert!(
            !evaluation
                .trace
                .contains(&TraceEvent::Enter(function.body())),
            "argument discard never enters the source method body"
        );
        assert_eq!(
            evaluation
                .effect_trace()
                .iter()
                .filter(|event| matches!(event, EffectTraceEvent::Discard(_)))
                .count(),
            1
        );
    }

    #[test]
    fn mixed_recursive_group_creates_functions_before_guarded_data_in_member_order() {
        let (program, _, _) = crate::core::validate::generic_cell_source_fixture_for_test(
            concat!(
                "type Stream = Next(Int, Unit -> Int, Unit -> Int)\n",
                "main : Unit -> Bool\nmain () = region<R> r {\n",
                "let rec first : Stream = Next(42, read, again)\n",
                "and read : Unit -> Int = fn(ignored) {\nmatch first {\nNext(value, ignored, also_ignored) => value\n}\n}\n",
                "and again : Unit -> Int = fn(ignored) {\nread ()\n}\nlet alias = first\n",
                "match alias {\nNext(value, head, tail) => match (head ()) == 42 {\ntrue => (tail ()) == value\nfalse => false\n}\n}\n}\n",
            ),
            None,
        );
        let group = program
            .nodes()
            .iter()
            .find_map(|node| match &node.kind {
                EffectExprKind::Pure(crate::core::PureExprKind::Computation(
                    crate::core::PureComputation::RecursiveBind(group),
                )) if group.members().len() == 3
                    && matches!(group.members()[0].binder().ty(), Type::Nominal(_)) =>
                {
                    Some(group)
                }
                _ => None,
            })
            .unwrap();
        let functions = group
            .members()
            .iter()
            .filter_map(|member| {
                crate::core::region::closure_initializer::<
                        crate::core::effect::EffectOperationFamily,
                    >(member.initializer(), |node| {
                        program.node(node).map(|node| &node.kind)
                    })
                    .map(|(node, _)| node)
            })
            .collect::<Vec<_>>();
        assert_eq!(functions.len(), 2);
        let evaluation = evaluate_effect(&program).unwrap();
        assert_eq!(evaluation.value.to_string(), "true");
        let entered = |node| {
            evaluation
                .trace
                .iter()
                .enumerate()
                .filter_map(|(index, event)| (*event == TraceEvent::Enter(node)).then_some(index))
                .collect::<Vec<_>>()
        };
        let first = entered(functions[0]);
        let second = entered(functions[1]);
        let data = entered(group.members()[0].initializer());
        assert_eq!(first.len(), 1);
        assert_eq!(second.len(), 1);
        assert_eq!(data.len(), 1);
        assert!(
            first[0] < second[0] && second[0] < data[0],
            "functions materialize once in member order before the first guarded data initializer"
        );
    }

    #[test]
    fn type_views_share_records_and_dynamic_function_creation_is_fresh() {
        let (program, _, _) = crate::core::validate::generic_cell_source_fixture_for_test(
            "main : Unit -> Int\nmain () = {\nlet identity = fn(value) {\nvalue\n}\nlet answer = identity 42\nmatch identity true {\ntrue => answer\nfalse => 0\n}\n}\n",
            None,
        );
        let evaluation = evaluate_effect(&program).unwrap();
        assert_eq!(evaluation.value.to_string(), "42");
        let identity = program
            .nodes()
            .iter()
            .enumerate()
            .find_map(|(index, node)| {
                let EffectExprKind::Operation(EffectOperation::RegionClosure(closure)) = &node.kind
                else {
                    return None;
                };
                let EffectExprKind::Pure(PureExprKind::Variable(variable)) =
                    &program.node(closure.code.body()).unwrap().kind
                else {
                    return None;
                };
                closure
                    .code
                    .function()
                    .is_some_and(|function| {
                        variable.binder() == function.parameter().id()
                            && matches!(function.parameter().ty(), Type::Variable(_))
                    })
                    .then_some(index)
            })
            .expect("generic identity closure");
        assert_eq!(evaluation.heap.cells_for_test().iter().filter(|cell| {
            cell.stored_fields().is_some_and(|fields| matches!(fields.first(), Some(Value::ClosureCode(code)) if code.node.value() as usize == identity))
        }).count(), 1, "both type views share one created record");

        let (program, _, _) = crate::core::validate::generic_cell_source_fixture_for_test(
            "main : Unit -> ((Unit -> Int), (Unit -> Int))\nmain () = {\nlet make : Unit -> (Unit -> Int) = fn(ignored) {\nlet rec read : Unit -> Int = fn(ignored) {\n42\n}\nread\n}\n(make (), make ())\n}\n",
            None,
        );
        let evaluation = evaluate_effect(&program).unwrap();
        let cells = evaluation.heap.cells_for_test();
        let fields = cells
            .iter()
            .filter_map(HeapCell::tuple_fields)
            .find(|fields| {
                fields.len() == 2
                    && fields
                        .iter()
                        .all(|value| matches!(value, Value::RegionFunction(_) | Value::Location(_)))
            })
            .expect("result tuple containing both stored callables");
        let record = |value: &Value| match value {
            Value::RegionFunction(function) => function.record,
            Value::Location(record) => {
                packed_tuple_location(cells, *record, &mut TypeWorkBudget::unbounded()).unwrap()
            }
            _ => panic!("stored callable view"),
        };
        assert_ne!(
            record(&fields[0]),
            record(&fields[1]),
            "each dynamic group entry creates fresh records"
        );
    }

    #[test]
    fn callable_reads_captures_from_the_supplied_record_slots() {
        let path = std::env::temp_dir().join(format!(
            "ash-region-capture-slots-{}.ash",
            std::process::id()
        ));
        std::fs::write(&path, concat!(
            "main : Unit -> (Unit -> Int)\nmain () = {\n",
            "let captured = 42\nlet callback : Unit -> Int = fn(ignored) {\ncaptured\n}\ncallback\n}\n",
        )).unwrap();
        let compiled = crate::driver::compile_path(crate::driver::RunConfiguration {
            entry: path.clone(),
            roots: crate::module::ModuleRoots::empty(),
        })
        .unwrap();
        std::fs::remove_file(path).unwrap();
        let (program, _) = compiled.effect_build_input().unwrap();
        let mut evaluation = evaluate_effect(program).unwrap();
        let Value::RegionFunction(function) = &evaluation.value else {
            panic!("stored callable");
        };
        let record = function.record;
        let heap = Arc::get_mut(&mut evaluation.heap).expect("unique observation owner");
        let root_completion = heap.take_root_completion_for_test();
        let cells = heap.cells_mut_for_test();
        let HeapCell::Tuple(fields) = &mut cells[record] else {
            panic!("supplied Value slots");
        };
        assert_eq!(fields.len(), 2);
        assert!(matches!(&fields[0], Value::ClosureCode(_)));
        assert!(matches!(&fields[1], Value::SmallInteger(42)));
        // A retained host Environment would still return 42. The shared
        // callable reader must obtain the actual captured Value from its slot.
        fields[1] = Value::SmallInteger(43);
        let mut machine = Machine::new_effect(program);
        machine.heap = cells
            .iter_mut()
            .map(|cell| std::mem::replace(cell, HeapCell::Uninitialized))
            .collect();
        machine.root_completion = root_completion;
        let callable = machine.read_callable(&evaluation.value).unwrap();
        machine.control = Some(Control::Evaluate(callable.body, callable.environment));
        assert_eq!(machine.run().unwrap().value.to_string(), "43");
    }

    #[test]
    fn rust_owned_native_fields_are_released_before_provider_call_and_survive_short_work() {
        use crate::eval::{NativeTupleAdapter, NativeTupleStorage};
        use std::cell::RefCell;
        thread_local! { static HELD: RefCell<Vec<Value>> = const { RefCell::new(Vec::new()) }; }
        // A safe test double observes Rust ownership only. The generated-host
        // test separately checks actual address initialization and reads.
        fn initialize(_: &mut NativeTupleStorage, values: Vec<Value>) {
            HELD.with(|held| {
                assert!(held.borrow().is_empty());
                *held.borrow_mut() = values;
            });
        }
        fn fields(_: &NativeTupleStorage) -> &[Value] {
            &[Value::Unit, Value::Unit]
        }
        fn drop_fields(_: &mut NativeTupleStorage) {
            HELD.with(|held| drop(std::mem::take(&mut *held.borrow_mut())));
        }
        let adapter = NativeTupleAdapter {
            initialize,
            fields,
            drop_fields,
            copy_bytes: |_, _| {},
            bytes: |_| &[],
        };
        let (program, _, _) = crate::core::validate::generic_cell_source_fixture_for_test(
            "main : Unit -> Unit\nmain () = region<R> owner {\n()\n}\n",
            None,
        );
        let mut pending = vec![program.root()];
        let node = loop {
            let id = pending.pop().expect("declared region");
            let kind = &program.node(id).unwrap().kind;
            if matches!(kind, EffectExprKind::Operation(EffectOperation::Region(scope)) if !scope.entry)
            {
                break id;
            }
            pending.extend((0..kind.child_count()).filter_map(|index| kind.child_at(index)));
        };
        for short in [true, false] {
            let bytes: Arc<[u8]> = Arc::from([1_u8, 2, 3]);
            let mut memory = [0_u128; 256];
            let pointer = memory.as_mut_ptr().cast();
            let fields = NativeTupleStorage::initialize(
                Address::new(pointer),
                vec![Value::Bytes(Arc::clone(&bytes)), Value::Unit],
                adapter,
            );
            let mut machine = Machine::new_effect(&program);
            machine.heap.push(HeapCell::NativeTuple(fields));
            machine.frames.reserve(2);
            if short {
                machine.instantiation_work = TypeWorkBudget::with_limit(0);
            }
            let result = machine.return_from(
                Frame::RegionBoundary {
                    node,
                    key: ActivationKey(9),
                    allocate: Value::Unit,
                    release: Value::Unit,
                    preceding: Value::Unit,
                    records: vec![BackingRecord {
                        locator: Address::new(pointer),
                        extent: 4096,
                        usable_bytes: 2 * core::mem::size_of::<Value>(),
                        alignment: 16,
                        invocation: RegionInvocation {
                            owner: ActivationKey(9),
                            serial: 5,
                        },
                        location: Some(0),
                        initialized: true,
                    }],
                },
                Value::Unit,
            );
            assert!(
                matches!(machine.frames.last(), Some(Frame::ApplyArgument { .. })),
                "provider call remains pending in its owned frame"
            );
            let Frame::RegionCompletion { records, .. } = &machine.frames[0] else {
                panic!("completion retained")
            };
            if short {
                let RuntimeFailure::Report(report) = result.unwrap_err() else {
                    panic!("work report")
                };
                assert_eq!(
                    report.primary.resource().unwrap().cause,
                    ResourceFailureCause::WorkBudgetExhausted
                );
                assert!(records[0].initialized);
                assert_eq!(Arc::strong_count(&bytes), 2);
                assert!(matches!(machine.heap[0], HeapCell::NativeTuple(_)));
            } else {
                result.unwrap();
                assert!(!records[0].initialized);
                assert_eq!(
                    Arc::strong_count(&bytes),
                    1,
                    "Rust-owned field was released before invoking provider"
                );
                assert!(matches!(machine.heap[0], HeapCell::Uninitialized));
            }
            drop(machine);
            assert_eq!(Arc::strong_count(&bytes), 1);
        }
    }

    #[test]
    fn native_initializer_uses_saved_request_not_larger_backing_capacity() {
        let mut machine = prepared_driver();
        let mut memory = [0_u128; 256];
        let storage = machine
            .register_pending_backing(BackingRecord {
                locator: Address::new(memory.as_mut_ptr().cast()),
                extent: 4096,
                usable_bytes: core::mem::size_of::<Value>(),
                alignment: 16,
                invocation: RegionInvocation {
                    owner: ActivationKey(9),
                    serial: 5,
                },
                location: None,
                initialized: false,
            })
            .unwrap();
        let Value::RegionStorage(storage) = storage else {
            panic!("pending token")
        };
        assert_eq!(
            machine
                .initialize_region_tuple(storage, vec![Value::Unit, Value::Unit])
                .unwrap_err(),
            RuntimeFailure::InvalidControlState
        );
        let Frame::RegionBoundary { records, .. } = &machine.frames[0] else {
            panic!("owner retained")
        };
        assert!(!records[0].initialized);
        assert!(records[0].location.is_none());
    }

    #[test]
    fn close_frame_reservation_failure_keeps_the_owner_and_backing() {
        let program = super::super::tests::effect_program(
            "main : Unit -> Unit\nmain () = region<R> owner {\n()\n}\n",
        );
        let mut pending = vec![program.root()];
        let node = loop {
            let id = pending.pop().expect("declared owner");
            let kind = &program.node(id).unwrap().kind;
            if matches!(kind, EffectExprKind::Operation(EffectOperation::Region(scope)) if !scope.entry)
            {
                break id;
            }
            pending.extend((0..kind.child_count()).filter_map(|index| kind.child_at(index)));
        };
        let mut machine = Machine::new_effect(&program);
        machine.frames.push(Frame::RegionBoundary {
            node,
            key: ActivationKey(9),
            allocate: Value::Unit,
            release: Value::Unit,
            preceding: Value::Unit,
            records: Vec::new(),
        });
        machine.frames.push(Frame::RegionAllocated {
            segment: CapturedContinuation { frames: Vec::new() },
            invocation: RegionInvocation {
                owner: ActivationKey(9),
                serial: 5,
            },
            registered: false,
        });
        let storage = machine
            .allocate_host_region_storage(
                ActivationKey(9),
                Value::RegionRequest(RegionRequest {
                    usable_bytes: 2 * core::mem::size_of::<Value>(),
                    alignment: core::mem::align_of::<Value>(),
                    invocation: Some(RegionInvocation {
                        owner: ActivationKey(9),
                        serial: 5,
                    }),
                }),
            )
            .unwrap();
        assert!(matches!(storage, Value::RegionStorage(_)));
        machine.frames.pop();
        machine.control = Some(Control::Return(Value::Unit));
        machine_test_hooks::FAIL_CONTROL_RESERVATION
            .set(Some(ResourceFailureCause::AllocatorRefused));
        let failure = machine.run_loop().unwrap_err();
        machine_test_hooks::reset();
        let RuntimeFailure::Report(report) = failure else {
            panic!("resource failure report");
        };
        assert_eq!(
            report.primary.resource().unwrap().cause,
            ResourceFailureCause::AllocatorRefused
        );
        assert!(
            matches!(machine.frames.as_slice(), [Frame::RegionBoundary { key, records, .. }]
            if *key == ActivationKey(9) && records.len() == 1)
        );
        assert!(
            machine
                .heap
                .iter()
                .any(|cell| matches!(cell, HeapCell::Tuple(fields) if fields.len() == 2))
        );
    }
}
