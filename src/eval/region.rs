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

impl Machine<'_> {
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

    #[allow(
        clippy::too_many_arguments,
        reason = "one explicit tuple initializer frame is moved through the existing machine"
    )]
    pub(super) fn return_region_tuple(
        &mut self,
        node: NodeId,
        environment: Environment,
        mut context: Option<ActivationKey>,
        next: usize,
        mut fields: Vec<Value>,
        value: Value,
    ) -> Result<(), RuntimeFailure> {
        let tuple = self
            .region_tuple(node)
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let following = if next == 0 {
            let Value::RegionView(owner) = value else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            context = Some(owner);
            tuple.fields.first().copied().or(Some(tuple.storage))
        } else if next <= tuple.fields.len() {
            fields.push(value);
            Some(tuple.fields.get(next).copied().unwrap_or(tuple.storage))
        } else {
            let Value::RegionStorage(storage) = value else {
                return Err(RuntimeFailure::InvalidControlState);
            };
            if Some(storage.invocation.owner) != context {
                return Err(RuntimeFailure::InvalidControlState);
            }
            if let Some(constructor) = tuple.constructor {
                fields.insert(0, Value::ConstructorTag(constructor));
            }
            let initialized = self.initialize_region_tuple(storage, fields)?;
            self.control = Some(Control::Return(initialized));
            return Ok(());
        };
        if let Some(following) = following {
            self.frames.push(Frame::RegionTuple {
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
        if let Some(tuple) = self.region_tuple(node) {
            let (context, count) = (
                tuple.context,
                tuple.fields.len() + usize::from(tuple.constructor.is_some()),
            );
            let mut fields = Vec::new();
            reserve_control(&mut fields, count, RuntimeResource::HeapCells, true)?;
            reserve_control(&mut self.frames, 1, RuntimeResource::FrameStorage, false)?;
            self.frames.push(Frame::RegionTuple {
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
        let retained = self
            .captured_cells
            .checked_add(self.frames.len() - index - 1)
            .filter(|count| *count <= self.capture_limit)
            .ok_or(RuntimeFailure::CapturedControlCapacity)?;
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
        // Root observation ordering remains the separate entry completion work.
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
            let fields = record
                .location
                .and_then(|location| self.heap.get(location))
                .and_then(HeapCell::stored_fields)
                .ok_or(RuntimeFailure::InvalidControlState)?;
            cells = cells
                .checked_add(fields.len())
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
            Value::Integer(extent),
            Value::Integer(alignment),
        ] = fields.as_ref()
        else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let invocation = request
            .invocation
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let extent = extent
            .to_usize()
            .ok_or(RuntimeFailure::InvalidControlState)?;
        let alignment = alignment
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
                "using outer {\n(20, 22)\n}\n}\nmatch kept {\n(a, b) => a + b\n}\n}\n",
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
        let cells = evaluation.heap.cells_for_test();
        assert_eq!(
            cells
                .iter()
                .filter(|cell| matches!(cell, HeapCell::Uninitialized))
                .count(),
            2,
            "both declared owners retire their supplied arrays"
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
        let mut machine = prepared_driver();
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
