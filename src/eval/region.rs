//! Region ownership and target-directed service at its structural owner frame.
use super::*;
use crate::eval::value::{Address, RegionInvocation, RegionStorage};

/// Registration facts only. Physical validity and isolation remain the binding
/// module's assumptions; initialization must consume the pending token.
#[derive(Debug)]
pub(super) struct BackingRecord {
    pub(super) locator: Address,
    pub(super) extent: usize,
    pub(super) alignment: usize,
    pub(super) invocation: RegionInvocation,
}

impl Machine<'_> {
    fn region_scope(&self, node: NodeId) -> Option<&crate::core::region::RegionScopeNode> {
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

    pub(super) fn enter_region(
        &mut self,
        node: NodeId,
        environment: &Environment,
    ) -> Result<bool, RuntimeFailure> {
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
        let Some(HeapCell::Tuple(fields)) = self.heap.get(location) else {
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

    pub(super) fn register_region_backing(
        &mut self,
        owner: ActivationKey,
        value: Value,
    ) -> Result<Value, RuntimeFailure> {
        let Value::Location(location) = value else {
            return Err(RuntimeFailure::InvalidControlState);
        };
        let location = packed_tuple_location(&self.heap, location, &mut self.instantiation_work)?;
        let Some(HeapCell::Tuple(fields)) = self.heap.get(location) else {
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
        charge_effect_work(
            &mut self.instantiation_work,
            self.frames.len(),
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
        records.push(BackingRecord {
            locator,
            extent,
            alignment,
            invocation,
        });
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
}
