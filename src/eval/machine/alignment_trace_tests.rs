//! Opt-in, pre-step observations of the actual evaluator for TASK-0032.
//! Frame vectors retain Rust's outermost-first order, including captured vectors.
//! Environment table indices are observer references, not Ash binder identities.
//! Unsupported observations stop the observer, not evaluation; failures retain
//! the observed prefix and do not establish transition atomicity or simulation.
//! Encountered arithmetic frames, general data, polymorphic values/frames, hooks,
//! native buffers and foreign closure arenas are outside this observer. This is
//! not a static fragment-membership checker. Normalized copies use comparison
//! labels for modules; they are never supplied back to Core or evaluation.

use super::*;
use crate::source::{GeneratedReason, Origin, SourceId, Span};
use crate::types::{Type, TypeVariableId};
use std::collections::HashMap;
use std::sync::Mutex;

#[derive(Clone, Debug, Eq, PartialEq)]
struct NodeReference {
    raw: Option<NodeId>,
    original: u32,
}
impl From<NodeId> for NodeReference {
    fn from(raw: NodeId) -> Self {
        Self {
            original: raw.value(),
            raw: Some(raw),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SpanRecord {
    raw: Option<Span>,
    source_slot: usize,
    start: u32,
    stop: u32,
}
#[derive(Clone, Debug, Eq, PartialEq)]
enum OriginTree {
    Source(SpanRecord),
    Generated {
        cause: Box<Self>,
        reason: GeneratedReason,
    },
    Related {
        primary: Box<Self>,
        related: Vec<SpanRecord>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct InstantiationRecord(Vec<(TypeVariableId, u32)>);
#[derive(Clone, Debug, Eq, PartialEq)]
struct EnvironmentRecord {
    head: Option<usize>,
    len: usize,
    instantiation: InstantiationRecord,
}
#[derive(Clone, Debug, Eq, PartialEq)]
struct EntryRecord {
    kind: EntryKind,
    parent: Option<usize>,
    visible_len: usize,
    instantiation: InstantiationRecord,
}
#[derive(Clone, Debug, Eq, PartialEq)]
enum EntryKind {
    Binding {
        binder: BinderId,
        value: ValueRecord,
    },
    Recursive {
        members: Vec<FunctionTemplate>,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
struct FunctionTemplate {
    binder: BinderId,
    parameter: BinderId,
    body: NodeReference,
    origin: OriginTree,
    // Polymorphic and data templates are rejected before any field is erased.
}
#[derive(Clone, Debug, Eq, PartialEq)]
enum ValueRecord {
    Integer(crate::integer::Integer),
    Boolean(bool),
    Unit,
    Handle(u32),
    Location(usize),
    Closure {
        parameter: BinderId,
        body: NodeReference,
        program_root: NodeReference,
        program_nodes: usize,
        environment: EnvironmentRecord,
        origin: OriginTree,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
enum HeapRecord {
    // These preserve raw initialization/alias states; the fixture uses binary tuples.
    Uninitialized,
    Alias(usize),
    Pair(Box<[ValueRecord; 2]>),
}
#[derive(Clone, Debug, Eq, PartialEq)]
struct BinderRecord {
    id: BinderId,
    ty: Type,
    origin: OriginTree,
}
#[derive(Clone, Debug, Eq, PartialEq)]
enum PatternKind {
    Unit,
    Boolean(bool),
    Binder(BinderRecord),
}
#[derive(Clone, Debug, Eq, PartialEq)]
struct PatternRecord {
    ty: Type,
    origin: OriginTree,
    kind: PatternKind,
}
#[derive(Clone, Debug, Eq, PartialEq)]
struct ArmRecord {
    pattern: PatternRecord,
    body: NodeReference,
    origin: OriginTree,
}
#[derive(Clone, Debug, Eq, PartialEq)]
enum FrameRecord {
    CloseCompletion,
    CleanupBoundary {
        action: NodeReference,
        environment: EnvironmentRecord,
    },
    CleanupCompletion {
        saved: ValueRecord,
    },
    ResourceInitializer {
        node: NodeReference,
        environment: EnvironmentRecord,
    },
    ResourceBoundary {
        node: NodeReference,
        key: u32,
        payload: crate::integer::Integer,
    },
    Bind {
        binder: BinderId,
        body: NodeReference,
        environment: EnvironmentRecord,
    },
    ApplyFunction {
        argument: NodeReference,
        caller_environment: EnvironmentRecord,
    },
    ApplyArgument {
        function: ValueRecord,
    },
    Tuple {
        elements: Vec<NodeReference>,
        next: usize,
        values: Vec<ValueRecord>,
        environment: EnvironmentRecord,
    },
    Match {
        arms: Vec<ArmRecord>,
        environment: EnvironmentRecord,
    },
    HandlerBoundary {
        node: NodeReference,
        effect: EffectInstance,
        environment: EnvironmentRecord,
    },
    Request {
        node: NodeReference,
        effect: EffectInstance,
        instantiation: InstantiationRecord,
    },
    Resume {
        node: NodeReference,
    },
    ClauseBoundary {
        handler: HandlerId,
        owner: ResumeId,
        continuation: Option<Vec<Self>>,
    },
}
#[derive(Clone, Debug, Eq, PartialEq)]
enum ControlRecord {
    Evaluate(NodeReference, EnvironmentRecord),
    Return(ValueRecord),
    Discard(HandlerId, ResumeId),
}
#[derive(Clone, Debug, Eq, PartialEq)]
struct Snapshot {
    control: ControlRecord,
    frames: Vec<FrameRecord>,
    environments: Vec<EntryRecord>,
    heap: Vec<HeapRecord>,
    next_activation: u32,
    captured_cells: usize,
    live_resources: usize,
    live_cleanups: usize,
    live_registrations: usize,
    next_registration: u32,
    max_frame_depth: usize,
    capture_limit: usize,
    resource_limit: usize,
    cleanup_limit: usize,
    registration_limit: usize,
    work_used: usize,
    work_remaining: usize,
    // Only normalized copies populate these comparison module labels.
    modules: Vec<(String, u32)>,
    entered: Vec<NodeReference>,
    effects: Vec<EffectTraceEvent>,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SnapshotError {
    MissingControl,
    MissingNode,
    MissingSource,
    UnsupportedInstantiation,
    UnsupportedType,
    UnsupportedValue,
    ForeignProgram,
    UnsupportedPattern,
    UnsupportedFrame,
    NativeBuffer,
    Registration,
    UnsupportedHeap,
    DepthLimit,
}
#[derive(Debug)]
pub(super) struct Trace {
    snapshots: Vec<Snapshot>,
    rejected: Option<SnapshotError>,
    sources: HashMap<SourceId, usize>,
}
pub(super) type SharedTrace = Arc<Mutex<Trace>>;

pub(super) fn capture(machine: &Machine, trace: &SharedTrace) {
    let mut trace = trace.lock().expect("observer mutex");
    if trace.rejected.is_some() {
        return;
    }
    match Builder::snapshot(machine, &trace.sources) {
        Ok(snapshot) => trace.snapshots.push(snapshot),
        Err(error) => trace.rejected = Some(error),
    }
}

struct Builder<'a> {
    machine: &'a Machine,
    sources: &'a HashMap<SourceId, usize>,
    entries: Vec<Option<EntryRecord>>,
    references: HashMap<*const EnvironmentEntry, usize>,
}
impl<'a> Builder<'a> {
    fn snapshot(
        machine: &'a Machine,
        sources: &'a HashMap<SourceId, usize>,
    ) -> Result<Snapshot, SnapshotError> {
        let mut builder = Self {
            machine,
            sources,
            entries: Vec::new(),
            references: HashMap::new(),
        };
        let control = match machine
            .control
            .as_ref()
            .ok_or(SnapshotError::MissingControl)?
        {
            Control::Evaluate(node, environment) => {
                ControlRecord::Evaluate((*node).into(), builder.environment(environment, 0)?)
            }
            Control::Return(value) => ControlRecord::Return(builder.value(value, 0)?),
            Control::Discard(handler, owner) => ControlRecord::Discard(*handler, *owner),
        };
        let frames = builder.frames(&machine.frames, 0)?;
        let heap = machine
            .heap
            .iter()
            .map(|cell| match cell {
                HeapCell::Uninitialized => Ok(HeapRecord::Uninitialized),
                HeapCell::Alias(location) => Ok(HeapRecord::Alias(*location)),
                HeapCell::Tuple(elements) => match elements.as_ref() {
                    [left, right] => Ok(HeapRecord::Pair(Box::new([
                        builder.value(left, 0)?,
                        builder.value(right, 0)?,
                    ]))),
                    _ => Err(SnapshotError::UnsupportedHeap),
                },
                HeapCell::Constructor(..) => Err(SnapshotError::UnsupportedHeap),
            })
            .collect::<Result<_, _>>()?;
        Ok(Snapshot {
            control,
            frames,
            heap,
            environments: builder
                .entries
                .into_iter()
                .map(|entry| entry.expect("entry filled before snapshot publication"))
                .collect(),
            next_activation: machine.next_activation,
            captured_cells: machine.captured_cells,
            live_resources: machine.live_resources,
            live_cleanups: machine.live_cleanups,
            live_registrations: machine.live_registrations,
            next_registration: machine.next_registration,
            max_frame_depth: machine.max_frame_depth,
            capture_limit: machine.capture_limit,
            resource_limit: machine.resource_limit,
            cleanup_limit: machine.cleanup_limit,
            registration_limit: machine.registration_limit,
            work_used: machine.instantiation_work.used(),
            work_remaining: machine.instantiation_work.remaining(),
            modules: Vec::new(),
            entered: machine
                .trace
                .iter()
                .map(|TraceEvent::Enter(node)| (*node).into())
                .collect(),
            effects: machine.effect_trace.clone().unwrap_or_default(),
        })
    }
    fn depth(depth: usize) -> Result<(), SnapshotError> {
        if depth > 256 {
            Err(SnapshotError::DepthLimit)
        } else {
            Ok(())
        }
    }
    fn span(&self, span: Span) -> Result<SpanRecord, SnapshotError> {
        Ok(SpanRecord {
            raw: Some(span),
            source_slot: *self
                .sources
                .get(&span.source())
                .ok_or(SnapshotError::MissingSource)?,
            start: span.range().start(),
            stop: span.range().end(),
        })
    }
    fn origin(&self, origin: &Origin, depth: usize) -> Result<OriginTree, SnapshotError> {
        Self::depth(depth)?;
        Ok(match origin {
            Origin::Source(span) => OriginTree::Source(self.span(*span)?),
            Origin::Generated { cause, reason } => OriginTree::Generated {
                cause: Box::new(self.origin(cause, depth + 1)?),
                reason: *reason,
            },
            Origin::Related { primary, related } => OriginTree::Related {
                primary: Box::new(self.origin(primary, depth + 1)?),
                related: related
                    .iter()
                    .map(|span| self.span(*span))
                    .collect::<Result<_, _>>()?,
            },
        })
    }
    fn instantiation(instantiation: &Instantiation) -> Result<InstantiationRecord, SnapshotError> {
        let (bindings, has_rows) = instantiation.alignment_bindings();
        if has_rows {
            return Err(SnapshotError::UnsupportedInstantiation);
        }
        let bindings = bindings
            .into_iter()
            .map(|(identity, ty)| match ty {
                Type::Inference(activation) => Ok((identity, activation.value())),
                _ => Err(SnapshotError::UnsupportedInstantiation),
            })
            .collect::<Result<_, _>>()?;
        Ok(InstantiationRecord(bindings))
    }
    fn environment(
        &mut self,
        environment: &Environment,
        depth: usize,
    ) -> Result<EnvironmentRecord, SnapshotError> {
        Self::depth(depth)?;
        let head = environment
            .head
            .as_ref()
            .map(|entry| self.entry(entry, depth + 1))
            .transpose()?;
        Ok(EnvironmentRecord {
            head,
            len: environment.len,
            instantiation: Self::instantiation(&environment.instantiation)?,
        })
    }
    fn entry(
        &mut self,
        entry: &Arc<EnvironmentEntry>,
        depth: usize,
    ) -> Result<usize, SnapshotError> {
        Self::depth(depth)?;
        let pointer = Arc::as_ptr(entry);
        if let Some(index) = self.references.get(&pointer) {
            return Ok(*index);
        }
        let index = self.entries.len();
        self.entries.push(None);
        self.references.insert(pointer, index);
        let parent = entry
            .parent
            .as_ref()
            .map(|parent| self.entry(parent, depth + 1))
            .transpose()?;
        let kind = match &entry.kind {
            EnvironmentEntryKind::Binding { binder, value } => EntryKind::Binding {
                binder: *binder,
                value: self.value(value, depth + 1)?,
            },
            EnvironmentEntryKind::Recursive { members } => {
                let mut templates = Vec::new();
                for member in members {
                    let RecursiveMemberKind::Function {
                        parameter,
                        body,
                        origin,
                        abstraction: None,
                    } = &member.kind
                    else {
                        return Err(SnapshotError::UnsupportedValue);
                    };
                    templates.push(FunctionTemplate {
                        binder: member.binder,
                        parameter: *parameter,
                        body: (*body).into(),
                        origin: self.origin(origin, depth + 1)?,
                    });
                }
                EntryKind::Recursive { members: templates }
            }
        };
        self.entries[index] = Some(EntryRecord {
            kind,
            parent,
            visible_len: entry.visible_len,
            instantiation: Self::instantiation(&entry.instantiation)?,
        });
        Ok(index)
    }
    fn value(&mut self, value: &Value, depth: usize) -> Result<ValueRecord, SnapshotError> {
        Self::depth(depth)?;
        Ok(match value {
            Value::Integer(integer) => ValueRecord::Integer(integer.clone()),
            Value::Boolean(boolean) => ValueRecord::Boolean(*boolean),
            Value::Unit => ValueRecord::Unit,
            Value::ResourceHandle(key) => ValueRecord::Handle(key.0),
            Value::Location(location) => ValueRecord::Location(*location),
            Value::Function(closure) => {
                if closure.program.root() != self.machine.program.root() {
                    return Err(SnapshotError::ForeignProgram);
                }
                ValueRecord::Closure {
                    parameter: closure.parameter,
                    body: closure.body.into(),
                    program_root: closure.program.root().into(),
                    program_nodes: closure.program.node_count(),
                    environment: self.environment(&closure.environment, depth + 1)?,
                    origin: self.origin(&closure.origin, depth + 1)?,
                }
            }
            Value::Polymorphic { .. } | Value::ConstructorFunction(_) | Value::Data(_) => {
                return Err(SnapshotError::UnsupportedValue);
            }
        })
    }
    fn supported_type(ty: &Type) -> bool {
        match ty {
            Type::Unit | Type::Bool | Type::Int => true,
            Type::Tuple(elements) => {
                matches!(elements.as_ref(),[a,b] if Self::supported_type(a)&&Self::supported_type(b))
            }
            Type::Function(input, output) => {
                Self::supported_type(input) && Self::supported_type(output)
            }
            Type::EffectfulFunction(input, output) => {
                Self::supported_type(input)
                    && Self::supported_type(output.value())
                    && output.effects().tail().is_none()
            }
            Type::Application(head, argument) => {
                matches!((head.as_ref(),argument.as_ref()),(Type::Nominal(nominal),Type::Variable(_)|Type::Inference(_)) if crate::resolved::ResourceApi::for_module(nominal.module()).is_some_and(|api| !api.is_native_buffer()&&api.handle()==*nominal))
            }
            _ => false,
        }
    }
    fn pattern(&self, pattern: &CorePattern) -> Result<PatternRecord, SnapshotError> {
        if !Self::supported_type(&pattern.ty) {
            return Err(SnapshotError::UnsupportedType);
        }
        let kind = match &pattern.kind {
            CorePatternKind::Unit => PatternKind::Unit,
            CorePatternKind::Boolean(boolean) => PatternKind::Boolean(*boolean),
            CorePatternKind::Binder(binder) => {
                if !Self::supported_type(binder.ty()) {
                    return Err(SnapshotError::UnsupportedType);
                }
                PatternKind::Binder(BinderRecord {
                    id: binder.id(),
                    ty: binder.ty().clone(),
                    origin: self.origin(binder.origin(), 0)?,
                })
            }
            _ => return Err(SnapshotError::UnsupportedPattern),
        };
        Ok(PatternRecord {
            ty: pattern.ty.clone(),
            origin: self.origin(&pattern.origin, 0)?,
            kind,
        })
    }
    fn frames(
        &mut self,
        frames: &[Frame],
        depth: usize,
    ) -> Result<Vec<FrameRecord>, SnapshotError> {
        Self::depth(depth)?;
        frames
            .iter()
            .map(|frame| self.frame(frame, depth + 1))
            .collect()
    }
    fn frame(&mut self, frame: &Frame, depth: usize) -> Result<FrameRecord, SnapshotError> {
        Self::depth(depth)?;
        Ok(match frame {
            Frame::CloseCompletion => FrameRecord::CloseCompletion,
            Frame::CleanupBoundary {
                action,
                environment,
            } => FrameRecord::CleanupBoundary {
                action: (*action).into(),
                environment: self.environment(environment, depth + 1)?,
            },
            Frame::CleanupCompletion { saved } => FrameRecord::CleanupCompletion {
                saved: self.value(saved, depth + 1)?,
            },
            Frame::ResourceInitializer { node, environment } => FrameRecord::ResourceInitializer {
                node: (*node).into(),
                environment: self.environment(environment, depth + 1)?,
            },
            Frame::ResourceBoundary {
                node,
                key,
                payload: ResourcePayload::Cell(payload),
            } => FrameRecord::ResourceBoundary {
                node: (*node).into(),
                key: key.0,
                payload: payload.clone(),
            },
            Frame::ResourceBoundary {
                payload: ResourcePayload::NativeBuffer { .. },
                ..
            } => return Err(SnapshotError::NativeBuffer),
            Frame::Bind {
                binder,
                body,
                environment,
            } => FrameRecord::Bind {
                binder: *binder,
                body: (*body).into(),
                environment: self.environment(environment, depth + 1)?,
            },
            Frame::ApplyFunction {
                argument,
                caller_environment,
            } => FrameRecord::ApplyFunction {
                argument: (*argument).into(),
                caller_environment: self.environment(caller_environment, depth + 1)?,
            },
            Frame::ApplyArgument { function } => FrameRecord::ApplyArgument {
                function: self.value(function, depth + 1)?,
            },
            Frame::Tuple {
                elements,
                next,
                values,
                environment,
            } => {
                if elements.len() != 2 {
                    return Err(SnapshotError::UnsupportedFrame);
                }
                FrameRecord::Tuple {
                    elements: elements.iter().map(|node| (*node).into()).collect(),
                    next: *next,
                    values: values
                        .iter()
                        .map(|value| self.value(value, depth + 1))
                        .collect::<Result<_, _>>()?,
                    environment: self.environment(environment, depth + 1)?,
                }
            }
            Frame::Match { arms, environment } => FrameRecord::Match {
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(ArmRecord {
                            pattern: self.pattern(arm.pattern())?,
                            body: arm.body().into(),
                            origin: self.origin(arm.origin(), depth + 1)?,
                        })
                    })
                    .collect::<Result<_, _>>()?,
                environment: self.environment(environment, depth + 1)?,
            },
            Frame::HandlerBoundary {
                node,
                environment,
                registration: None,
            } => {
                let handler = self
                    .machine
                    .handler(*node)
                    .ok_or(SnapshotError::MissingNode)?;
                if handler.hook_root().is_some() {
                    return Err(SnapshotError::Registration);
                }
                FrameRecord::HandlerBoundary {
                    node: (*node).into(),
                    effect: handler.effect().clone(),
                    environment: self.environment(environment, depth + 1)?,
                }
            }
            Frame::Request {
                node,
                instantiation,
            } => {
                let Some(ExecutableNode::Effect(expression)) = self.machine.program.node(*node)
                else {
                    return Err(SnapshotError::MissingNode);
                };
                let EffectExprKind::Operation(EffectOperation::Request(request)) = &expression.kind
                else {
                    return Err(SnapshotError::MissingNode);
                };
                FrameRecord::Request {
                    node: (*node).into(),
                    effect: request.effect().clone(),
                    instantiation: Self::instantiation(instantiation)?,
                }
            }
            Frame::Resume { node } => FrameRecord::Resume {
                node: (*node).into(),
            },
            Frame::ClauseBoundary {
                handler,
                owner,
                continuation,
                registration: None,
            } => FrameRecord::ClauseBoundary {
                handler: *handler,
                owner: *owner,
                continuation: continuation
                    .as_ref()
                    .map(|capture| self.frames(&capture.frames, depth + 1))
                    .transpose()?,
            },
            Frame::RegistrationBoundary { .. }
            | Frame::HandlerBoundary {
                registration: Some(_),
                ..
            }
            | Frame::ClauseBoundary {
                registration: Some(_),
                ..
            } => return Err(SnapshotError::Registration),
            Frame::PrimitiveLeft { .. }
            | Frame::PrimitiveRight { .. }
            | Frame::InitializeRecursive { .. }
            | Frame::TypeApplication { .. } => return Err(SnapshotError::UnsupportedFrame),
        })
    }
}

fn observed(
    fixture: &crate::core::alignment_export::CompiledFixture,
) -> (Result<Evaluation, RuntimeFailure>, Trace) {
    observe_machine(Machine::new_effect(&fixture.program), fixture)
}

fn observe_machine(
    mut machine: Machine,
    fixture: &crate::core::alignment_export::CompiledFixture,
) -> (Result<Evaluation, RuntimeFailure>, Trace) {
    let shared = Arc::new(Mutex::new(Trace {
        snapshots: Vec::new(),
        rejected: None,
        sources: fixture
            .sources
            .iter()
            .enumerate()
            .map(|(slot, (source, _, _))| (*source, slot))
            .collect(),
    }));
    machine.alignment_trace = Some(Arc::clone(&shared));
    let result = machine.run();
    let trace = Arc::try_unwrap(shared)
        .expect("observer is sole trace owner")
        .into_inner()
        .expect("observer mutex");
    (result, trace)
}

#[test]
fn observer_retains_actual_loop_boundaries_and_terminal_state() {
    let fixture = crate::core::alignment_export::effect_program("restored-clause-suffix");
    let (evaluation, trace) = observed(&fixture);
    assert_eq!(evaluation.unwrap().value.to_string(), "11");
    assert_eq!(trace.rejected, None);
    assert!(
        !trace.snapshots.is_empty(),
        "actual pre-step states must be retained"
    );
    let terminal = trace.snapshots.last().expect("terminal state");
    assert!(
        matches!(&terminal.control,ControlRecord::Return(ValueRecord::Integer(value)) if value.to_string()=="11")
    );
    assert!(terminal.frames.is_empty());
}

#[test]
fn observing_preserves_results_entry_trace_effect_trace_and_depth() {
    for name in [
        "restored-clause-suffix",
        "surviving-handler",
        "nested-resume",
        "nested-discard",
        "pure-closure-capture",
    ] {
        let fixture = crate::core::alignment_export::effect_program(name);
        let baseline = Machine::new_effect(&fixture.program)
            .run()
            .expect("unobserved execution");
        let (result, trace) = observed(&fixture);
        let result = result.expect("observed execution");
        if matches!(name, "nested-resume" | "nested-discard") {
            assert_eq!(
                trace.rejected,
                Some(SnapshotError::UnsupportedFrame),
                "{name}"
            );
        } else {
            assert_eq!(trace.rejected, None, "{name}");
        }
        assert_eq!(
            result.value.to_string(),
            baseline.value.to_string(),
            "{name}"
        );
        assert_eq!(result.trace, baseline.trace, "{name}");
        assert_eq!(result.effect_trace(), baseline.effect_trace(), "{name}");
        assert_eq!(result.max_frame_depth, baseline.max_frame_depth, "{name}");
        if trace.rejected.is_some() {
            continue;
        }
        let terminal = trace.snapshots.last().expect("terminal");
        assert_eq!(terminal.effects, result.effect_trace(), "{name}");
        assert_eq!(
            (
                terminal.captured_cells,
                terminal.live_resources,
                terminal.live_cleanups,
                terminal.live_registrations
            ),
            (0, 0, 0, 0),
            "{name}"
        );
    }
}

#[test]
fn actual_cell_payload_updates_are_7_then_11_and_abandoned_99_never_runs() {
    let fixture = crate::core::alignment_export::effect_program("restored-clause-suffix");
    let (result, trace) = observed(&fixture);
    assert_eq!(result.expect("execution").value.to_string(), "11");
    let updates = trace
        .snapshots
        .windows(2)
        .filter_map(|states| {
            let previous = &states[0];
            let next = &states[1];
            if let Some(key) = next.effects[previous.effects.len()..]
                .iter()
                .find_map(|event| match event {
                    EffectTraceEvent::ResourceWritten(key) => Some(key),
                    _ => None,
                })
            {
                next.frames.iter().find_map(|frame| match frame {
                    FrameRecord::ResourceBoundary {
                        key: found,
                        payload,
                        ..
                    } if found == key => Some(payload.to_string()),
                    _ => None,
                })
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    assert_eq!(updates, ["7", "11"]);
}

#[test]
fn resume_restores_capture_above_the_complete_consumed_clause_prefix() {
    let fixture = crate::core::alignment_export::effect_program("restored-clause-suffix");
    let (_, trace) = observed(&fixture);
    let mut checked = 0;
    for states in trace.snapshots.windows(2) {
        let before = &states[0];
        let after = &states[1];
        if !matches!(before.frames.last(), Some(FrameRecord::Resume { .. }))
            || !matches!(before.control, ControlRecord::Return(_))
        {
            continue;
        }
        let mut expected = before.frames[..before.frames.len() - 1].to_vec();
        let Some(FrameRecord::Resume { node }) = before.frames.last() else {
            unreachable!()
        };
        let resume = fixture
            .program
            .node(node.raw.expect("raw resume node"))
            .expect("resume node");
        let EffectExprKind::Operation(EffectOperation::Resume(resume)) = &resume.kind else {
            panic!("resume frame refers to resume Core")
        };
        let handler = resume.handler();
        let owner = resume.owner();
        let boundary = expected.iter_mut().rev().find(|frame| matches!(frame, FrameRecord::ClauseBoundary { handler: found, owner: ticket, .. } if *found == handler && *ticket == owner)).expect("nearest exact owner");
        let FrameRecord::ClauseBoundary { continuation, .. } = boundary else {
            unreachable!()
        };
        let captured = continuation
            .take()
            .expect("nearest exact owner must be live");
        // Environment-table references are local to each snapshot. Normalize by
        // comparing through their corresponding table entries below.
        let prefix_len = expected.len();
        expected.extend(captured.iter().cloned());
        assert_eq!(after.frames.len(), expected.len());
        assert!(after.frames[..prefix_len].iter().any(|frame| matches!(frame, FrameRecord::ClauseBoundary {handler: found, owner: ticket, continuation: None} if *found==handler && *ticket==owner)));
        assert_eq!(after.captured_cells + captured.len(), before.captured_cells);
        // Each frame's full structured data is checked after resolving observer
        // environment indices, rather than comparing unrelated table indices.
        assert_eq!(
            frame_shapes(&expected, &before.environments),
            frame_shapes(&after.frames, &after.environments)
        );
        checked += 1;
    }
    assert_eq!(checked, 1);
    assert!(
        trace
            .snapshots
            .iter()
            .any(|state| state.frames.iter().any(|frame| matches!(
                frame,
                FrameRecord::ClauseBoundary {
                    continuation: None,
                    ..
                }
            )))
    );
}

#[test]
fn normalized_snapshots_are_identical_across_independent_compilation() {
    let first = crate::core::alignment_export::effect_program("restored-clause-suffix");
    let second = crate::core::alignment_export::effect_program("restored-clause-suffix");
    let (_, first) = observed(&first);
    let (_, second) = observed(&second);
    assert_eq!(first.rejected, None);
    assert_eq!(first.snapshots.len(), second.snapshots.len());
    assert_eq!(second.rejected, None);
    for (index, (first, second)) in first
        .normalized()
        .iter()
        .zip(second.normalized())
        .enumerate()
    {
        assert_eq!(*first, second, "snapshot {index}");
    }
}

// A structural copy discards only allocation-scoped source/Core tokens.
// Checked binder, effect and owner identities and arena distinctions survive.
struct Normalizer<'a> {
    entries: &'a [EntryRecord],
    remapped: HashMap<usize, usize>,
    result: Vec<EntryRecord>,
    modules: HashMap<crate::module::ModuleId, crate::module::ModuleId>,
    module_labels: Vec<(String, u32)>,
}
impl<'a> Normalizer<'a> {
    fn new(entries: &'a [EntryRecord]) -> Self {
        Self {
            entries,
            remapped: HashMap::new(),
            result: Vec::new(),
            modules: HashMap::new(),
            module_labels: Vec::new(),
        }
    }
    fn module(&mut self, raw: crate::module::ModuleId) -> crate::module::ModuleId {
        if let Some(label) = self.modules.get(&raw) {
            return *label;
        }
        let label = crate::module::ModuleId::new(
            u32::try_from(self.modules.len()).expect("bounded observer module count"),
        );
        let namespace = if raw.is_builtin_cell() {
            "cell"
        } else if raw.is_builtin_native_buffer() {
            "nativeBuffer"
        } else if raw.to_string().starts_with("source:") {
            "directCoreSource"
        } else {
            "admitted"
        };
        self.module_labels.push((namespace.into(), raw.value()));
        self.modules.insert(raw, label);
        label
    }
    fn binder(&mut self, binder: &mut BinderId) {
        if let BinderId::Resolved { module, .. } = binder {
            *module = self.module(*module);
        }
    }
    fn variable(&mut self, variable: &mut TypeVariableId) {
        if let TypeVariableId::Resolved { module, .. } = variable {
            *module = self.module(*module);
        }
    }
    fn instantiation(&mut self, instantiation: &mut InstantiationRecord) {
        for (variable, _) in &mut instantiation.0 {
            self.variable(variable);
        }
    }
    fn effect_id(&mut self, id: crate::types::EffectId) -> crate::types::EffectId {
        crate::types::EffectId::new(self.module(id.module()), id.declaration())
    }
    fn effect(&mut self, effect: &mut EffectInstance) {
        let id = self.effect_id(effect.effect());
        let mut arguments = effect.arguments().to_vec();
        for argument in &mut arguments {
            self.ty(argument);
        }
        *effect = EffectInstance::new(id, arguments.into_boxed_slice());
    }
    fn ty(&mut self, ty: &mut Type) {
        match ty {
            Type::Variable(variable) => self.variable(variable),
            Type::Nominal(id) => {
                // Supported nominal leaves are the module-owned cell handle.
                *id = crate::types::NominalTypeId::new(self.module(id.module()), id.declaration());
            }
            Type::Tuple(elements) => {
                for element in elements {
                    self.ty(element);
                }
            }
            Type::Function(input, output) | Type::Application(input, output) => {
                self.ty(input);
                self.ty(output);
            }
            Type::EffectfulFunction(input, computation) => {
                self.ty(input);
                let mut value = computation.value().clone();
                self.ty(&mut value);
                let mut effects = computation.effects().known().to_vec();
                for effect in &mut effects {
                    self.effect(effect);
                }
                assert!(
                    computation.effects().tail().is_none(),
                    "observer admits closed rows only"
                );
                **computation = crate::types::ComputationType::new(
                    value,
                    crate::types::EffectRow::closed(effects.into_boxed_slice()),
                );
            }
            Type::Forall(..) => panic!("observer rejects polymorphic types"),
            Type::Unit | Type::Bool | Type::Int | Type::Inference(_) => (),
        }
    }
    fn node(node: &mut NodeReference) {
        node.raw = None;
    }
    fn origin(origin: &mut OriginTree) {
        match origin {
            OriginTree::Source(span) => span.raw = None,
            OriginTree::Generated { cause, .. } => Self::origin(cause),
            OriginTree::Related { primary, related } => {
                Self::origin(primary);
                for span in related {
                    span.raw = None;
                }
            }
        }
    }
    fn entry(&mut self, old: usize) -> usize {
        if let Some(new) = self.remapped.get(&old) {
            return *new;
        }
        let new = self.result.len();
        self.remapped.insert(old, new);
        let mut entry = self.entries[old].clone();
        self.result.push(entry.clone());
        entry.parent = entry.parent.map(|parent| self.entry(parent));
        match &mut entry.kind {
            EntryKind::Binding { binder, value } => {
                self.binder(binder);
                self.value(value);
            }
            EntryKind::Recursive { members } => {
                for member in members {
                    self.binder(&mut member.binder);
                    self.binder(&mut member.parameter);
                    Self::node(&mut member.body);
                    Self::origin(&mut member.origin);
                }
            }
        }
        self.instantiation(&mut entry.instantiation);
        self.result[new] = entry;
        new
    }
    fn environment(&mut self, environment: &mut EnvironmentRecord) {
        environment.head = environment.head.map(|old| self.entry(old));
        self.instantiation(&mut environment.instantiation);
    }
    fn value(&mut self, value: &mut ValueRecord) {
        if let ValueRecord::Closure {
            parameter,
            body,
            program_root,
            environment,
            origin,
            ..
        } = value
        {
            self.binder(parameter);
            Self::node(body);
            // This fragment's closures all belong to the observed validated
            // arena. Builder rejects any other arena before this erasure.
            Self::node(program_root);
            self.environment(environment);
            Self::origin(origin);
        }
    }
    fn pattern(&mut self, pattern: &mut PatternRecord) {
        self.ty(&mut pattern.ty);
        Self::origin(&mut pattern.origin);
        if let PatternKind::Binder(binder) = &mut pattern.kind {
            self.binder(&mut binder.id);
            self.ty(&mut binder.ty);
            Self::origin(&mut binder.origin);
        }
    }
    fn frames(&mut self, frames: &mut [FrameRecord]) {
        for frame in frames {
            match frame {
                FrameRecord::Bind { binder, .. } => self.binder(binder),
                FrameRecord::HandlerBoundary { effect, .. } => self.effect(effect),
                FrameRecord::Request {
                    effect,
                    instantiation,
                    ..
                } => {
                    self.effect(effect);
                    self.instantiation(instantiation);
                }
                _ => (),
            }
            match frame {
                FrameRecord::CleanupBoundary {
                    action,
                    environment,
                } => {
                    Self::node(action);
                    self.environment(environment);
                }
                FrameRecord::ResourceInitializer { node, environment }
                | FrameRecord::Bind {
                    body: node,
                    environment,
                    ..
                }
                | FrameRecord::ApplyFunction {
                    argument: node,
                    caller_environment: environment,
                }
                | FrameRecord::HandlerBoundary {
                    node, environment, ..
                } => {
                    Self::node(node);
                    self.environment(environment);
                }
                FrameRecord::CleanupCompletion { saved: value }
                | FrameRecord::ApplyArgument { function: value } => self.value(value),
                FrameRecord::Tuple {
                    elements,
                    values,
                    environment,
                    ..
                } => {
                    for node in elements {
                        Self::node(node);
                    }
                    for value in values {
                        self.value(value);
                    }
                    self.environment(environment);
                }
                FrameRecord::Match { arms, environment } => {
                    for arm in arms {
                        self.pattern(&mut arm.pattern);
                        Self::node(&mut arm.body);
                        Self::origin(&mut arm.origin);
                    }
                    self.environment(environment);
                }
                FrameRecord::ResourceBoundary { node, .. }
                | FrameRecord::Request { node, .. }
                | FrameRecord::Resume { node } => Self::node(node),
                FrameRecord::ClauseBoundary {
                    continuation: Some(frames),
                    ..
                } => self.frames(frames),
                FrameRecord::ClauseBoundary {
                    continuation: None, ..
                }
                | FrameRecord::CloseCompletion => (),
            }
        }
    }
}
impl Snapshot {
    fn normalized(
        &self,
        modules: &mut HashMap<crate::module::ModuleId, crate::module::ModuleId>,
        labels: &mut Vec<(String, u32)>,
    ) -> Self {
        let mut copy = self.clone();
        let mut normalize = Normalizer::new(&self.environments);
        normalize.modules = std::mem::take(modules);
        normalize.module_labels = std::mem::take(labels);
        match &mut copy.control {
            ControlRecord::Evaluate(node, environment) => {
                Normalizer::node(node);
                normalize.environment(environment);
            }
            ControlRecord::Return(value) => normalize.value(value),
            ControlRecord::Discard(..) => (),
        }
        normalize.frames(&mut copy.frames);
        for cell in &mut copy.heap {
            if let HeapRecord::Pair(values) = cell {
                for value in values.iter_mut() {
                    normalize.value(value);
                }
            }
        }
        for node in &mut copy.entered {
            Normalizer::node(node);
        }
        for event in &mut copy.effects {
            match event {
                EffectTraceEvent::Request(operation)
                | EffectTraceEvent::ClauseEntered(_, operation) => {
                    *operation = crate::types::OperationId::new(
                        normalize.effect_id(operation.owner()),
                        operation.operation(),
                    );
                }
                _ => (),
            }
        }
        copy.modules = normalize.module_labels.clone();
        *modules = normalize.modules;
        *labels = normalize.module_labels;
        copy.environments = normalize.result;
        copy
    }
}
impl Trace {
    fn normalized(&self) -> Vec<Snapshot> {
        let mut modules = HashMap::new();
        let mut labels = Vec::new();
        self.snapshots
            .iter()
            .map(|snapshot| snapshot.normalized(&mut modules, &mut labels))
            .collect()
    }
}
fn frame_shapes(
    frames: &[FrameRecord],
    entries: &[EntryRecord],
) -> (Vec<FrameRecord>, Vec<EntryRecord>, Vec<(String, u32)>) {
    let mut copy = frames.to_vec();
    let mut normalize = Normalizer::new(entries);
    normalize.frames(&mut copy);
    (copy, normalize.result, normalize.module_labels)
}

#[test]
fn excluded_native_hook_and_polymorphic_states_are_rejected_explicitly() {
    let fixture = crate::core::alignment_export::effect_program("restored-clause-suffix");
    let sources = fixture
        .sources
        .iter()
        .enumerate()
        .map(|(slot, (source, _, _))| (*source, slot))
        .collect();
    let root = fixture.program.root();
    let mut machine = Machine::new_effect(&fixture.program);
    machine.control = Some(Control::Return(Value::Polymorphic {
        abstraction: root,
        environment: Environment::new(),
    }));
    assert_eq!(
        Builder::snapshot(&machine, &sources).unwrap_err(),
        SnapshotError::UnsupportedValue
    );
    machine.control = Some(Control::Return(Value::Unit));
    machine.frames.push(Frame::RegistrationBoundary {
        key: RegistrationKey(0),
        handler: root,
        callback: Value::Unit,
        handler_active: false,
        pending_invocations: 0,
    });
    assert_eq!(
        Builder::snapshot(&machine, &sources).unwrap_err(),
        SnapshotError::Registration
    );
    machine.frames.clear();
    machine.frames.push(Frame::ResourceBoundary {
        node: root,
        key: ActivationKey(0),
        payload: ResourcePayload::NativeBuffer {
            owner: NativeOwner::allocate(1).expect("native owner"),
            completion: None,
        },
    });
    assert_eq!(
        Builder::snapshot(&machine, &sources).unwrap_err(),
        SnapshotError::NativeBuffer
    );
    machine.frames.clear();
    machine.frames.push(Frame::TypeApplication {
        node: root,
        caller: Instantiation::default(),
    });
    assert_eq!(
        Builder::snapshot(&machine, &sources).unwrap_err(),
        SnapshotError::UnsupportedFrame
    );
}

#[test]
fn observer_rejection_retains_prefix_and_does_not_interrupt_execution() {
    let mut fixture = crate::core::alignment_export::effect_program("restored-clause-suffix");
    let baseline = Machine::new_effect(&fixture.program)
        .run()
        .expect("baseline");
    // Missing source admission deliberately makes the observer reject the first
    // lexical template, while actual evaluation continues using validated Core.
    fixture.sources.clear();
    let (result, trace) = observed(&fixture);
    let result = result.expect("observer rejection does not reject evaluation");
    assert_eq!(trace.rejected, Some(SnapshotError::MissingSource));
    assert!(!trace.snapshots.is_empty());
    assert_eq!(result.value.to_string(), baseline.value.to_string());
    assert_eq!(result.trace, baseline.trace);
    assert_eq!(result.effect_trace(), baseline.effect_trace());
}

#[test]
fn lexical_cell_instantiation_and_closure_environment_survive_observation() {
    let fixture = crate::core::alignment_export::effect_program("pure-closure-capture");
    let (result, trace) = observed(&fixture);
    assert_eq!(result.expect("execution").value.to_string(), "()");
    assert_eq!(trace.rejected, None);
    let captured = trace
        .snapshots
        .iter()
        .find_map(|snapshot| {
            if let ControlRecord::Return(ValueRecord::Closure { environment, .. }) =
                &snapshot.control
                && !environment.instantiation.0.is_empty()
            {
                Some((snapshot, environment))
            } else {
                None
            }
        })
        .expect("closure retains lexical resource instantiation");
    assert_eq!(captured.1.instantiation.0.len(), 1);
    assert_eq!(captured.1.instantiation.0[0].1, 0);
    assert_eq!(captured.0.next_activation, 1);
    let mut head = captured.1.head;
    let mut found_handle = false;
    while let Some(index) = head {
        let entry = &captured.0.environments[index];
        found_handle |= matches!(
            entry.kind,
            EntryKind::Binding {
                value: ValueRecord::Handle(0),
                ..
            }
        );
        head = entry.parent;
    }
    assert!(
        found_handle,
        "captured environment retains the cell access key"
    );
}

#[test]
fn resource_capacity_failure_retains_actual_prefix_without_changing_failure() {
    let fixture = crate::core::alignment_export::effect_program("restored-clause-suffix");
    let mut baseline = Machine::new_effect(&fixture.program);
    baseline.resource_limit = 0;
    let baseline = baseline
        .run()
        .expect_err("resource acquisition exceeds zero limit");
    let mut machine = Machine::new_effect(&fixture.program);
    machine.resource_limit = 0;
    let (result, trace) = observe_machine(machine, &fixture);
    assert_eq!(result.expect_err("same capacity failure"), baseline);
    assert_eq!(trace.rejected, None);
    assert!(!trace.snapshots.is_empty());
    let last = trace.snapshots.last().expect("observed failing-step input");
    assert_eq!(last.next_activation, 0);
    assert_eq!(last.live_resources, 0);
    assert!(
        !last
            .effects
            .iter()
            .any(|event| matches!(event, EffectTraceEvent::ResourceAcquired(_)))
    );
}

#[test]
fn normalization_preserves_distinct_module_and_program_identities() {
    let first = crate::core::alignment_export::effect_program("restored-clause-suffix");
    let second = crate::core::alignment_export::effect_program("restored-clause-suffix");
    let mut normalize = Normalizer::new(&[]);
    let first_source = first
        .sources
        .iter()
        .find(|(_, module, _)| !module.is_builtin_resource())
        .expect("source")
        .1;
    let second_source = second
        .sources
        .iter()
        .find(|(_, module, _)| !module.is_builtin_resource())
        .expect("source")
        .1;
    assert_ne!(
        normalize.module(first_source),
        normalize.module(second_source)
    );
    assert_eq!(
        normalize.module(first_source),
        normalize.module(first_source)
    );
    let cell = first
        .sources
        .iter()
        .find(|(_, module, _)| module.is_builtin_cell())
        .expect("cell")
        .1;
    let cell_label = normalize.module(cell);
    assert_ne!(cell_label, normalize.module(first_source));
    assert_eq!(
        normalize.module_labels[cell_label.value() as usize].0,
        "cell"
    );

    let mut machine = Machine::new_effect(&first.program);
    machine.control = Some(Control::Return(Value::Function(Closure {
        parameter: BinderId::generated(0),
        body: second.program.root(),
        program: ExecutableProgram::Effect(second.program.shared()),
        environment: Environment::new(),
        origin: second
            .program
            .node(second.program.root())
            .expect("root")
            .origin
            .clone(),
    })));
    let sources = first
        .sources
        .iter()
        .enumerate()
        .map(|(slot, (source, _, _))| (*source, slot))
        .collect();
    assert_eq!(
        Builder::snapshot(&machine, &sources).unwrap_err(),
        SnapshotError::ForeignProgram
    );
}

// This renderer reads the retained actual-loop data only. Frozen identities
// come from the graph exporter; no model evaluator participates in generation.
struct ObservationExporter<'a> {
    identities: &'a crate::core::alignment_export::IdentityMaps,
    entries: &'a [EntryRecord],
}
impl ObservationExporter<'_> {
    fn list(items: impl IntoIterator<Item = String>) -> String {
        format!("[{}]", items.into_iter().collect::<Vec<_>>().join(", "))
    }
    fn node(&self, node: &NodeReference) -> Result<usize, String> {
        let raw = node
            .raw
            .ok_or("normalized node cannot be exported as actual data")?;
        if raw.value() != node.original {
            return Err("original node identity mismatch".into());
        }
        self.identities
            .nodes
            .get(&raw)
            .copied()
            .ok_or_else(|| "node absent from graph numbering".into())
    }
    fn binder(&self, binder: BinderId) -> Result<usize, String> {
        self.identities
            .binders
            .get(&binder)
            .copied()
            .ok_or_else(|| "binder absent from graph numbering".into())
    }
    fn owner(&self, owner: ResumeId) -> Result<usize, String> {
        self.identities
            .owners
            .get(&owner)
            .copied()
            .ok_or_else(|| "owner absent from graph numbering".into())
    }
    fn resource(&self, identity: TypeVariableId) -> Result<usize, String> {
        self.identities
            .resources
            .get(&identity)
            .copied()
            .ok_or_else(|| "resource absent from graph numbering".into())
    }
    fn instantiation(&self, instantiation: &InstantiationRecord) -> Result<String, String> {
        let mut bindings = instantiation
            .0
            .iter()
            .map(|(identity, key)| Ok((self.resource(*identity)?, *key)))
            .collect::<Result<Vec<_>, String>>()?;
        bindings.sort_unstable();
        Ok(Self::list(
            bindings
                .into_iter()
                .map(|(name, key)| format!("({name}, {key})")),
        ))
    }
    fn resource_argument(&self, ty: &Type) -> Result<String, String> {
        match ty {
            Type::Variable(identity) => Ok(format!("(.bound {})", self.resource(*identity)?)),
            Type::Inference(key) => Ok(format!("(.activation {})", key.value())),
            _ => Err("unsupported runtime effect argument".into()),
        }
    }
    fn effect(&self, effect: &EffectInstance) -> Result<String, String> {
        if let Some(api) = crate::resolved::ResourceApi::for_module(effect.effect().module()) {
            if api.is_native_buffer() || effect.effect() != api.ops() {
                return Err("unsupported runtime builtin effect".into());
            }
            let [argument] = effect.arguments() else {
                return Err("cell effect arity".into());
            };
            return Ok(format!("(.cell {})", self.resource_argument(argument)?));
        }
        let id = self
            .identities
            .effects
            .get(&effect.effect())
            .ok_or("effect absent from graph numbering")?;
        let args = effect
            .arguments()
            .iter()
            .map(|ty| {
                self.resource_argument(ty)
                    .map(|resource| format!("(.resource {resource})"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(format!("(.user {id} {})", Self::list(args)))
    }
    fn operation_effect(&self, operation: crate::types::OperationId) -> Result<String, String> {
        let effect = operation.owner();
        if let Some(api) = crate::resolved::ResourceApi::for_module(effect.module()) {
            if api.is_native_buffer() || effect != api.ops() {
                return Err("unsupported trace builtin effect".into());
            }
            // EffectTrace stores declaration identities, not request arguments.
            return Ok(".cell".into());
        }
        let id = self
            .identities
            .effects
            .get(&effect)
            .ok_or("trace effect absent from graph numbering")?;
        Ok(format!("(.user {id})"))
    }
    fn environment(&self, environment: &EnvironmentRecord) -> Result<String, String> {
        let mut entries = Vec::new();
        let mut head = environment.head;
        while let Some(index) = head {
            let entry = self.entries.get(index).ok_or("environment reference")?;
            let bindings = self.instantiation(&entry.instantiation)?;
            entries.push(match &entry.kind {
                EntryKind::Binding { binder, value } => format!(
                    "(.binding {} {} {} {bindings})",
                    self.binder(*binder)?,
                    self.value(value)?,
                    entry.visible_len
                ),
                EntryKind::Recursive { members } => {
                    let [member] = members.as_slice() else {
                        return Err("multiple function templates outside observed wrapper".into());
                    };
                    format!(
                        "(.template {} {} {} {} {bindings})",
                        self.binder(member.binder)?,
                        self.binder(member.parameter)?,
                        self.node(&member.body)?,
                        entry.visible_len
                    )
                }
            });
            head = entry.parent;
        }
        Ok(format!(
            "(.mk {} {} {})",
            environment.len,
            self.instantiation(&environment.instantiation)?,
            Self::list(entries)
        ))
    }
    fn value(&self, value: &ValueRecord) -> Result<String, String> {
        Ok(match value {
            ValueRecord::Unit => ".unit".into(),
            ValueRecord::Boolean(value) => format!("(.boolean {value})"),
            ValueRecord::Integer(value) => format!("(.integer ({value}))"),
            ValueRecord::Handle(key) => format!("(.handle {key})"),
            ValueRecord::Location(key) => format!("(.location {key})"),
            ValueRecord::Closure {
                parameter,
                body,
                program_root,
                program_nodes,
                environment,
                ..
            } => format!(
                "(.closure {} {} {} {program_nodes} {})",
                self.binder(*parameter)?,
                self.node(body)?,
                self.node(program_root)?,
                self.environment(environment)?
            ),
        })
    }
    fn frames(&self, frames: &[FrameRecord]) -> Result<String, String> {
        // Both ordinary and recursively captured vectors use Rust orientation.
        Ok(Self::list(
            frames
                .iter()
                .rev()
                .map(|frame| self.frame(frame))
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }
    fn frame(&self, frame: &FrameRecord) -> Result<String, String> {
        Ok(match frame {
            FrameRecord::CloseCompletion => ".closeCompletion".into(),
            FrameRecord::CleanupBoundary {
                action,
                environment,
            } => format!(
                "(.cleanupBoundary {} {})",
                self.node(action)?,
                self.environment(environment)?
            ),
            FrameRecord::CleanupCompletion { saved } => {
                format!("(.cleanupCompletion {})", self.value(saved)?)
            }
            FrameRecord::ResourceInitializer { node, environment } => format!(
                "(.resourceInitializer {} {})",
                self.node(node)?,
                self.environment(environment)?
            ),
            FrameRecord::ResourceBoundary { node, key, payload } => {
                format!("(.resourceBoundary {} {key} ({payload}))", self.node(node)?)
            }
            FrameRecord::Bind {
                binder,
                body,
                environment,
            } => format!(
                "(.bind {} {} {})",
                self.binder(*binder)?,
                self.node(body)?,
                self.environment(environment)?
            ),
            FrameRecord::ApplyFunction {
                argument,
                caller_environment,
            } => format!(
                "(.applyFunction {} {})",
                self.node(argument)?,
                self.environment(caller_environment)?
            ),
            FrameRecord::ApplyArgument { function } => {
                format!("(.applyArgument {})", self.value(function)?)
            }
            FrameRecord::Tuple {
                elements,
                next,
                values,
                environment,
            } => format!(
                "(.tuple {} {next} {} {})",
                Self::list(
                    elements
                        .iter()
                        .map(|node| self.node(node).map(|id| id.to_string()))
                        .collect::<Result<Vec<_>, _>>()?
                ),
                Self::list(
                    values
                        .iter()
                        .map(|value| self.value(value))
                        .collect::<Result<Vec<_>, _>>()?
                ),
                self.environment(environment)?
            ),
            FrameRecord::Match { arms, environment } => {
                let arms = arms
                    .iter()
                    .map(|arm| {
                        let pattern = match &arm.pattern.kind {
                            PatternKind::Unit => ".unit".into(),
                            PatternKind::Boolean(value) => format!("(.boolean {value})"),
                            PatternKind::Binder(_) => {
                                return Err("binder match outside observed fixture".to_string());
                            }
                        };
                        Ok(format!("⟨{pattern}, {}⟩", self.node(&arm.body)?))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                format!(
                    "(.matchCases {} {})",
                    Self::list(arms),
                    self.environment(environment)?
                )
            }
            FrameRecord::HandlerBoundary {
                node,
                effect,
                environment,
            } => format!(
                "(.handlerBoundary {} {} {})",
                self.node(node)?,
                self.effect(effect)?,
                self.environment(environment)?
            ),
            FrameRecord::Request {
                node,
                effect,
                instantiation,
            } => format!(
                "(.request {} {} {})",
                self.node(node)?,
                self.effect(effect)?,
                self.instantiation(instantiation)?
            ),
            FrameRecord::Resume { node } => format!("(.resume {})", self.node(node)?),
            FrameRecord::ClauseBoundary {
                handler,
                owner,
                continuation,
            } => {
                let capture = continuation
                    .as_ref()
                    .map(|frames| self.frames(frames).map(|frames| format!("(some {frames})")))
                    .transpose()?
                    .unwrap_or_else(|| "none".into());
                format!(
                    "(.clauseBoundary {} {} {capture})",
                    handler.value(),
                    self.owner(*owner)?
                )
            }
        })
    }
    fn event(&self, event: &EffectTraceEvent) -> Result<String, String> {
        Ok(match *event {
            EffectTraceEvent::ResourceAcquired(key) => format!("(.acquired {key})"),
            EffectTraceEvent::ResourceRead(key) => format!("(.read {key})"),
            EffectTraceEvent::ResourceWritten(key) => format!("(.written {key})"),
            EffectTraceEvent::ResourceReleased(key) => format!("(.released {key})"),
            EffectTraceEvent::HandlerActivated(id) => format!("(.handlerActivated {})", id.value()),
            EffectTraceEvent::Request(operation) => format!(
                "(.request {} {})",
                self.operation_effect(operation)?,
                operation.operation()
            ),
            EffectTraceEvent::HandlerSelected(id) => format!("(.handlerSelected {})", id.value()),
            EffectTraceEvent::ClauseEntered(id, operation) => format!(
                "(.clauseEntered {} {} {})",
                id.value(),
                self.operation_effect(operation)?,
                operation.operation()
            ),
            EffectTraceEvent::Resume(id) => format!("(.resumed {})", id.value()),
            EffectTraceEvent::Discard(id) => format!("(.discarded {})", id.value()),
            EffectTraceEvent::HandlerRestored(id) => format!("(.handlerRestored {})", id.value()),
            EffectTraceEvent::ClauseReturned(id) => format!("(.clauseReturned {})", id.value()),
        })
    }
    fn snapshot(&self, snapshot: &Snapshot) -> Result<String, String> {
        let control = match &snapshot.control {
            ControlRecord::Evaluate(node, environment) => format!(
                "(.evaluate {} {})",
                self.node(node)?,
                self.environment(environment)?
            ),
            ControlRecord::Return(value) => format!("(.returned {})", self.value(value)?),
            ControlRecord::Discard(handler, owner) => {
                format!("(.discard {} {})", handler.value(), self.owner(*owner)?)
            }
        };
        let heap = Self::list(
            snapshot
                .heap
                .iter()
                .map(|cell| {
                    Ok(match cell {
                        HeapRecord::Uninitialized => ".uninitialized".into(),
                        HeapRecord::Alias(location) => format!("(.alias {location})"),
                        HeapRecord::Pair(values) => format!(
                            "(.pair {} {})",
                            self.value(&values[0])?,
                            self.value(&values[1])?
                        ),
                    })
                })
                .collect::<Result<Vec<_>, String>>()?,
        );
        let entered = Self::list(
            snapshot
                .entered
                .iter()
                .map(|node| self.node(node).map(|node| node.to_string()))
                .collect::<Result<Vec<_>, _>>()?,
        );
        let effects = Self::list(
            snapshot
                .effects
                .iter()
                .map(|event| self.event(event))
                .collect::<Result<Vec<_>, _>>()?,
        );
        Ok(format!(
            "{{ control := {control}, frames := {}, heap := {heap}, accounting := ⟨{}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}⟩, entered := {entered}, effects := {effects} }}",
            self.frames(&snapshot.frames)?,
            snapshot.next_activation,
            snapshot.captured_cells,
            snapshot.live_resources,
            snapshot.live_cleanups,
            snapshot.live_registrations,
            snapshot.next_registration,
            snapshot.max_frame_depth,
            snapshot.capture_limit,
            snapshot.resource_limit,
            snapshot.cleanup_limit,
            snapshot.registration_limit,
            snapshot.work_used,
            snapshot.work_remaining
        ))
    }
}

fn export_actual_trace(
    fixture: &crate::core::alignment_export::CompiledFixture,
    trace: &Trace,
) -> Result<String, String> {
    if let Some(error) = trace.rejected {
        return Err(format!("observer rejected: {error:?}"));
    }
    let identities = crate::core::alignment_export::identity_maps(fixture)?;
    let snapshots = trace
        .snapshots
        .iter()
        .map(|snapshot| {
            ObservationExporter {
                identities: &identities,
                entries: &snapshot.environments,
            }
            .snapshot(snapshot)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut definitions = String::from(
        "import CoreObservation\nimport CoreExportedFixture\n\n/-! Generated only from actual Rust run_loop boundaries of the validated\nrestored-clause-suffix fixture. Frozen numbering is shared with the graph exporter.\nThis finite successful trace is implementation evidence, not general simulation. -/\nnamespace Ash.OneShot.CoreObservedTrace\nopen CoreObservation\nset_option maxRecDepth 100000\nset_option maxHeartbeats 10000000\n\n",
    );
    for (index, snapshot) in snapshots.iter().enumerate() {
        definitions.push_str(&format!("def s{index} : Snapshot :=\n  {snapshot}\n\n"));
    }
    let last = snapshots
        .len()
        .checked_sub(1)
        .ok_or("empty observed trace")?;
    definitions.push_str(&format!(
        "def actual : List Snapshot := {}\n\nexample : actual.length = {} := rfl\n\n",
        ObservationExporter::list((0..snapshots.len()).map(|index| format!("s{index}"))),
        snapshots.len()
    ));
    definitions.push_str(&format!(r#"def initialModel : CoreMachine.State := CoreMachine.initial CoreExportedFixture.graph

/-- Every exported actual boundary has the stated structural/ownership relation;
    every consecutive pair has one genuine independent-machine transition. -/
theorem checked : checkTrace CoreExportedFixture.graph initialModel [] actual = true := by
  decide +kernel

theorem actual_steps : CheckedTrace CoreExportedFixture.graph initialModel [] actual {last} :=
  checkTrace_sound _ _ _ _ checked

theorem actual_result : s{last}.control = .returned (.integer 11) := rfl

theorem actual_cell_order : actualCells s{last} =
    [.acquired 0, .written 0, .written 0, .read 0, .released 0] := rfl

theorem actual_write_values : writtenValues actual = [7, 11] := by decide +kernel

theorem actual_cleanup_start_order : callbackStarts actual = [27] := by decide +kernel

/-- One handler occurrence and two distinct owner tickets appear in the model;
    they have no Rust fields. The checked replay keeps their full state and
    successor equations while projecting to Rust's static owner/capture data. -/
theorem model_ghost_counts : ghostCounts (atStep CoreExportedFixture.graph {last} initialModel) =
    some (1, 2, 1, 1) := by decide +kernel

theorem model_ghost_captures : ghostCaptures (atStep CoreExportedFixture.graph {last} initialModel) =
    [(0, 0), (0, 1)] := by decide +kernel

/-- Dropping the terminal boundary or adding one after completion fails. -/
theorem truncated_rejected : checkTrace CoreExportedFixture.graph initialModel [] (actual.take {last}) =
    false := by decide +kernel

theorem extra_terminal_rejected : checkTrace CoreExportedFixture.graph initialModel [] (actual ++ [s{last}]) =
    false := by decide +kernel

#print axioms checked
#print axioms actual_steps
#print axioms actual_result
#print axioms actual_cell_order
#print axioms actual_write_values
#print axioms actual_cleanup_start_order
#print axioms model_ghost_counts
#print axioms model_ghost_captures
#print axioms truncated_rejected
#print axioms extra_terminal_rejected

end Ash.OneShot.CoreObservedTrace
"#));
    Ok(definitions)
}

#[test]
#[ignore = "explicit regeneration of actual-loop Lean trace"]
fn regenerate_actual_observed_trace() {
    let fixture = crate::core::alignment_export::effect_program("restored-clause-suffix");
    let (result, trace) = observed(&fixture);
    assert_eq!(result.expect("actual execution").value.to_string(), "11");
    let rendered = export_actual_trace(&fixture, &trace).expect("actual snapshots export");
    std::fs::write(
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/direct-effects/one-shot/CoreObservedTrace.lean"),
        rendered,
    )
    .expect("write observed trace");
}

#[test]
fn actual_observation_export_is_stable_and_matches_checked_in_trace() {
    let first = crate::core::alignment_export::effect_program("restored-clause-suffix");
    let second = crate::core::alignment_export::effect_program("restored-clause-suffix");
    let (_, first_trace) = observed(&first);
    let (_, second_trace) = observed(&second);
    let rendered = export_actual_trace(&first, &first_trace).expect("export first");
    assert_eq!(
        rendered,
        export_actual_trace(&second, &second_trace).expect("export second")
    );
    assert_eq!(
        rendered,
        include_str!("../../../docs/design/direct-effects/one-shot/CoreObservedTrace.lean")
    );
}
