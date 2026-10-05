//! Connected private evaluator witness for terminal acquisition publication refusal.
//! The ordinary evaluator remains unbounded; this test uses its existing work meter.

use super::*;
use crate::{
    foreign::{
        ForeignConstructorDeclaration, ForeignEffectDeclaration, ForeignManifest,
        ForeignManifestSchema, ForeignModuleFact, ForeignOperationDeclaration,
        ForeignRegistrations, ForeignResultRelation, ForeignTypeDeclaration, provider_manifest,
        runtime::{
            ExecutableForeignModule, ForeignAcquisition, ForeignCompletion, ForeignData,
            ForeignDataNode, ForeignExecutionError, ForeignFinishContext, ForeignOperationKey,
            ForeignRuntime, ForeignRuntimeBinding, NativeResourceOwner,
        },
    },
    module::{ForeignOperationRole, ForeignRegistrationId, ModuleRoots, load_module_graph},
};
use std::{any::Any, cell::RefCell, path::PathBuf, rc::Rc, sync::Arc};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Event {
    Acquired(usize),
    Borrowed(usize),
    Finished(usize),
    Destroyed(usize),
}
#[derive(Debug)]
struct Trace {
    events: Vec<Event>,
    live: [bool; 2],
}
type Observations = Rc<RefCell<Trace>>;
#[derive(Debug)]
struct Owner {
    family: usize,
    storage: Option<Box<[i64]>>,
    trace: Observations,
}
impl Owner {
    fn destroy(&mut self) {
        if let Some(storage) = self.storage.take() {
            let mut trace = self.trace.borrow_mut();
            assert!(
                trace.live[self.family],
                "the native payload is destroyed once"
            );
            if self.family == 1 {
                assert!(
                    trace.live[0],
                    "the borrowed parent remains live at child destruction"
                );
            } else {
                assert!(
                    !trace.live[1],
                    "a parent cannot be destroyed before its child"
                );
            }
            drop(storage);
            trace.live[self.family] = false;
            trace.events.push(Event::Destroyed(self.family));
        }
    }
}
impl Drop for Owner {
    fn drop(&mut self) {
        self.destroy();
    }
}
impl NativeResourceOwner for Owner {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}
#[derive(Debug)]
struct Binding {
    manifest: Arc<ForeignManifest>,
    trace: Observations,
}
impl Binding {
    fn authenticate(&self, module: &ForeignModuleFact) -> Result<(), ForeignExecutionError> {
        if Arc::ptr_eq(module.manifest(), &self.manifest) {
            Ok(())
        } else {
            Err(ForeignExecutionError("wrong original acquisition manifest"))
        }
    }
    fn owner<'a>(&self, states: &'a [&dyn NativeResourceOwner], family: usize) -> &'a Owner {
        let [state] = states else {
            panic!("one exact borrowed state")
        };
        let owner = state.as_any().downcast_ref::<Owner>().unwrap();
        assert_eq!(owner.family, family);
        assert!(Rc::ptr_eq(&owner.trace, &self.trace));
        assert!(owner.storage.is_some() && self.trace.borrow().live[family]);
        owner
    }
}
impl ExecutableForeignModule for Binding {
    fn preflight(&self, module: &ForeignModuleFact) -> Result<(), ForeignExecutionError> {
        self.authenticate(module)
    }
    fn acquire(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignAcquisition, ForeignExecutionError> {
        self.authenticate(module)?;
        assert_eq!(key.operation, 0);
        let value = match key.effect {
            0 => {
                assert!(states.is_empty());
                let Some(ForeignDataNode::Integer(value)) = input.node(input.root()) else {
                    panic!("parent input is its registered integer")
                };
                value.to_i64().unwrap()
            }
            1 => {
                self.owner(states, 0);
                let Some(ForeignDataNode::Tuple(fields)) = input.node(input.root()) else {
                    panic!("child input is its registered state/integer tuple")
                };
                assert_eq!(fields.len(), 2);
                assert!(matches!(
                    input.node(fields[0]),
                    Some(ForeignDataNode::State(0))
                ));
                let Some(ForeignDataNode::Integer(value)) = input.node(fields[1]) else {
                    panic!("child input is its registered integer")
                };
                value.to_i64().unwrap()
            }
            _ => panic!("only the exact parent and child acquisitions are executed"),
        };
        let mut storage = Vec::new();
        storage
            .try_reserve_exact(1)
            .map_err(|_| ForeignExecutionError::STORAGE_REFUSED)?;
        storage.push(value);
        let mut trace = self.trace.borrow_mut();
        assert!(!trace.live[key.effect]);
        trace.live[key.effect] = true;
        trace.events.push(Event::Acquired(key.effect));
        drop(trace);
        Ok(ForeignAcquisition::Acquired(Box::new(Owner {
            family: key.effect,
            storage: Some(storage.into_boxed_slice()),
            trace: Rc::clone(&self.trace),
        })))
    }
    fn invoke(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignData, ForeignExecutionError> {
        self.authenticate(module)?;
        assert_eq!(key.operation, 1);
        assert!(matches!(
            input.node(input.root()),
            Some(ForeignDataNode::State(0))
        ));
        let value = self.owner(states, key.effect).storage.as_ref().unwrap()[0];
        self.trace
            .borrow_mut()
            .events
            .push(Event::Borrowed(key.effect));
        ForeignData::new(
            vec![ForeignDataNode::Integer(crate::integer::Integer::from_i64(
                value,
            ))],
            0,
        )
    }
    fn finish(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        owner: &mut dyn NativeResourceOwner,
        context: ForeignFinishContext,
    ) -> Result<ForeignCompletion, ForeignExecutionError> {
        self.authenticate(module)?;
        assert_eq!(key.operation, 2);
        assert!(!context.retained_dependents);
        let owner = owner.as_any_mut().downcast_mut::<Owner>().unwrap();
        assert_eq!(owner.family, key.effect);
        self.trace
            .borrow_mut()
            .events
            .push(Event::Finished(key.effect));
        owner.destroy();
        Ok(ForeignCompletion::Closed)
    }
}

fn ty(
    name: &str,
    parameters: &[&str],
    opaque_state: bool,
    constructors: &[(&str, Option<&str>)],
) -> ForeignTypeDeclaration {
    ForeignTypeDeclaration {
        name: name.into(),
        parameters: parameters.iter().map(|name| (*name).into()).collect(),
        opaque_state,
        constructors: constructors
            .iter()
            .map(|(name, payload)| ForeignConstructorDeclaration {
                name: (*name).into(),
                payload: payload.map(str::to_owned),
            })
            .collect(),
    }
}
fn operation(
    name: &str,
    signature: &str,
    role: ForeignOperationRole,
    state_operands: Vec<Vec<usize>>,
    retained_arguments: Vec<usize>,
    result: ForeignResultRelation,
) -> ForeignOperationDeclaration {
    ForeignOperationDeclaration {
        name: name.into(),
        signature: signature.into(),
        role,
        owned_identity_position: 0,
        state_operands,
        retained_arguments,
        result,
    }
}
fn effect(
    name: &str,
    state: &str,
    parameters: &[&str],
    acquire: &str,
    borrowed: Vec<Vec<usize>>,
    retained: Vec<usize>,
) -> ForeignEffectDeclaration {
    ForeignEffectDeclaration {
        name: name.into(),
        parameters: parameters.iter().map(|name| (*name).into()).collect(),
        operations: vec![
            operation(
                "acquire",
                acquire,
                ForeignOperationRole::Acquire,
                borrowed,
                if retained.is_empty() { vec![] } else { vec![0] },
                ForeignResultRelation::Acquire {
                    state: state.into(),
                    error: "InitError".into(),
                    report: "Acquire".into(),
                    retained_parameters: retained,
                },
            ),
            operation(
                "read",
                &format!("{state}<{}> -> Int", parameters.join(", ")),
                ForeignOperationRole::Borrow,
                vec![vec![]],
                vec![],
                ForeignResultRelation::Independent,
            ),
            operation(
                "finish",
                &format!(
                    "{state}<{}> -> Finish<{state}<{}>, FinishError>",
                    parameters.join(", "),
                    parameters.join(", ")
                ),
                ForeignOperationRole::Finish,
                vec![vec![]],
                vec![],
                ForeignResultRelation::Finish {
                    state: state.into(),
                    error: "FinishError".into(),
                    report: "Finish".into(),
                },
            ),
        ],
    }
}
fn manifest() -> ForeignManifest {
    ForeignManifest::new(
        "@foreign.retention",
        ForeignRegistrationId::new(2),
        ForeignManifestSchema {
            types: vec![
                ty("ParentState", &["R"], true, &[]),
                ty("ChildState", &["S", "R"], true, &[]),
                ty("InitError", &[], false, &[("InitRefused", None)]),
                ty("FinishError", &[], false, &[("FinishRefused", None)]),
                ty(
                    "Acquire",
                    &["State", "E"],
                    false,
                    &[("Acquired", Some("State")), ("Refused", Some("E"))],
                ),
                ty(
                    "Finish",
                    &["State", "E"],
                    false,
                    &[
                        ("Consumed", None),
                        ("ConsumedFailure", Some("E")),
                        ("Retained", Some("State, E")),
                    ],
                ),
            ],
            effects: vec![
                effect(
                    "Parent",
                    "ParentState",
                    &["R"],
                    "Int -> Acquire<ParentState<R>, InitError>",
                    vec![],
                    vec![],
                ),
                effect(
                    "Child",
                    "ChildState",
                    &["S", "R"],
                    "(ParentState<R>, Int) -> Acquire<ChildState<S, R>, InitError>",
                    vec![vec![0]],
                    vec![1],
                ),
            ],
            state_access: None,
        },
    )
    .unwrap()
}

fn checked_fixture(roots: &ModuleRoots) -> crate::core::ValidatedEffectProgram {
    let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/provider-experiments/publication-source/entry.ash");
    let graph = load_module_graph(&entry, roots).unwrap();
    let mut checked = Vec::<crate::resolved::CheckedModule>::new();
    let mut availability = crate::elaborate::ProviderCodeAvailability::default();
    let mut resolution = TypeWorkBudget::default();
    let mut checking = TypeWorkBudget::default();
    let mut constraints = crate::interface::InterfaceConstraintBudget::default();
    let mut coverage = crate::pattern::UsefulnessBudget::default();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                crate::resolve::DependencyExports::new(
                    edge,
                    checked
                        .iter()
                        .find(|module| module.module() == edge.target())
                        .unwrap()
                        .exports(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let resolved = crate::resolve::resolve_module_with_budget(
            loaded,
            &dependencies,
            &mut resolution,
            &mut constraints,
        )
        .unwrap();
        let module = crate::elaborate::check_module_with_budget_and_provider_codes(
            resolved,
            &availability,
            &mut checking,
            &mut coverage,
            &mut constraints,
        )
        .unwrap();
        if let Some(code) = module.provider_code() {
            availability
                .retain(module.module(), code, &mut checking)
                .unwrap();
        }
        checked.push(module);
    }
    let linked = crate::evidence_validation::validate_interface_evidence(
        crate::elaborate::link_modules(checked, graph.entry()).unwrap(),
    )
    .unwrap();
    let mut elaborator = crate::elaborate::EffectElaborator::for_module_program(&linked).unwrap();
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .unwrap();
    let unchecked = elaborator.finish(typed.node).unwrap();
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let relation = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    crate::core::validate_effect_modules(unchecked, &sources, &relation).unwrap()
}
fn runtime(registrations: &ForeignRegistrations) -> (ForeignRuntime, Observations) {
    let trace = Rc::new(RefCell::new(Trace {
        events: Vec::with_capacity(8),
        live: [false; 2],
    }));
    let original = Arc::clone(registrations.get("@foreign.retention").unwrap());
    let runtime = ForeignRuntime::new(vec![ForeignRuntimeBinding::new(
        Arc::clone(&original),
        Box::new(Binding {
            manifest: original,
            trace: Rc::clone(&trace),
        }),
    )])
    .unwrap();
    (runtime, trace)
}
#[test]
fn terminal_acquisition_publication_refusal_destroys_unpublished_child_before_outer_host_teardown()
{
    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
        manifest(),
    ])
    .unwrap();
    let roots = ModuleRoots::empty().with_foreign_registrations(registrations.clone());
    let program = checked_fixture(&roots);
    let mut pending = vec![program.root()];
    let mut child_body = None;
    let mut wrapping = None;
    let mut seen = std::collections::HashSet::new();
    while let Some(node) = pending.pop() {
        if !seen.insert(node) {
            continue;
        }
        let expression = program.node(node).unwrap();
        if let EffectExprKind::Pure(PureExprKind::Value(PureValue::String(text))) = &expression.kind
            && text.bytes().as_ref() == b"acquired"
        {
            assert!(wrapping.replace(node).is_none());
        }
        if let EffectExprKind::Operation(EffectOperation::ProviderScope(scope)) = &expression.kind
            && scope.descriptor.native_effect().effect().declaration() == 1
        {
            assert!(child_body.replace(scope.handler().body()).is_none());
        }
        pending
            .extend((0..expression.kind.child_count()).filter_map(|i| expression.kind.child_at(i)));
    }
    let child_body = child_body.expect("one checked child scope");
    let observed = Arc::new(std::sync::Mutex::new(Vec::new()));
    let (mut measured_runtime, measured_native) = runtime(&registrations);
    let mut measured = Machine::new_effect(&program);
    measured.foreign_runtime = Some(&mut measured_runtime);
    measured.work_trace = Some(Arc::clone(&observed));
    let completed = measured.run().unwrap();
    assert_eq!(
        completed.value.to_string(),
        "Completed(Completed(42, Closed), Closed)"
    );
    assert_eq!(measured_runtime.retained_owner_count(), 0);
    assert_eq!(
        measured_native.borrow().events,
        vec![
            Event::Acquired(0),
            Event::Borrowed(0),
            Event::Acquired(1),
            Event::Borrowed(1),
            Event::Finished(1),
            Event::Destroyed(1),
            Event::Finished(0),
            Event::Destroyed(0)
        ]
    );
    let publication = observed
        .lock()
        .unwrap()
        .iter()
        .find(|(node, _)| *node == child_body)
        .map(|(_, used)| *used)
        .unwrap();
    // The direct successful native report is a constructor location. Its
    // resolution is the final one-unit charge before source body publication.
    let before_publication = publication.checked_sub(1).unwrap();
    let wrapping = wrapping.expect("one pure report-wrapping string");
    let wrapping_used = observed
        .lock()
        .unwrap()
        .iter()
        .find(|(node, _)| *node == wrapping)
        .map(|(_, used)| *used)
        .unwrap();
    // This charge occurs after native acquisition but before its source
    // report returns: the guard is still in the active Acquire frame.
    for (cut, phase, requested) in [
        (wrapping_used, RuntimePhase::Evaluation, b"acquired".len()),
        (before_publication, RuntimePhase::Acquisition, 1),
    ] {
        for prefill in [0, 7] {
            let (mut host, native) = runtime(&registrations);
            let rejected_trace = Arc::new(std::sync::Mutex::new(Vec::new()));
            let mut rejected = Machine::new_effect(&program);
            rejected.foreign_runtime = Some(&mut host);
            rejected.work_trace = Some(Arc::clone(&rejected_trace));
            rejected.instantiation_work = TypeWorkBudget::with_limit(cut + prefill);
            rejected.instantiation_work.charge(prefill).unwrap();
            let RuntimeFailure::Report(report) = rejected.run().unwrap_err() else {
                panic!("publication work refusal has a terminal resource report")
            };
            let details = report.primary.resource().unwrap();
            assert_eq!(details.cause, ResourceFailureCause::WorkBudgetExhausted);
            assert_eq!(details.phase, phase);
            assert_eq!(details.resource, RuntimeResource::WorkUnits);
            assert_eq!(
                (details.requested, details.available),
                (Some(requested), Some(0))
            );
            assert!(report.teardown.is_none());
            assert_eq!(report.cleanup, CleanupStatus::Complete);
            assert!(
                !rejected_trace
                    .lock()
                    .unwrap()
                    .iter()
                    .any(|(node, _)| *node == child_body)
            );
            assert_eq!(
                host.retained_owner_count(),
                1,
                "only the active outer guard remains quarantined"
            );
            assert_eq!(native.borrow().live, [true, false]);
            assert_eq!(
                native.borrow().events,
                vec![
                    Event::Acquired(0),
                    Event::Borrowed(0),
                    Event::Acquired(1),
                    Event::Destroyed(1)
                ]
            );
            drop(host);
            assert_eq!(native.borrow().live, [false; 2]);
            assert_eq!(
                native.borrow().events,
                vec![
                    Event::Acquired(0),
                    Event::Borrowed(0),
                    Event::Acquired(1),
                    Event::Destroyed(1),
                    Event::Destroyed(0)
                ]
            );
        }
    }
    // A fresh exact full-run ledger executes the same checked source and
    // honest native protocol; refusal never schedules a source finish retry.
    let (mut fresh_host, fresh_native) = runtime(&registrations);
    let mut fresh = Machine::new_effect(&program);
    fresh.foreign_runtime = Some(&mut fresh_host);
    fresh.instantiation_work = TypeWorkBudget::with_limit(completed.runtime_work);
    let retried = fresh.run().unwrap();
    assert_eq!(retried.value.to_string(), completed.value.to_string());
    assert_eq!(retried.runtime_work, completed.runtime_work);
    assert_eq!(fresh_host.retained_owner_count(), 0);
    assert_eq!(
        fresh_native.borrow().events,
        measured_native.borrow().events
    );
}
