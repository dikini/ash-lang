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
            ForeignDataNode, ForeignExecutionError, ForeignFinishContext, ForeignInvocation,
            ForeignInvocationWork, ForeignOperationKey, ForeignRuntime, ForeignRuntimeBinding,
            NativeInvocationCommit, NativeResourceOwner,
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
    runtime_with_binding(registrations, |binding| Box::new(binding))
}
fn runtime_with_binding(
    registrations: &ForeignRegistrations,
    executable: impl FnOnce(Binding) -> Box<dyn ExecutableForeignModule>,
) -> (ForeignRuntime, Observations) {
    let trace = Rc::new(RefCell::new(Trace {
        events: Vec::with_capacity(8),
        live: [false; 2],
    }));
    let original = Arc::clone(registrations.get("@foreign.retention").unwrap());
    let runtime = ForeignRuntime::new(vec![ForeignRuntimeBinding::new(
        Arc::clone(&original),
        executable(Binding {
            manifest: original,
            trace: Rc::clone(&trace),
        }),
    )])
    .unwrap();
    (runtime, trace)
}

#[derive(Debug)]
struct PublicationBinding {
    inner: Binding,
    publications: Rc<RefCell<[usize; 2]>>,
    pending: Rc<RefCell<PendingTrace>>,
    invalid_result: bool,
}
#[derive(Debug, Default)]
struct PendingTrace {
    prepared: usize,
    committed: usize,
    abandoned: usize,
}
#[derive(Debug)]
struct PendingPublication {
    manifest: Arc<ForeignManifest>,
    key: ForeignOperationKey,
    // Nonowning identity only; neither this address nor the trace retains an owner.
    owner_address: usize,
    owner_trace: Observations,
    publications: Rc<RefCell<[usize; 2]>>,
    candidate: usize,
    pending: Rc<RefCell<PendingTrace>>,
    published: bool,
}
impl Drop for PendingPublication {
    fn drop(&mut self) {
        if !self.published {
            self.pending.borrow_mut().abandoned += 1;
        }
    }
}
impl NativeInvocationCommit for PendingPublication {
    fn commit(
        mut self: Box<Self>,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<(), ForeignExecutionError> {
        if key != self.key || !Arc::ptr_eq(module.manifest(), &self.manifest) {
            return Err(ForeignExecutionError("wrong original staged invocation"));
        }
        let [state] = states else {
            return Err(ForeignExecutionError("wrong staged owner count"));
        };
        let owner = state
            .as_any()
            .downcast_ref::<Owner>()
            .ok_or(ForeignExecutionError("wrong staged owner type"))?;
        if owner as *const Owner as usize != self.owner_address
            || owner.family != key.effect
            || !Rc::ptr_eq(&owner.trace, &self.owner_trace)
            || owner.storage.is_none()
            || !owner.trace.borrow().live[key.effect]
        {
            return Err(ForeignExecutionError("wrong or inactive staged owner"));
        }
        let mut publications = self.publications.borrow_mut();
        let current = publications
            .get_mut(key.effect)
            .ok_or(ForeignExecutionError("wrong staged publication family"))?;
        if *current != self.candidate {
            return Err(ForeignExecutionError("stale staged publication candidate"));
        }
        let next = current
            .checked_add(1)
            .ok_or(ForeignExecutionError("staged publication count exhausted"))?;
        let mut pending = self.pending.borrow_mut();
        let committed = pending
            .committed
            .checked_add(1)
            .ok_or(ForeignExecutionError("staged commit count exhausted"))?;
        *current = next;
        self.published = true;
        pending.committed = committed;
        Ok(())
    }
}
impl ExecutableForeignModule for PublicationBinding {
    fn preflight(&self, module: &ForeignModuleFact) -> Result<(), ForeignExecutionError> {
        self.inner.preflight(module)
    }
    fn acquire(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignAcquisition, ForeignExecutionError> {
        self.inner.acquire(key, module, input, states)
    }
    fn invoke(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignData, ForeignExecutionError> {
        let output = self.inner.invoke(key, module, input, states)?;
        // The current immediate API publishes before evaluator result admission.
        self.publications.borrow_mut()[key.effect] += 1;
        if self.invalid_result {
            ForeignData::new(vec![ForeignDataNode::Boolean(false)], 0)
        } else {
            Ok(output)
        }
    }
    fn prepare_invoke(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignInvocation, ForeignExecutionError> {
        let original_output = self.inner.invoke(key, module, input, states)?;
        let owner = self.inner.owner(states, key.effect);
        let output = if self.invalid_result {
            ForeignData::new(vec![ForeignDataNode::Boolean(false)], 0)?
        } else {
            original_output
        };
        self.pending.borrow_mut().prepared += 1;
        Ok(ForeignInvocation::Prepared {
            output,
            commit: Box::new(PendingPublication {
                manifest: Arc::clone(&self.inner.manifest),
                key,
                owner_address: owner as *const Owner as usize,
                owner_trace: Rc::clone(&owner.trace),
                publications: Rc::clone(&self.publications),
                candidate: self.publications.borrow()[key.effect],
                pending: Rc::clone(&self.pending),
                published: false,
            }),
        })
    }
    fn finish(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        owner: &mut dyn NativeResourceOwner,
        context: ForeignFinishContext,
    ) -> Result<ForeignCompletion, ForeignExecutionError> {
        self.inner.finish(key, module, owner, context)
    }
}

// Intentionally omits prepare_invoke so the real default preserves old effects.
#[derive(Debug)]
struct LegacyPublicationBinding(PublicationBinding);
impl ExecutableForeignModule for LegacyPublicationBinding {
    fn preflight(&self, module: &ForeignModuleFact) -> Result<(), ForeignExecutionError> {
        self.0.preflight(module)
    }
    fn acquire(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignAcquisition, ForeignExecutionError> {
        self.0.acquire(key, module, input, states)
    }
    fn invoke(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignData, ForeignExecutionError> {
        self.0.invoke(key, module, input, states)
    }
    fn finish(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        owner: &mut dyn NativeResourceOwner,
        context: ForeignFinishContext,
    ) -> Result<ForeignCompletion, ForeignExecutionError> {
        self.0.finish(key, module, owner, context)
    }
}

#[derive(Debug)]
struct MeteredPublicationBinding {
    inner: PublicationBinding,
    charges: [usize; 2],
    swallow_failure: bool,
    attempts: Rc<RefCell<Vec<usize>>>,
}
impl ExecutableForeignModule for MeteredPublicationBinding {
    fn preflight(&self, module: &ForeignModuleFact) -> Result<(), ForeignExecutionError> {
        self.inner.preflight(module)
    }
    fn acquire(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignAcquisition, ForeignExecutionError> {
        self.inner.acquire(key, module, input, states)
    }
    fn invoke(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignData, ForeignExecutionError> {
        self.inner.invoke(key, module, input, states)
    }
    fn prepare_invoke(
        &self,
        _key: ForeignOperationKey,
        _module: &ForeignModuleFact,
        _input: &ForeignData,
        _states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignInvocation, ForeignExecutionError> {
        panic!("the evaluator must use the metered preparation entry")
    }
    fn prepare_invoke_with_work(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
        work: &mut ForeignInvocationWork<'_>,
    ) -> Result<ForeignInvocation, ForeignExecutionError> {
        for units in self.charges {
            self.attempts.borrow_mut().push(units);
            if let Err(error) = work.charge(units) {
                if !self.swallow_failure {
                    return Err(error);
                }
                // A smaller later debit must not erase the first refusal or
                // authorize the pending publication returned below.
                self.attempts.borrow_mut().push(1);
                assert!(work.charge(1).is_err());
                break;
            }
        }
        self.inner.prepare_invoke(key, module, input, states)
    }
    fn finish(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        owner: &mut dyn NativeResourceOwner,
        context: ForeignFinishContext,
    ) -> Result<ForeignCompletion, ForeignExecutionError> {
        self.inner.finish(key, module, owner, context)
    }
}

fn publication_fixture() -> (ForeignRegistrations, crate::core::ValidatedEffectProgram) {
    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
        manifest(),
    ])
    .unwrap();
    let roots = ModuleRoots::empty().with_foreign_registrations(registrations.clone());
    let program = checked_fixture(&roots);
    (registrations, program)
}

#[test]
fn staged_borrow_metered_preparation_adds_only_adapter_charges() {
    let (registrations, program) = publication_fixture();
    let mut outcomes = Vec::new();
    for metered in [false, true] {
        let publications = Rc::new(RefCell::new([0; 2]));
        let pending = Rc::new(RefCell::new(PendingTrace::default()));
        let attempts = Rc::new(RefCell::new(Vec::new()));
        let (mut host, native) = runtime_with_binding(&registrations, |inner| {
            let binding = PublicationBinding {
                inner,
                publications: Rc::clone(&publications),
                pending: Rc::clone(&pending),
                invalid_result: false,
            };
            if metered {
                Box::new(MeteredPublicationBinding {
                    inner: binding,
                    charges: [3, 5],
                    swallow_failure: false,
                    attempts: Rc::clone(&attempts),
                })
            } else {
                // This adapter overrides only the old prepare entry. The new
                // default must preserve its two calls without a work tariff.
                Box::new(binding)
            }
        });
        let mut machine = Machine::new_effect(&program);
        machine.foreign_runtime = Some(&mut host);
        let completed = machine.run().unwrap();
        assert_eq!(
            completed.value.to_string(),
            "Completed(Completed(42, Closed), Closed)"
        );
        assert_eq!(*publications.borrow(), [1, 1]);
        assert_eq!(pending.borrow().prepared, 2);
        assert_eq!(pending.borrow().committed, 2);
        assert_eq!(pending.borrow().abandoned, 0);
        assert_eq!(host.retained_owner_count(), 0);
        assert_eq!(native.borrow().live, [false; 2]);
        if metered {
            assert_eq!(*attempts.borrow(), vec![3, 5, 3, 5]);
        } else {
            assert!(attempts.borrow().is_empty());
        }
        outcomes.push((completed.runtime_work, native.borrow().events.clone()));
    }
    assert_eq!(outcomes[1].0, outcomes[0].0 + 16);
    assert_eq!(outcomes[1].1, outcomes[0].1);
    assert_eq!(
        outcomes[0]
            .1
            .iter()
            .filter(|event| matches!(event, Event::Borrowed(_)))
            .count(),
        2,
        "the default invokes old preparation exactly once per native read"
    );
}

fn assert_metered_preparation_refusal(swallow_failure: bool) {
    let (registrations, program) = publication_fixture();
    let (mut measured_host, _) = runtime(&registrations);
    let mut measured = Machine::new_effect(&program);
    measured.foreign_runtime = Some(&mut measured_host);
    let completed = measured.run().unwrap();
    // Measure the actual preparation entry without reproducing the evaluator's
    // codec or owner-lookup costs. This budget reaches the first read, where an
    // intentionally impossible second debit reports the remaining work.
    let probe_limit = completed.runtime_work.checked_add(64).unwrap();
    let publications = Rc::new(RefCell::new([0; 2]));
    let pending = Rc::new(RefCell::new(PendingTrace::default()));
    let attempts = Rc::new(RefCell::new(Vec::new()));
    let (mut probe_host, probe_native) = runtime_with_binding(&registrations, |inner| {
        Box::new(MeteredPublicationBinding {
            inner: PublicationBinding {
                inner,
                publications: Rc::clone(&publications),
                pending: Rc::clone(&pending),
                invalid_result: false,
            },
            charges: [3, usize::MAX],
            swallow_failure: false,
            attempts: Rc::clone(&attempts),
        })
    });
    let mut probe = Machine::new_effect(&program);
    probe.foreign_runtime = Some(&mut probe_host);
    probe.instantiation_work = TypeWorkBudget::with_limit(probe_limit);
    let RuntimeFailure::Report(report) = probe.run().unwrap_err() else {
        panic!("the measuring debit must retain a resource report")
    };
    let details = report.primary.resource().unwrap();
    assert_eq!(details.cause, ResourceFailureCause::WorkBudgetExhausted);
    assert_eq!(details.phase, RuntimePhase::Access);
    assert_eq!(details.resource, RuntimeResource::WorkUnits);
    assert_eq!(details.requested, Some(usize::MAX));
    let available = details.available.unwrap();
    assert!(available > 0);
    let after_first_charge = probe_limit.checked_sub(available).unwrap();
    assert_eq!(*attempts.borrow(), vec![3, usize::MAX]);
    assert_eq!(*publications.borrow(), [0, 0]);
    assert_eq!(pending.borrow().prepared, 0);
    assert_eq!(probe_host.retained_owner_count(), 1);
    drop(probe_host);
    assert_eq!(probe_native.borrow().live, [false; 2]);

    for prefill in [0, 7] {
        let publications = Rc::new(RefCell::new([0; 2]));
        let pending = Rc::new(RefCell::new(PendingTrace::default()));
        let attempts = Rc::new(RefCell::new(Vec::new()));
        let (mut host, native) = runtime_with_binding(&registrations, |inner| {
            Box::new(MeteredPublicationBinding {
                inner: PublicationBinding {
                    inner,
                    publications: Rc::clone(&publications),
                    pending: Rc::clone(&pending),
                    invalid_result: false,
                },
                charges: [3, 5],
                swallow_failure,
                attempts: Rc::clone(&attempts),
            })
        });
        let mut rejected = Machine::new_effect(&program);
        rejected.foreign_runtime = Some(&mut host);
        rejected.instantiation_work = TypeWorkBudget::with_limit(after_first_charge + 2 + prefill);
        rejected.instantiation_work.charge(prefill).unwrap();
        let RuntimeFailure::Report(report) = rejected.run().unwrap_err() else {
            panic!("adapter work refusal must retain its measured resource report")
        };
        let details = report.primary.resource().unwrap();
        assert_eq!(details.cause, ResourceFailureCause::WorkBudgetExhausted);
        assert_eq!(details.phase, RuntimePhase::Access);
        assert_eq!(details.resource, RuntimeResource::WorkUnits);
        assert_eq!((details.requested, details.available), (Some(5), Some(2)));
        assert!(report.teardown.is_none());
        assert_eq!(report.cleanup, CleanupStatus::Complete);
        assert_eq!(*publications.borrow(), [0, 0]);
        let prepared = usize::from(swallow_failure);
        assert_eq!(pending.borrow().prepared, prepared);
        assert_eq!(pending.borrow().committed, 0);
        assert_eq!(pending.borrow().abandoned, prepared);
        let expected_events = if swallow_failure {
            assert_eq!(*attempts.borrow(), vec![3, 5, 1]);
            vec![Event::Acquired(0), Event::Borrowed(0)]
        } else {
            assert_eq!(*attempts.borrow(), vec![3, 5]);
            vec![Event::Acquired(0)]
        };
        assert_eq!(native.borrow().events, expected_events);
        assert_eq!(host.retained_owner_count(), 1);
        assert_eq!(native.borrow().live, [true, false]);
        drop(host);
        assert_eq!(native.borrow().live, [false; 2]);
        let mut destroyed_events = expected_events;
        destroyed_events.push(Event::Destroyed(0));
        assert_eq!(
            native.borrow().events,
            destroyed_events,
            "neither pending preparation nor its drop keeps the native owner alive"
        );
    }
}

#[test]
fn staged_borrow_preparation_work_refusal_precedes_native_publication() {
    assert_metered_preparation_refusal(false);
}

#[test]
fn staged_borrow_swallowed_work_refusal_abandons_prepared_publication() {
    assert_metered_preparation_refusal(true);
}

#[test]
fn staged_borrow_result_type_refusal_precedes_native_publication() {
    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
        manifest(),
    ])
    .unwrap();
    let roots = ModuleRoots::empty().with_foreign_registrations(registrations.clone());
    let program = checked_fixture(&roots);
    let publications = Rc::new(RefCell::new([0; 2]));
    let pending = Rc::new(RefCell::new(PendingTrace::default()));
    let (mut host, native) = runtime_with_binding(&registrations, |inner| {
        Box::new(PublicationBinding {
            inner,
            publications: Rc::clone(&publications),
            pending: Rc::clone(&pending),
            invalid_result: true,
        })
    });
    let mut machine = Machine::new_effect(&program);
    machine.foreign_runtime = Some(&mut host);
    assert!(matches!(machine.run(), Err(RuntimeFailure::ForeignBinding)));
    assert_eq!(
        native.borrow().events,
        vec![Event::Acquired(0), Event::Borrowed(0)],
        "the checked source reaches the native read before result type rejection"
    );
    assert_eq!(
        *publications.borrow(),
        [0, 0],
        "rejecting Bool for the registered Int result must not publish native state"
    );
    assert_eq!(pending.borrow().prepared, 1);
    assert_eq!(pending.borrow().committed, 0);
    assert_eq!(pending.borrow().abandoned, 1);
}

#[test]
fn staged_borrow_valid_results_publish_once_per_native_call() {
    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
        manifest(),
    ])
    .unwrap();
    let roots = ModuleRoots::empty().with_foreign_registrations(registrations.clone());
    let program = checked_fixture(&roots);
    let publications = Rc::new(RefCell::new([0; 2]));
    let pending = Rc::new(RefCell::new(PendingTrace::default()));
    let (mut host, native) = runtime_with_binding(&registrations, |inner| {
        Box::new(PublicationBinding {
            inner,
            publications: Rc::clone(&publications),
            pending: Rc::clone(&pending),
            invalid_result: false,
        })
    });
    let mut machine = Machine::new_effect(&program);
    machine.foreign_runtime = Some(&mut host);
    let completed = machine.run().unwrap();
    assert_eq!(
        completed.value.to_string(),
        "Completed(Completed(42, Closed), Closed)"
    );
    assert_eq!(*publications.borrow(), [1, 1]);
    assert_eq!(host.retained_owner_count(), 0);
    assert_eq!(native.borrow().live, [false; 2]);
    assert_eq!(pending.borrow().prepared, 2);
    assert_eq!(pending.borrow().committed, 2);
    assert_eq!(pending.borrow().abandoned, 0);
}

#[test]
fn staged_borrow_legacy_immediate_result_refusal_preserves_existing_publication() {
    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
        manifest(),
    ])
    .unwrap();
    let roots = ModuleRoots::empty().with_foreign_registrations(registrations.clone());
    let program = checked_fixture(&roots);
    let publications = Rc::new(RefCell::new([0; 2]));
    let pending = Rc::new(RefCell::new(PendingTrace::default()));
    let (mut host, native) = runtime_with_binding(&registrations, |inner| {
        Box::new(LegacyPublicationBinding(PublicationBinding {
            inner,
            publications: Rc::clone(&publications),
            pending: Rc::clone(&pending),
            invalid_result: true,
        }))
    });
    let mut machine = Machine::new_effect(&program);
    machine.foreign_runtime = Some(&mut host);
    assert!(matches!(machine.run(), Err(RuntimeFailure::ForeignBinding)));
    assert_eq!(
        native.borrow().events,
        vec![Event::Acquired(0), Event::Borrowed(0)]
    );
    assert_eq!(*publications.borrow(), [1, 0]);
    assert_eq!(pending.borrow().prepared, 0);
    assert_eq!(pending.borrow().committed, 0);
    assert_eq!(pending.borrow().abandoned, 0);
}

#[test]
fn staged_borrow_pending_drop_and_foreign_or_stale_commit_do_not_publish() {
    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
        manifest(),
    ])
    .unwrap();
    let roots = ModuleRoots::empty().with_foreign_registrations(registrations.clone());
    let program = checked_fixture(&roots);
    let original = Arc::clone(registrations.get("@foreign.retention").unwrap());
    let module = program
        .registry()
        .foreign_modules()
        .find(|module| Arc::ptr_eq(module.manifest(), &original))
        .unwrap();
    let foreign_module = program
        .registry()
        .foreign_modules()
        .find(|module| !Arc::ptr_eq(module.manifest(), &original))
        .unwrap();
    let (_, native) = runtime(&registrations);
    let publications = Rc::new(RefCell::new([0; 2]));
    let pending = Rc::new(RefCell::new(PendingTrace::default()));
    let binding = PublicationBinding {
        inner: Binding {
            manifest: Arc::clone(&original),
            trace: Rc::clone(&native),
        },
        publications: Rc::clone(&publications),
        pending: Rc::clone(&pending),
        invalid_result: false,
    };
    let acquisition_key = ForeignOperationKey {
        effect: 0,
        operation: 0,
    };
    let read_key = ForeignOperationKey {
        effect: 0,
        operation: 1,
    };
    let input = ForeignData::new(
        vec![ForeignDataNode::Integer(crate::integer::Integer::from_i64(
            20,
        ))],
        0,
    )
    .unwrap();
    let ForeignAcquisition::Acquired(owner) = binding
        .acquire(acquisition_key, module, &input, &[])
        .unwrap()
    else {
        panic!("the real acquisition supplies the unique owner")
    };
    let state_input = ForeignData::new(vec![ForeignDataNode::State(0)], 0).unwrap();
    let states = [owner.as_ref()];
    let prepare = || {
        let ForeignInvocation::Prepared { commit, .. } = binding
            .prepare_invoke(read_key, module, &state_input, &states)
            .unwrap()
        else {
            panic!("this binding stages each borrowed invocation")
        };
        commit
    };
    drop(prepare());
    assert_eq!(*publications.borrow(), [0, 0]);
    assert_eq!(pending.borrow().abandoned, 1);
    assert!(prepare().commit(read_key, foreign_module, &states).is_err());
    assert!(prepare().commit(acquisition_key, module, &states).is_err());

    let (_, foreign_trace) = runtime(&registrations);
    let foreign_binding = Binding {
        manifest: original,
        trace: Rc::clone(&foreign_trace),
    };
    let ForeignAcquisition::Acquired(foreign_owner) = foreign_binding
        .acquire(acquisition_key, module, &input, &[])
        .unwrap()
    else {
        panic!("a separate acquisition supplies a genuinely different unique owner")
    };
    assert!(
        prepare()
            .commit(read_key, module, &[foreign_owner.as_ref()])
            .is_err()
    );
    assert_eq!(*publications.borrow(), [0, 0]);
    assert_eq!(pending.borrow().committed, 0);
    assert_eq!(pending.borrow().abandoned, 4);

    let first = prepare();
    let stale = prepare();
    first.commit(read_key, module, &states).unwrap();
    assert_eq!(*publications.borrow(), [1, 0]);
    assert!(stale.commit(read_key, module, &states).is_err());
    assert_eq!(*publications.borrow(), [1, 0]);
    assert_eq!(pending.borrow().prepared, 6);
    assert_eq!(pending.borrow().committed, 1);
    assert_eq!(pending.borrow().abandoned, 5);
    drop(owner);
    drop(foreign_owner);
    assert_eq!(native.borrow().live, [false; 2]);
    assert_eq!(foreign_trace.borrow().live, [false; 2]);
}

#[test]
fn staged_borrow_decode_work_refusal_drops_pending_before_native_publication() {
    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
        manifest(),
    ])
    .unwrap();
    let roots = ModuleRoots::empty().with_foreign_registrations(registrations.clone());
    let program = checked_fixture(&roots);
    let original = registrations.get("@foreign.retention").unwrap();
    let native = program
        .registry()
        .foreign_modules()
        .find(|module| Arc::ptr_eq(module.manifest(), original))
        .unwrap();
    let parent_read = native
        .operations
        .iter()
        .find(|operation| {
            operation.id.owner() == native.effects[0]
                && operation.role == ForeignOperationRole::Borrow
        })
        .unwrap()
        .id;
    let mut pending_nodes = vec![program.root()];
    let mut seen = std::collections::HashSet::new();
    let mut parent_operand = None;
    let mut child_scope = None;
    while let Some(node) = pending_nodes.pop() {
        if !seen.insert(node) {
            continue;
        }
        let expression = program.node(node).unwrap();
        match &expression.kind {
            EffectExprKind::Operation(EffectOperation::Request(request))
                if request.operation() == parent_read =>
            {
                let operand = request.operand();
                assert!(matches!(
                    &program.node(operand).unwrap().kind,
                    EffectExprKind::Pure(PureExprKind::Variable(_))
                ));
                assert!(parent_operand.replace(operand).is_none());
            }
            EffectExprKind::Operation(EffectOperation::ProviderScope(scope))
                if scope.descriptor.native_effect().effect() == native.effects[1] =>
            {
                assert!(child_scope.replace(node).is_none());
            }
            _ => {}
        }
        pending_nodes
            .extend((0..expression.kind.child_count()).filter_map(|i| expression.kind.child_at(i)));
    }
    let parent_operand = parent_operand.expect("one authenticated parent native-read operand");
    let child_scope = child_scope.expect("one checked child provider scope");
    let publications = Rc::new(RefCell::new([0; 2]));
    let pending = Rc::new(RefCell::new(PendingTrace::default()));
    let (mut measured_host, measured_native) = runtime_with_binding(&registrations, |inner| {
        Box::new(PublicationBinding {
            inner,
            publications: Rc::clone(&publications),
            pending: Rc::clone(&pending),
            invalid_result: false,
        })
    });
    let observed = Arc::new(std::sync::Mutex::new(Vec::new()));
    let mut measured = Machine::new_effect(&program);
    measured.foreign_runtime = Some(&mut measured_host);
    measured.work_trace = Some(Arc::clone(&observed));
    let completed = measured.run().unwrap();
    assert_eq!(completed.registration_acquisitions, 0);
    assert_eq!(
        completed.value.to_string(),
        "Completed(Completed(42, Closed), Closed)"
    );
    assert_eq!(*publications.borrow(), [1, 1]);
    assert_eq!(measured_native.borrow().live, [false; 2]);
    let trace = observed.lock().unwrap();
    assert_eq!(
        trace
            .iter()
            .filter(|(node, _)| *node == parent_operand)
            .count(),
        1
    );
    assert_eq!(
        trace
            .iter()
            .filter(|(node, _)| *node == child_scope)
            .count(),
        1
    );
    let operand_index = trace
        .iter()
        .position(|(node, _)| *node == parent_operand)
        .unwrap();
    assert_eq!(trace[operand_index + 1].0, child_scope);
    // No registration acquisition or intervening Evaluate node charges this
    // ordinary return/resume/bind path. The final decode clone of Int20 is the
    // last charge before the unique child scope's measured entry.
    let clone_charge =
        usize::try_from(crate::integer::Integer::from_i64(20).magnitude_byte_length())
            .unwrap()
            .max(1);
    assert_eq!(clone_charge, 1);
    let cut = trace[operand_index + 1]
        .1
        .checked_sub(clone_charge)
        .unwrap();
    drop(trace);
    for prefill in [0, 7] {
        let publications = Rc::new(RefCell::new([0; 2]));
        let pending = Rc::new(RefCell::new(PendingTrace::default()));
        let (mut host, native) = runtime_with_binding(&registrations, |inner| {
            Box::new(PublicationBinding {
                inner,
                publications: Rc::clone(&publications),
                pending: Rc::clone(&pending),
                invalid_result: false,
            })
        });
        let rejected_trace = Arc::new(std::sync::Mutex::new(Vec::new()));
        let mut rejected = Machine::new_effect(&program);
        rejected.foreign_runtime = Some(&mut host);
        rejected.work_trace = Some(Arc::clone(&rejected_trace));
        rejected.instantiation_work = TypeWorkBudget::with_limit(cut + prefill);
        rejected.instantiation_work.charge(prefill).unwrap();
        let RuntimeFailure::Report(report) = rejected.run().unwrap_err() else {
            panic!("the exact final decode clone must refuse work admission")
        };
        let details = report.primary.resource().unwrap();
        assert_eq!(details.cause, ResourceFailureCause::WorkBudgetExhausted);
        assert_eq!(details.phase, RuntimePhase::Access);
        assert_eq!(details.resource, RuntimeResource::WorkUnits);
        assert_eq!((details.requested, details.available), (Some(1), Some(0)));
        assert!(report.teardown.is_none());
        assert_eq!(report.cleanup, CleanupStatus::Complete);
        assert!(
            !rejected_trace
                .lock()
                .unwrap()
                .iter()
                .any(|(node, _)| *node == child_scope)
        );
        assert_eq!(
            native.borrow().events,
            vec![Event::Acquired(0), Event::Borrowed(0)],
            "the parent native read ran, but the child acquisition never began"
        );
        assert_eq!(*publications.borrow(), [0, 0]);
        assert_eq!(pending.borrow().prepared, 1);
        assert_eq!(pending.borrow().committed, 0);
        assert_eq!(pending.borrow().abandoned, 1);
        assert_eq!(host.retained_owner_count(), 1);
        drop(host);
        assert_eq!(native.borrow().live, [false; 2]);
    }
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
