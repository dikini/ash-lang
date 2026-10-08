//! DN-0036 test-only retained-owner dependency witness.
//! The binding owns real unique Rust storage and injects explicit retained
//! dispositions; it makes no claim about SQLite or a production native family.
use ash::{
    driver::{RunConfiguration, run_path_with_foreign_runtime},
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
    module::{ForeignOperationRole, ForeignRegistrationId, ModuleRoots},
};
use std::{any::Any, cell::RefCell, collections::HashMap, path::PathBuf, rc::Rc, sync::Arc};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Event {
    Acquired { id: u64, parent: Option<u64> },
    Borrowed(u64),
    InjectedRetained { id: u64, retained_dependents: bool },
    InjectedConsumed(u64),
    Destroyed(u64),
}
#[derive(Debug, Default)]
struct Trace {
    next: u64,
    live: HashMap<u64, Option<u64>>,
    events: Vec<Event>,
}
impl Trace {
    /// Keep one allocation-free destruction observation for every live owner,
    /// in addition to the event about to be recorded.
    fn reserve_event_and_releases(
        &mut self,
        new_owners: usize,
    ) -> Result<(), ForeignExecutionError> {
        let additional = self
            .live
            .len()
            .checked_add(new_owners)
            .and_then(|owners| owners.checked_add(1))
            .ok_or(ForeignExecutionError("test observation capacity exhausted"))?;
        self.events
            .try_reserve(additional)
            .map_err(|_| ForeignExecutionError("test native observation refused"))
    }
}
type Observations = Rc<RefCell<Trace>>;

#[derive(Debug)]
struct Owner {
    id: u64,
    family: usize,
    storage: Option<Storage>,
    trace: Observations,
}
impl NativeResourceOwner for Owner {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}
/// The native payload allocation has a lifetime independent of its guard.
#[derive(Debug)]
struct Storage {
    values: Box<[i64]>,
    id: u64,
    trace: Observations,
}
impl Drop for Storage {
    fn drop(&mut self) {
        let mut trace = self.trace.borrow_mut();
        assert!(
            !trace.live.values().any(|parent| *parent == Some(self.id)),
            "native parent storage destroyed before retained child"
        );
        assert!(
            trace.events.capacity() - trace.events.len() >= trace.live.len(),
            "destruction observations must have acquisition-reserved capacity"
        );
        // Observe actual payload destruction, including a consumed disposition
        // whose empty guard has not yet returned to the evaluator.
        drop(std::mem::take(&mut self.values));
        assert!(
            trace.live.remove(&self.id).is_some(),
            "same native owner destroyed twice"
        );
        trace.events.push(Event::Destroyed(self.id));
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
        category: if opaque_state {
            ash::foreign::ForeignTypeCategory::State
        } else {
            ash::foreign::ForeignTypeCategory::Data
        },
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
            foundation: None,
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

#[derive(Clone, Copy, Debug, Default)]
enum FinishConversionFault {
    #[default]
    None,
    ConsumedChild,
    RetainedChild,
}

#[derive(Debug)]
struct Binding {
    manifest: Arc<ForeignManifest>,
    trace: Observations,
    conversion_fault: FinishConversionFault,
}
impl Binding {
    fn authenticate(&self, module: &ForeignModuleFact) -> Result<(), ForeignExecutionError> {
        if !Arc::ptr_eq(module.manifest(), &self.manifest) {
            return Err(ForeignExecutionError(
                "test binding requires the original registration allocation",
            ));
        }
        Ok(())
    }
    fn owner<'a>(
        &self,
        states: &'a [&dyn NativeResourceOwner],
        family: usize,
    ) -> Result<&'a Owner, ForeignExecutionError> {
        let [state] = states else {
            return Err(ForeignExecutionError("exactly one state operand required"));
        };
        let owner = state
            .as_any()
            .downcast_ref::<Owner>()
            .filter(|owner| owner.family == family)
            .ok_or(ForeignExecutionError("wrong original native state family"))?;
        if !Rc::ptr_eq(&owner.trace, &self.trace)
            || !self.trace.borrow().live.contains_key(&owner.id)
        {
            return Err(ForeignExecutionError(
                "state view is not this binding's live owner",
            ));
        }
        Ok(owner)
    }
}
impl ExecutableForeignModule for Binding {
    fn preflight(&self, module: &ForeignModuleFact) -> Result<(), ForeignExecutionError> {
        self.authenticate(module)?;
        if self.manifest.as_ref() != &manifest()
            || module.effects.len() != 2
            || module.operations.len() != 6
        {
            return Err(ForeignExecutionError(
                "test binding contract differs from its original manifest",
            ));
        }
        Ok(())
    }
    fn acquire(
        &self,
        key: ForeignOperationKey,
        module: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignAcquisition, ForeignExecutionError> {
        self.authenticate(module)?;
        let (parent, value) = match (key.effect, key.operation, input.node(input.root())) {
            (0, 0, Some(ForeignDataNode::Integer(value))) if states.is_empty() => (
                None,
                value.to_i64().ok_or(ForeignExecutionError(
                    "initializer exceeds test native integer range",
                ))?,
            ),
            (1, 0, Some(ForeignDataNode::Tuple(fields))) if fields.len() == 2 => {
                if !matches!(input.node(fields[0]), Some(ForeignDataNode::State(0))) {
                    return Err(ForeignExecutionError(
                        "child acquisition requires original borrowed parent slot",
                    ));
                }
                let Some(ForeignDataNode::Integer(value)) = input.node(fields[1]) else {
                    return Err(ForeignExecutionError(
                        "child storage initializer is not Int",
                    ));
                };
                (
                    Some(self.owner(states, 0)?.id),
                    value.to_i64().ok_or(ForeignExecutionError(
                        "initializer exceeds test native integer range",
                    ))?,
                )
            }
            _ => {
                return Err(ForeignExecutionError(
                    "unregistered acquisition coordinate or conversion",
                ));
            }
        };
        let mut storage = Vec::new();
        storage
            .try_reserve_exact(1)
            .map_err(|_| ForeignExecutionError("test native allocation refused"))?;
        storage.push(value);
        let mut trace = self.trace.borrow_mut();
        trace
            .live
            .try_reserve(1)
            .map_err(|_| ForeignExecutionError("test native owner table refused"))?;
        trace.reserve_event_and_releases(1)?;
        let id = trace.next;
        trace.next = id
            .checked_add(1)
            .ok_or(ForeignExecutionError("test native activation exhausted"))?;
        assert!(trace.live.insert(id, parent).is_none());
        trace.events.push(Event::Acquired { id, parent });
        drop(trace);
        Ok(ForeignAcquisition::Acquired(Box::new(Owner {
            id,
            family: key.effect,
            storage: Some(Storage {
                values: storage.into_boxed_slice(),
                id,
                trace: Rc::clone(&self.trace),
            }),
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
        if key.effect > 1
            || key.operation != 1
            || !matches!(input.node(input.root()), Some(ForeignDataNode::State(0)))
        {
            return Err(ForeignExecutionError(
                "unregistered borrowed coordinate or state conversion",
            ));
        }
        let owner = self.owner(states, key.effect)?;
        let value = owner
            .storage
            .as_ref()
            .ok_or(ForeignExecutionError(
                "borrow after consumed native storage",
            ))?
            .values[0];
        let mut trace = self.trace.borrow_mut();
        trace.reserve_event_and_releases(0)?;
        trace.events.push(Event::Borrowed(owner.id));
        ForeignData::new(
            vec![ForeignDataNode::Integer(ash::integer::Integer::from_i64(
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
        let owner = owner
            .as_any_mut()
            .downcast_mut::<Owner>()
            .filter(|owner| key.operation == 2 && key.effect == owner.family)
            .ok_or(ForeignExecutionError(
                "unregistered finish coordinate or original owner",
            ))?;
        let mut trace = self.trace.borrow_mut();
        if !Rc::ptr_eq(&owner.trace, &self.trace) || !trace.live.contains_key(&owner.id) {
            return Err(ForeignExecutionError(
                "finish did not retain the same native owner",
            ));
        }
        let has_child = trace.live.values().any(|parent| *parent == Some(owner.id));
        if has_child != context.retained_dependents {
            return Err(ForeignExecutionError(
                "retained dependency context does not match actual native guards",
            ));
        }
        trace.reserve_event_and_releases(0)?;
        if key.effect == 1 && matches!(self.conversion_fault, FinishConversionFault::ConsumedChild)
        {
            trace.events.push(Event::InjectedConsumed(owner.id));
            drop(trace);
            drop(owner.storage.take().ok_or(ForeignExecutionError(
                "native child storage already consumed",
            ))?);
            // The outer result preserves the completed transition. Only error
            // data conversion fails; source completion must never retry it.
            return Ok(ForeignCompletion::ConsumedError(Err(
                ForeignExecutionError("injected completion error conversion failure"),
            )));
        }
        trace.events.push(Event::InjectedRetained {
            id: owner.id,
            retained_dependents: context.retained_dependents,
        });
        drop(trace);
        if key.effect == 1 && matches!(self.conversion_fault, FinishConversionFault::RetainedChild)
        {
            return Ok(ForeignCompletion::RetainedError(Err(
                ForeignExecutionError("injected completion error conversion failure"),
            )));
        }
        let constructor =
            *module
                .constructors
                .get("FinishRefused")
                .ok_or(ForeignExecutionError(
                    "original completion error constructor missing",
                ))?;
        Ok(ForeignCompletion::RetainedError(ForeignData::new(
            vec![ForeignDataNode::Constructor(constructor, None)],
            0,
        )))
    }
}

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/provider-experiments/retention-source")
        .join(name)
}
fn execute(
    name: &str,
) -> (
    Result<String, ash::driver::FileFailure>,
    ForeignRuntime,
    Observations,
) {
    execute_with_conversion_fault(name, FinishConversionFault::None)
}
fn execute_with_conversion_fault(
    name: &str,
    conversion_fault: FinishConversionFault,
) -> (
    Result<String, ash::driver::FileFailure>,
    ForeignRuntime,
    Observations,
) {
    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
        manifest(),
    ])
    .unwrap();
    let original = Arc::clone(registrations.get("@foreign.retention").unwrap());
    let trace = Rc::new(RefCell::new(Trace::default()));
    let binding = ForeignRuntimeBinding::new(
        Arc::clone(&original),
        Box::new(Binding {
            manifest: original,
            trace: Rc::clone(&trace),
            conversion_fault,
        }),
    );
    let mut runtime = ForeignRuntime::new(vec![binding]).unwrap();
    let result = run_path_with_foreign_runtime(
        RunConfiguration {
            entry: fixture(name),
            roots: ModuleRoots::empty().with_foreign_registrations(registrations),
        },
        &mut runtime,
    )
    .map(|observation| observation.value_display());
    (result, runtime, trace)
}

#[test]
fn retained_child_and_parent_keep_exact_native_owners_until_dependency_ordered_host_teardown() {
    let (result, runtime, trace) = execute("entry.ash");
    assert_eq!(
        result.unwrap(),
        "Completed(Completed(42, RetainedError(FinishRefused)), RetainedError(FinishRefused))"
    );
    assert_eq!(runtime.retained_owner_count(), 2);
    assert_eq!(
        trace.borrow().events,
        vec![
            Event::Acquired {
                id: 0,
                parent: None
            },
            Event::Borrowed(0),
            Event::Acquired {
                id: 1,
                parent: Some(0)
            },
            Event::Borrowed(1),
            Event::InjectedRetained {
                id: 1,
                retained_dependents: false
            },
            Event::InjectedRetained {
                id: 0,
                retained_dependents: true
            },
        ]
    );
    assert_eq!(trace.borrow().live.len(), 2);
    drop(runtime);
    assert_eq!(
        &trace.borrow().events[6..],
        &[Event::Destroyed(1), Event::Destroyed(0)]
    );
    assert!(trace.borrow().live.is_empty());
}

#[test]
fn retained_dependency_revokes_parent_source_access_without_retrying_native_finish() {
    let (result, runtime, trace) = execute("revoked.ash");
    let failure =
        result.expect_err("the dependency quarantine cannot grant another source state view");
    assert!(
        !failure.is_source_rejection(),
        "the typed program encounters an injected runtime disposition: {failure:?}"
    );
    assert_eq!(runtime.retained_owner_count(), 2);
    let events = trace.borrow().events.clone();
    assert_eq!(
        events
            .iter()
            .filter(|event| matches!(event, Event::Borrowed(0)))
            .count(),
        1
    );
    assert_eq!(
        events
            .iter()
            .filter(|event| matches!(event, Event::InjectedRetained { id: 1, .. }))
            .count(),
        1
    );
    assert!(
        !events
            .iter()
            .any(|event| matches!(event, Event::Destroyed(_)))
    );
    drop(runtime);
    let events = trace.borrow().events.clone();
    assert_eq!(
        &events[events.len() - 2..],
        &[Event::Destroyed(1), Event::Destroyed(0)]
    );
    assert!(trace.borrow().live.is_empty());
}

#[test]
fn finish_conversion_failure_preserves_disposition_and_dependency_order_without_retry() {
    for (fault, consumed) in [
        (FinishConversionFault::ConsumedChild, true),
        (FinishConversionFault::RetainedChild, false),
    ] {
        let (result, runtime, trace) = execute_with_conversion_fault("entry.ash", fault);
        let failure = result.expect_err("completion error conversion must fail after disposition");
        assert!(!failure.is_source_rejection(), "{failure:?}");
        assert!(
            matches!(
                failure.pipeline_failure(),
                Some(ash::driver::PipelineFailure::Runtime(
                    ash::eval::RuntimeFailure::ForeignBinding
                ))
            ),
            "{failure:?}"
        );
        let mut expected = vec![
            Event::Acquired {
                id: 0,
                parent: None,
            },
            Event::Borrowed(0),
            Event::Acquired {
                id: 1,
                parent: Some(0),
            },
            Event::Borrowed(1),
        ];
        if consumed {
            expected.extend([Event::InjectedConsumed(1), Event::Destroyed(1)]);
            assert_eq!(runtime.retained_owner_count(), 1);
            assert_eq!(trace.borrow().live, HashMap::from([(0, None)]));
        } else {
            expected.push(Event::InjectedRetained {
                id: 1,
                retained_dependents: false,
            });
            assert_eq!(runtime.retained_owner_count(), 2);
            assert_eq!(
                trace.borrow().live,
                HashMap::from([(0, None), (1, Some(0))])
            );
        }
        // No parent source finish runs after the failed report conversion;
        // host-abort drainage preserves its live storage rather than retrying.
        assert_eq!(trace.borrow().events, expected);
        drop(runtime);
        if !consumed {
            expected.push(Event::Destroyed(1));
        }
        expected.push(Event::Destroyed(0));
        assert_eq!(trace.borrow().events, expected);
        assert!(trace.borrow().live.is_empty());
        // The same checked source succeeds with honest report conversion in a
        // fresh runtime; the injected failure has not changed its protocol.
        let (retry, runtime, trace) = execute("entry.ash");
        assert_eq!(
            retry.unwrap(),
            "Completed(Completed(42, RetainedError(FinishRefused)), RetainedError(FinishRefused))"
        );
        assert_eq!(runtime.retained_owner_count(), 2);
        drop(runtime);
        assert!(trace.borrow().live.is_empty());
    }
}
