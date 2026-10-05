use ash::{
    driver::{PipelineFailure, RunConfiguration, run_path_with_foreign_runtime},
    eval::{ResourceFailureCause, RuntimeFailure, RuntimePhase, RuntimeResource},
    foreign::{
        ForeignConstructorDeclaration, ForeignEffectDeclaration, ForeignManifest,
        ForeignManifestSchema, ForeignModuleFact, ForeignOperationDeclaration,
        ForeignRegistrations, ForeignResultRelation, ForeignTypeDeclaration,
        runtime::{
            ExecutableForeignModule, ForeignAcquisition, ForeignCompletion, ForeignData,
            ForeignDataNode, ForeignExecutionError, ForeignExecutionReason, ForeignFinishContext,
            ForeignOperationKey, ForeignRuntime, ForeignRuntimeBinding, NativeResourceOwner,
        },
    },
    module::{ForeignOperationRole, ForeignRegistrationId, ModuleRoots},
};
use std::{
    any::Any,
    cell::RefCell,
    fs,
    path::PathBuf,
    rc::Rc,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

static IDS: AtomicU64 = AtomicU64::new(0);
struct Tree(PathBuf);
impl Tree {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "ash-codec-failure-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        fs::write(path.join("entry.ash"), SOURCE).unwrap();
        Self(path)
    }
}
impl Drop for Tree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

const SOURCE: &str = r#"
import @foreign.codec_probe as Native
pub type Completion<E> = Closed
| ConsumedError(E)
| RetainedError(E)
pub type Scope<I, E, T> = NotAcquired(I)
| Completed(T, Completion<E>)
pub effect ReadOps<R> {
read : Handle<R> -> Int
}
pub interface Reader<R> {
read : Handle<R> -> Int ! {ReadOps<R>}
}
pub resource Handle<R> {
input Int
state Native.Token<R>
result Scope<Native.Fault, Native.Fault, T> for <T>
provider Reader<R>
effect ReadOps<R>
interpret Native.Requests<R>
acquire value => perform Native.Requests<R>.begin value
finish state => perform Native.Requests<R>.end state
handlers state {
read item => resume (perform Native.Requests<R>.read state)
}
}
main : Unit -> Scope<Native.Fault, Native.Fault, Int>
main () = resource Handle<R> item = 42 {
read item
}
"#;

fn manifest() -> ForeignManifest {
    let ty = |name: &str, parameters: &[&str], opaque_state, cases: &[(&str, Option<&str>)]| {
        ForeignTypeDeclaration {
            name: name.into(),
            parameters: parameters.iter().map(|p| (*p).into()).collect(),
            opaque_state,
            constructors: cases
                .iter()
                .map(|(name, payload)| ForeignConstructorDeclaration {
                    name: (*name).into(),
                    payload: payload.map(str::to_owned),
                })
                .collect(),
        }
    };
    ForeignManifest::new(
        "@foreign.codec_probe",
        ForeignRegistrationId::new(901),
        ForeignManifestSchema {
            types: vec![
                ty("Token", &["R"], true, &[]),
                ty("Fault", &[], false, &[("Oops", Some("Int"))]),
                ty(
                    "Start",
                    &["State", "E"],
                    false,
                    &[("Started", Some("State")), ("Denied", Some("E"))],
                ),
                ty(
                    "Stop",
                    &["State", "E"],
                    false,
                    &[
                        ("Stopped", None),
                        ("StopFailed", Some("E")),
                        ("Kept", Some("State, E")),
                    ],
                ),
            ],
            effects: vec![ForeignEffectDeclaration {
                name: "Requests".into(),
                parameters: vec!["R".into()],
                operations: vec![
                    ForeignOperationDeclaration {
                        name: "begin".into(),
                        signature: "Int -> Start<Token<R>, Fault>".into(),
                        role: ForeignOperationRole::Acquire,
                        owned_identity_position: 0,
                        state_operands: vec![],
                        retained_arguments: vec![],
                        result: ForeignResultRelation::Acquire {
                            state: "Token".into(),
                            error: "Fault".into(),
                            report: "Start".into(),
                            retained_parameters: vec![],
                        },
                    },
                    ForeignOperationDeclaration {
                        name: "read".into(),
                        signature: "Token<R> -> Int".into(),
                        role: ForeignOperationRole::Borrow,
                        owned_identity_position: 0,
                        state_operands: vec![vec![]],
                        retained_arguments: vec![],
                        result: ForeignResultRelation::Independent,
                    },
                    ForeignOperationDeclaration {
                        name: "end".into(),
                        signature: "Token<R> -> Stop<Token<R>, Fault>".into(),
                        role: ForeignOperationRole::Finish,
                        owned_identity_position: 0,
                        state_operands: vec![vec![]],
                        retained_arguments: vec![],
                        result: ForeignResultRelation::Finish {
                            state: "Token".into(),
                            error: "Fault".into(),
                            report: "Stop".into(),
                        },
                    },
                ],
            }],
            state_access: None,
        },
    )
    .unwrap()
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Boundary {
    Preflight,
    Acquire,
    Borrow,
    BeforeFinish,
    ConsumedFinish,
    RetainedFinish,
}
#[derive(Debug, Default)]
struct Counts {
    preflight: usize,
    acquired: usize,
    invoked: usize,
    finished: usize,
    consumed: usize,
    dropped: usize,
    host_released: usize,
}
#[derive(Debug)]
struct Owner {
    counts: Rc<RefCell<Counts>>,
    live: bool,
}
impl NativeResourceOwner for Owner {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}
impl Drop for Owner {
    fn drop(&mut self) {
        let mut counts = self.counts.borrow_mut();
        counts.dropped += 1;
        counts.host_released += usize::from(self.live);
    }
}
#[derive(Debug)]
struct Probe {
    boundary: Boundary,
    error: ForeignExecutionError,
    finish_integer_bytes: Option<usize>,
    counts: Rc<RefCell<Counts>>,
}
impl ExecutableForeignModule for Probe {
    fn preflight(&self, _: &ForeignModuleFact) -> Result<(), ForeignExecutionError> {
        self.counts.borrow_mut().preflight += 1;
        if self.boundary == Boundary::Preflight {
            Err(self.error)
        } else {
            Ok(())
        }
    }
    fn acquire(
        &self,
        key: ForeignOperationKey,
        _: &ForeignModuleFact,
        input: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignAcquisition, ForeignExecutionError> {
        assert_eq!(
            key,
            ForeignOperationKey {
                effect: 0,
                operation: 0
            }
        );
        assert!(matches!(
            input.node(input.root()),
            Some(ForeignDataNode::Integer(_))
        ));
        assert!(states.is_empty());
        self.counts.borrow_mut().acquired += 1;
        if self.boundary == Boundary::Acquire {
            return Err(self.error);
        }
        Ok(ForeignAcquisition::Acquired(Box::new(Owner {
            counts: Rc::clone(&self.counts),
            live: true,
        })))
    }
    fn invoke(
        &self,
        key: ForeignOperationKey,
        _: &ForeignModuleFact,
        _: &ForeignData,
        states: &[&dyn NativeResourceOwner],
    ) -> Result<ForeignData, ForeignExecutionError> {
        assert_eq!(
            key,
            ForeignOperationKey {
                effect: 0,
                operation: 1
            }
        );
        assert_eq!(states.len(), 1);
        let owner = states[0].as_any().downcast_ref::<Owner>().unwrap();
        assert!(Rc::ptr_eq(&owner.counts, &self.counts));
        assert!(owner.live);
        self.counts.borrow_mut().invoked += 1;
        if self.boundary == Boundary::Borrow {
            return Err(self.error);
        }
        ForeignData::new(
            vec![ForeignDataNode::Integer(ash::integer::Integer::from_i64(7))],
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
        assert_eq!(
            key,
            ForeignOperationKey {
                effect: 0,
                operation: 2
            }
        );
        assert!(!context.retained_dependents);
        self.counts.borrow_mut().finished += 1;
        let owner = owner.as_any_mut().downcast_mut::<Owner>().unwrap();
        assert!(Rc::ptr_eq(&owner.counts, &self.counts));
        assert!(owner.live, "a consumed owner must never be finished again");
        let data = match self.finish_integer_bytes {
            Some(bytes) => {
                let mut value = ash::integer::Integer::from_i64(1);
                let mut base = ash::integer::Integer::from_i64(256);
                let mut exponent = bytes.checked_sub(1).expect("nonempty integer magnitude");
                while exponent != 0 {
                    if exponent & 1 != 0 {
                        value = &value * &base;
                    }
                    exponent >>= 1;
                    if exponent != 0 {
                        base = &base * &base;
                    }
                }
                assert_eq!(
                    usize::try_from(value.magnitude_byte_length()).unwrap(),
                    bytes
                );
                // Preserve the actual bounded factory result inside the
                // declared consumed or retained completion disposition.
                ForeignData::new(
                    vec![
                        ForeignDataNode::Integer(value),
                        ForeignDataNode::Constructor(module.constructors["Oops"], Some(0)),
                    ],
                    1,
                )
            }
            None => Err(self.error),
        };
        match self.boundary {
            Boundary::BeforeFinish => Err(self.error),
            Boundary::ConsumedFinish => {
                owner.live = false;
                self.counts.borrow_mut().consumed += 1;
                Ok(ForeignCompletion::ConsumedError(data))
            }
            Boundary::RetainedFinish => Ok(ForeignCompletion::RetainedError(data)),
            _ => panic!("failure should stop before finish"),
        }
    }
}

fn assert_boundary(boundary: Boundary) {
    let tree = Tree::new();
    for (error, cause, resource) in [
        (
            ForeignExecutionError::WORK_EXHAUSTED,
            Some(ResourceFailureCause::WorkBudgetExhausted),
            RuntimeResource::WorkUnits,
        ),
        (
            ForeignExecutionError::STORAGE_REFUSED,
            Some(ResourceFailureCause::StorageReservationFailed),
            RuntimeResource::ForeignCodecStorage,
        ),
        (
            ForeignExecutionError::RESOURCE_REFUSED,
            Some(ResourceFailureCause::ResourceAdmissionRefused),
            RuntimeResource::ForeignAdmission,
        ),
        (
            ForeignExecutionError("ordinary binding work/storage refusal"),
            None,
            RuntimeResource::ForeignCodecStorage,
        ),
    ] {
        let registrations = ForeignRegistrations::new([manifest()]).unwrap();
        let counts = Rc::new(RefCell::new(Counts::default()));
        let binding = ForeignRuntimeBinding::new(
            Arc::clone(registrations.get("@foreign.codec_probe").unwrap()),
            Box::new(Probe {
                boundary,
                error,
                finish_integer_bytes: None,
                counts: Rc::clone(&counts),
            }),
        );
        let mut runtime = ForeignRuntime::new(vec![binding]).unwrap();
        let failure = run_path_with_foreign_runtime(
            RunConfiguration {
                entry: tree.0.join("entry.ash"),
                roots: ModuleRoots::empty().with_foreign_registrations(registrations),
            },
            &mut runtime,
        )
        .expect_err("codec refusal must publish no source result");
        let Some(PipelineFailure::Runtime(failure)) = failure.pipeline_failure() else {
            panic!("{boundary:?}: {failure:?}");
        };
        if let Some(cause) = cause {
            let RuntimeFailure::Report(report) = failure else {
                panic!("{boundary:?}: {failure:?}");
            };
            let details = report.primary.resource().unwrap();
            assert_eq!(details.cause, cause, "{boundary:?}");
            assert_eq!(report.primary.reason_code(), cause.reason_code());
            assert_eq!(details.resource, resource);
            assert_eq!(details.requested, None);
            assert_eq!(details.available, None);
            assert_eq!(
                details.phase,
                match boundary {
                    Boundary::Preflight | Boundary::Acquire => RuntimePhase::Acquisition,
                    Boundary::Borrow => RuntimePhase::Access,
                    _ => RuntimePhase::Cleanup,
                }
            );
            assert!(report.teardown.is_none());
        } else {
            assert_eq!(
                failure.reason_code(),
                RuntimeFailure::ForeignBinding.reason_code()
            );
        }
        let retained = !matches!(
            boundary,
            Boundary::Preflight | Boundary::Acquire | Boundary::ConsumedFinish
        );
        assert_eq!(
            runtime.retained_owner_count(),
            usize::from(retained),
            "{boundary:?}"
        );
        {
            let observed = counts.borrow();
            assert_eq!(observed.preflight, 1);
            assert_eq!(
                observed.acquired,
                usize::from(boundary != Boundary::Preflight)
            );
            assert_eq!(
                observed.invoked,
                usize::from(!matches!(boundary, Boundary::Preflight | Boundary::Acquire))
            );
            assert_eq!(
                observed.finished,
                usize::from(matches!(
                    boundary,
                    Boundary::BeforeFinish | Boundary::ConsumedFinish | Boundary::RetainedFinish
                ))
            );
            assert_eq!(
                observed.consumed,
                usize::from(boundary == Boundary::ConsumedFinish)
            );
            assert_eq!(
                observed.dropped,
                usize::from(boundary == Boundary::ConsumedFinish)
            );
            assert_eq!(observed.host_released, 0);
        }
        drop(runtime);
        let observed = counts.borrow();
        let acquired = !matches!(boundary, Boundary::Preflight | Boundary::Acquire);
        assert_eq!(observed.dropped, usize::from(acquired));
        assert_eq!(observed.host_released, usize::from(retained));
        assert_eq!(
            observed.finished,
            usize::from(matches!(
                boundary,
                Boundary::BeforeFinish | Boundary::ConsumedFinish | Boundary::RetainedFinish
            )),
            "host disposal must not retry source finish"
        );
    }
}

#[test]
fn preflight_markers_preserve_detected_failure_causes() {
    assert_boundary(Boundary::Preflight);
}
#[test]
fn acquisition_markers_publish_no_owner_or_source_result() {
    assert_boundary(Boundary::Acquire);
}
#[test]
fn borrowed_call_markers_quarantine_the_original_owner() {
    assert_boundary(Boundary::Borrow);
}
#[test]
fn finish_refusal_before_transition_retains_the_original_owner() {
    assert_boundary(Boundary::BeforeFinish);
}
#[test]
fn consumed_finish_conversion_refusal_does_not_resurrect_or_retry_owner() {
    assert_boundary(Boundary::ConsumedFinish);
}
#[test]
fn retained_finish_conversion_refusal_quarantines_before_reporting() {
    assert_boundary(Boundary::RetainedFinish);
}

#[test]
fn tuple_error_api_classifies_only_exact_reserved_markers() {
    let original = ForeignExecutionError("adapter storage refused after work exhausted");
    let ForeignExecutionError(message) = original;
    assert_eq!(message, "adapter storage refused after work exhausted");
    assert_eq!(original.to_string(), message);
    assert_eq!(original.reason(), ForeignExecutionReason::Binding);
    assert_eq!(
        ForeignExecutionError("@ash.foreign/work-exhausted (adapter detail)").reason(),
        ForeignExecutionReason::Binding,
    );
    assert_eq!(
        ForeignExecutionError::WORK_EXHAUSTED.reason(),
        ForeignExecutionReason::WorkExhausted
    );
    assert_eq!(
        ForeignExecutionError::STORAGE_REFUSED.reason(),
        ForeignExecutionReason::StorageRefused
    );
    assert_eq!(
        ForeignExecutionError::RESOURCE_REFUSED.reason(),
        ForeignExecutionReason::ResourceRefused
    );
}

#[test]
fn missing_executable_binding_remains_a_contract_failure() {
    let tree = Tree::new();
    let registrations = ForeignRegistrations::new([manifest()]).unwrap();
    let mut runtime = ForeignRuntime::default();
    let failure = run_path_with_foreign_runtime(
        RunConfiguration {
            entry: tree.0.join("entry.ash"),
            roots: ModuleRoots::empty().with_foreign_registrations(registrations),
        },
        &mut runtime,
    )
    .expect_err("missing bindings must not publish a source acquisition refusal");
    let Some(PipelineFailure::Runtime(failure)) = failure.pipeline_failure() else {
        panic!("{failure:?}");
    };
    assert_eq!(
        failure.reason_code(),
        RuntimeFailure::ForeignBinding.reason_code()
    );
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn malformed_graphs_remain_binding_errors_and_excess_payload_work_is_explicit() {
    for data in [
        ForeignData::new(vec![], 0),
        ForeignData::new(vec![ForeignDataNode::Unit], 1),
        ForeignData::new(vec![ForeignDataNode::Tuple(vec![0].into_boxed_slice())], 0),
    ] {
        assert_eq!(data.unwrap_err().reason(), ForeignExecutionReason::Binding);
    }
    let oversized = ForeignData::new(
        vec![ForeignDataNode::Bytes(Arc::from(
            vec![0; ash::types::TYPE_WORK_LIMIT],
        ))],
        0,
    )
    .unwrap_err();
    assert_eq!(oversized, ForeignExecutionError::WORK_EXHAUSTED);
}

#[test]
fn finish_payload_admission_refusal_preserves_disposition_and_fresh_retry() {
    // ForeignData admission counts two nodes and two integer copies. The
    // ordinary evaluator has no fixed gas limit; exercise this factory bound.
    let large = (ash::types::TYPE_WORK_LIMIT - 2) / 2 + 1;
    assert!(2 + 2 * large > ash::types::TYPE_WORK_LIMIT);
    for boundary in [Boundary::ConsumedFinish, Boundary::RetainedFinish] {
        for bytes in [large, 1] {
            let tree = Tree::new();
            let registrations = ForeignRegistrations::new([manifest()]).unwrap();
            let counts = Rc::new(RefCell::new(Counts::default()));
            let binding = ForeignRuntimeBinding::new(
                Arc::clone(registrations.get("@foreign.codec_probe").unwrap()),
                Box::new(Probe {
                    boundary,
                    error: ForeignExecutionError(
                        "payload path must return the actual factory result",
                    ),
                    finish_integer_bytes: Some(bytes),
                    counts: Rc::clone(&counts),
                }),
            );
            let mut runtime = ForeignRuntime::new(vec![binding]).unwrap();
            let result = run_path_with_foreign_runtime(
                RunConfiguration {
                    entry: tree.0.join("entry.ash"),
                    roots: ModuleRoots::empty().with_foreign_registrations(registrations),
                },
                &mut runtime,
            );
            if bytes == large {
                let failure =
                    result.expect_err("native payload admission refused before source publication");
                let Some(PipelineFailure::Runtime(RuntimeFailure::Report(report))) =
                    failure.pipeline_failure()
                else {
                    panic!("{boundary:?}: {failure:?}");
                };
                let details = report
                    .primary
                    .resource()
                    .expect("real factory work refusal keeps its detected cause");
                assert_eq!(details.cause, ResourceFailureCause::WorkBudgetExhausted);
                assert_eq!(details.phase, RuntimePhase::Cleanup);
                assert_eq!(details.resource, RuntimeResource::WorkUnits);
                // The public tuple factory error preserves its work cause,
                // but carries no requested/available quantities.
                assert_eq!(details.requested, None);
                assert_eq!(details.available, None);
                assert!(report.teardown.is_none());
            } else {
                let observation =
                    result.expect("fresh smaller payload executes without source retry");
                let display = observation.value_display();
                assert!(display.contains("Completed"), "{display}");
                assert!(display.contains("Oops(1)"), "{display}");
                assert!(
                    display.contains(if boundary == Boundary::ConsumedFinish {
                        "ConsumedError"
                    } else {
                        "RetainedError"
                    }),
                    "{display}"
                );
            }
            let retained = boundary == Boundary::RetainedFinish;
            assert_eq!(runtime.retained_owner_count(), usize::from(retained));
            {
                let observed = counts.borrow();
                assert_eq!(
                    (
                        observed.preflight,
                        observed.acquired,
                        observed.invoked,
                        observed.finished
                    ),
                    (1, 1, 1, 1)
                );
                assert_eq!(observed.consumed, usize::from(!retained));
                assert_eq!(observed.dropped, usize::from(!retained));
                assert_eq!(observed.host_released, 0);
            }
            drop(runtime);
            let observed = counts.borrow();
            assert_eq!(observed.dropped, 1);
            assert_eq!(observed.host_released, usize::from(retained));
            assert_eq!(
                observed.finished, 1,
                "host release must not retry source finish"
            );
        }
    }
}
