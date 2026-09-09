use ash::{
    eval::{
        CleanupStatus, ResourceFailure, ResourceFailureCause, RuntimeFailure, RuntimePhase,
        RuntimeResource,
    },
    render,
};

fn failure() -> RuntimeFailure {
    RuntimeFailure::MissingBinding
        .with_resource_details(ResourceFailure::new(
            ResourceFailureCause::StorageReservationFailed,
            RuntimePhase::Capture,
            RuntimeResource::FrameStorage,
            Some(usize::MAX),
            None,
        ))
        .with_teardown_failure(
            ResourceFailure::new(
                ResourceFailureCause::AllocatorRefused,
                RuntimePhase::Teardown,
                RuntimeResource::TypeDisposal,
                Some(1),
                Some(0),
            ),
            CleanupStatus::Incomplete,
        )
}

#[test]
fn runtime_json_preserves_primary_teardown_and_cleanup_facts() {
    let mut output = [0; 4096];
    let mut remaining = output.as_mut_slice();
    render::write_runtime_json(&mut remaining, failure()).unwrap();
    let used = 4096 - remaining.len();
    let json: serde_json::Value = serde_json::from_slice(&output[..used]).unwrap();
    assert_eq!(json["schema_version"], 1);
    assert_eq!(json["reason"], "runtime.missing-binding");
    assert_eq!(json["responsibility"], "runtime");
    assert_eq!(json["labels"], serde_json::json!([]));
    let facts = json["facts"].as_array().unwrap();
    let fact = |name| facts.iter().find(|fact| fact["name"] == name).unwrap()["value"].clone();
    assert_eq!(fact("cause"), "runtime.storage-reservation-failed");
    assert_eq!(fact("phase"), "capture");
    assert_eq!(fact("resource"), "control frames");
    assert_eq!(fact("requested"), usize::MAX);
    assert!(!facts.iter().any(|fact| fact["name"] == "available"));
    assert_eq!(fact("underlying_cause"), "undetermined");
    assert_eq!(fact("teardown_cause"), "runtime.allocator-refused");
    assert_eq!(fact("teardown_phase"), "teardown");
    assert_eq!(fact("teardown_resource"), "type disposal tasks");
    assert_eq!(fact("teardown_requested"), 1);
    assert_eq!(fact("teardown_available"), 0);
    assert_eq!(fact("cleanup"), "incomplete");
    assert_eq!(
        output[..used].iter().filter(|&&byte| byte == b'\n').count(),
        1
    );
}

#[test]
fn runtime_json_covers_existing_base_reasons_without_inventing_resource_details() {
    for failure in [
        RuntimeFailure::MissingNode,
        RuntimeFailure::UnexpectedPrimitiveValue,
        RuntimeFailure::UnexpectedFunctionValue,
        RuntimeFailure::MissingBinding,
        RuntimeFailure::UnexpectedRecursiveBinding,
        RuntimeFailure::EnvironmentCapacity,
        RuntimeFailure::InvalidControlState,
        RuntimeFailure::HeapCapacity,
        RuntimeFailure::CapturedControlCapacity,
        RuntimeFailure::ResourceCapacity,
        RuntimeFailure::InvalidLocation,
        RuntimeFailure::UninitializedLocation,
        RuntimeFailure::AliasLoop,
        RuntimeFailure::ImpossibleMatch,
    ] {
        let mut output = [0; 4096];
        let mut remaining = output.as_mut_slice();
        render::write_runtime_json(&mut remaining, failure).unwrap();
        let used = 4096 - remaining.len();
        let json: serde_json::Value = serde_json::from_slice(&output[..used]).unwrap();
        assert_eq!(json["reason"], failure.reason_code());
        assert_eq!(
            json["facts"],
            serde_json::json!([
                {"name": "cleanup", "kind": "cleanup-status", "value": "unknown"}
            ])
        );
    }
}

#[test]
fn runtime_json_retains_all_resource_causes_phases_and_cleanup_states() {
    for cause in [
        ResourceFailureCause::ConfiguredCapacity,
        ResourceFailureCause::AllocatorRefused,
        ResourceFailureCause::StorageReservationFailed,
        ResourceFailureCause::WorkBudgetExhausted,
    ] {
        for phase in [
            RuntimePhase::Acquisition,
            RuntimePhase::Capture,
            RuntimePhase::Evaluation,
            RuntimePhase::Cleanup,
            RuntimePhase::Access,
            RuntimePhase::Teardown,
            RuntimePhase::DiagnosticPreparation,
        ] {
            for cleanup in [
                CleanupStatus::Complete,
                CleanupStatus::Incomplete,
                CleanupStatus::Unknown,
            ] {
                let RuntimeFailure::Report(mut report) =
                    RuntimeFailure::resource(ResourceFailure::new(
                        cause,
                        phase,
                        RuntimeResource::WorkUnits,
                        Some(0),
                        Some(usize::MAX),
                    ))
                else {
                    unreachable!()
                };
                report.cleanup = cleanup;
                let mut output = [0; 4096];
                let mut remaining = output.as_mut_slice();
                render::write_runtime_json(&mut remaining, RuntimeFailure::Report(report)).unwrap();
                let used = 4096 - remaining.len();
                let json: serde_json::Value = serde_json::from_slice(&output[..used]).unwrap();
                let facts = json["facts"].as_array().unwrap();
                let fact =
                    |name| facts.iter().find(|fact| fact["name"] == name).unwrap()["value"].clone();
                assert_eq!(json["reason"], cause.reason_code());
                assert_eq!(fact("phase"), phase.label());
                assert_eq!(fact("cleanup"), cleanup.label());
                assert_eq!(fact("requested"), 0);
                assert_eq!(fact("available"), usize::MAX);
                assert!(!facts.iter().any(|fact| fact["name"] == "teardown_cause"));
                assert_eq!(
                    facts.iter().any(|fact| fact["name"] == "underlying_cause"),
                    cause == ResourceFailureCause::StorageReservationFailed
                );
            }
        }
    }
}

#[test]
fn runtime_json_stops_at_every_failed_write_without_retry_or_flush() {
    use std::io::{self, Write};
    struct Writer {
        remaining: usize,
        failed: bool,
        zero: bool,
    }
    impl Write for Writer {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            assert!(!self.failed, "must not retry after a failed write");
            if self.remaining == 0 {
                self.failed = true;
                return if self.zero {
                    Ok(0)
                } else {
                    Err(io::ErrorKind::Interrupted.into())
                };
            }
            let count = bytes.len().min(self.remaining).min(3);
            self.remaining -= count;
            Ok(count)
        }
        fn flush(&mut self) -> io::Result<()> {
            assert!(!self.failed, "must not flush after a failed write");
            Ok(())
        }
    }
    let mut output = [0; 4096];
    let mut remaining = output.as_mut_slice();
    render::write_runtime_json(&mut remaining, failure()).unwrap();
    let length = 4096 - remaining.len();
    for zero in [false, true] {
        for remaining in 0..length {
            let mut writer = Writer {
                remaining,
                failed: false,
                zero,
            };
            let error = render::write_runtime_json(&mut writer, failure()).unwrap_err();
            assert_eq!(
                error.kind(),
                if zero {
                    io::ErrorKind::WriteZero
                } else {
                    io::ErrorKind::Interrupted
                }
            );
        }
        render::write_runtime_json(
            &mut Writer {
                remaining: length,
                failed: false,
                zero,
            },
            failure(),
        )
        .unwrap();
    }
}

#[test]
fn runtime_json_returns_flush_failure_without_retry() {
    use std::io::{self, Write};
    struct Writer {
        flushed: bool,
    }
    impl Write for Writer {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            assert!(!self.flushed);
            Ok(bytes.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            assert!(!self.flushed);
            self.flushed = true;
            Err(io::ErrorKind::Interrupted.into())
        }
    }
    let mut writer = Writer { flushed: false };
    assert_eq!(
        render::write_runtime_json(&mut writer, failure())
            .unwrap_err()
            .kind(),
        io::ErrorKind::Interrupted
    );
    assert!(writer.flushed);
}
