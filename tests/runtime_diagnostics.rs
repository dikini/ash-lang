use ash::{
    eval::{
        CleanupStatus, ResourceFailure, ResourceFailureCause, RuntimeFailure, RuntimePhase,
        RuntimeResource,
    },
    render,
};

fn prepared_locales() -> [render::PreparedRuntimeMessages; 2] {
    use ash::message::{Catalogue, Locale};
    [Locale::English, Locale::Bulgarian].map(|locale| {
        render::PreparedRuntimeMessages::new(&Catalogue::new(locale).unwrap()).unwrap()
    })
}

enum Format<'a> {
    Json,
    Human(&'a render::PreparedRuntimeMessages),
    Short(&'a render::PreparedRuntimeMessages),
}

impl Format<'_> {
    fn write(
        &self,
        writer: &mut impl std::io::Write,
        failure: RuntimeFailure,
    ) -> std::io::Result<()> {
        match self {
            Self::Json => render::write_runtime_json(writer, failure),
            Self::Human(messages) => render::write_runtime_human(writer, failure, messages),
            Self::Short(messages) => render::write_runtime_short(writer, failure, messages),
        }
    }
}

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
fn runtime_human_leads_with_an_explanation() {
    let catalogue = ash::message::Catalogue::new(ash::message::Locale::English).unwrap();
    let messages = render::PreparedRuntimeMessages::new(&catalogue).unwrap();
    drop(catalogue);
    let mut output = [0; 8192];
    let mut remaining = output.as_mut_slice();
    render::write_runtime_human(&mut remaining, failure(), &messages).unwrap();
    let used = 8192 - remaining.len();
    let text = std::str::from_utf8(&output[..used]).unwrap();
    assert!(text.starts_with(
        "The runtime could not find a variable's lexical binding. [runtime.missing-binding]"
    ));
}

#[test]
fn prepared_runtime_text_localizes_both_formats_without_a_live_catalogue() {
    use ash::message::{Catalogue, Locale};
    let failure = RuntimeFailure::resource(ResourceFailure::new(
        ResourceFailureCause::WorkBudgetExhausted,
        RuntimePhase::Access,
        RuntimeResource::WorkUnits,
        Some(3),
        Some(2),
    ));
    for (locale, expected) in [
        (
            Locale::English,
            "The runtime work budget cannot admit the requested work. [runtime.work-budget-exhausted]\nPhase: effect access\nResource: runtime work units\nRequested additional units: 3\nAvailable additional units: 2\nCleanup status: Host cleanup completion has not been established.\n",
        ),
        (
            Locale::Bulgarian,
            "Бюджетът за работа на средата за изпълнение не допуска заявената работа. [runtime.work-budget-exhausted]\nФаза: достъп до ефект\nРесурс: единици работа на средата за изпълнение\nЗаявени допълнителни единици: 3\nНалични допълнителни единици: 2\nСъстояние на почистването: Не е установено дали почистването от хоста е завършило.\n",
        ),
    ] {
        let catalogue = Catalogue::new(locale).unwrap();
        let messages = render::PreparedRuntimeMessages::new(&catalogue).unwrap();
        drop(catalogue);
        for short in [false, true] {
            let mut output = [0; 8192];
            let mut remaining = output.as_mut_slice();
            if short {
                render::write_runtime_short(&mut remaining, failure, &messages).unwrap();
            } else {
                render::write_runtime_human(&mut remaining, failure, &messages).unwrap();
            }
            let used = 8192 - remaining.len();
            let text = std::str::from_utf8(&output[..used]).unwrap();
            if short {
                assert_eq!(
                    text,
                    format!("{}\n", expected.trim_end().replace('\n', "; "))
                );
            } else {
                assert_eq!(text, expected);
            }
        }
    }
}

#[test]
fn prepared_runtime_text_covers_existing_resource_units_and_secondary_failure() {
    use ash::message::{Catalogue, Locale};
    for locale in [Locale::English, Locale::Bulgarian] {
        let messages =
            render::PreparedRuntimeMessages::new(&Catalogue::new(locale).unwrap()).unwrap();
        for resource in [
            RuntimeResource::TypeDisposal,
            RuntimeResource::KindDisposal,
            RuntimeResource::EnvironmentDisposal,
            RuntimeResource::CapturedDisposal,
            RuntimeResource::WorkUnits,
            RuntimeResource::ResourceOwners,
            RuntimeResource::CleanupOwners,
            RuntimeResource::RegistrationOwners,
            RuntimeResource::RegistrationKeys,
            RuntimeResource::RegistrationInvocations,
            RuntimeResource::ActivationKeys,
            RuntimeResource::EnvironmentBindings,
            RuntimeResource::FrameStorage,
            RuntimeResource::EffectTrace,
            RuntimeResource::EvaluationTrace,
            RuntimeResource::ResultHeapCells,
            RuntimeResource::HeapCells,
            RuntimeResource::InstantiationEntries,
            RuntimeResource::InstantiationStorage,
            RuntimeResource::CaptureInspection,
            RuntimeResource::RegistrationIdentities,
        ] {
            let failure = failure().with_teardown_failure(
                ResourceFailure::new(
                    ResourceFailureCause::ConfiguredCapacity,
                    RuntimePhase::Cleanup,
                    resource,
                    None,
                    None,
                ),
                CleanupStatus::Incomplete,
            );
            // Existing reports retain the first teardown failure, not the later one.
            let mut output = [0; 8192];
            let mut remaining = output.as_mut_slice();
            render::write_runtime_short(&mut remaining, failure, &messages).unwrap();
            let used = 8192 - remaining.len();
            let text = std::str::from_utf8(&output[..used]).unwrap();
            assert!(text.contains("[runtime.missing-binding]"));
            assert!(text.contains("[runtime.storage-reservation-failed]"));
            assert!(text.contains("[runtime.allocator-refused]"));
            assert!(!text.contains("[runtime.capacity-exhausted]"));
            assert_eq!(text.lines().count(), 1);
            let failure = RuntimeFailure::resource(ResourceFailure::new(
                ResourceFailureCause::ConfiguredCapacity,
                RuntimePhase::Acquisition,
                resource,
                Some(usize::MAX),
                Some(0),
            ));
            render::write_runtime_human(&mut output.as_mut_slice(), failure, &messages).unwrap();
        }
    }
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
    let messages = prepared_locales();
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
        for prepared in &messages {
            for format in [Format::Human(prepared), Format::Short(prepared)] {
                format.write(&mut output.as_mut_slice(), failure).unwrap();
            }
        }
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
    let messages = prepared_locales();
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
                for prepared in &messages {
                    for format in [Format::Human(prepared), Format::Short(prepared)] {
                        format
                            .write(&mut output.as_mut_slice(), RuntimeFailure::Report(report))
                            .unwrap();
                    }
                }
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
fn runtime_formats_stop_at_every_failed_write_without_retry_or_flush() {
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
    let [english, bulgarian] = prepared_locales();
    for format in [
        Format::Json,
        Format::Human(&english),
        Format::Short(&english),
        Format::Human(&bulgarian),
        Format::Short(&bulgarian),
    ] {
        let mut output = [0; 4096];
        let mut remaining = output.as_mut_slice();
        format.write(&mut remaining, failure()).unwrap();
        let length = 4096 - remaining.len();
        for zero in [false, true] {
            for remaining in 0..length {
                let mut writer = Writer {
                    remaining,
                    failed: false,
                    zero,
                };
                let error = format.write(&mut writer, failure()).unwrap_err();
                assert_eq!(
                    error.kind(),
                    if zero {
                        io::ErrorKind::WriteZero
                    } else {
                        io::ErrorKind::Interrupted
                    }
                );
            }
            format
                .write(
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
}

#[test]
fn runtime_formats_return_flush_failure_without_retry() {
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
    let [english, bulgarian] = prepared_locales();
    for format in [
        Format::Json,
        Format::Human(&english),
        Format::Short(&english),
        Format::Human(&bulgarian),
        Format::Short(&bulgarian),
    ] {
        let mut writer = Writer { flushed: false };
        assert_eq!(
            format.write(&mut writer, failure()).unwrap_err().kind(),
            io::ErrorKind::Interrupted
        );
        assert!(writer.flushed);
    }
}
