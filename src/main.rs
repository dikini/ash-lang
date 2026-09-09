use std::{
    env,
    ffi::OsString,
    io::{self, Write},
    path::PathBuf,
    process::ExitCode,
};

use ash::{
    driver::{FileFailure, Observation, PipelineFailure, RunConfiguration, run_path},
    eval::RuntimeFailure,
    module::{LoadGraphError, ModuleRoots},
    render,
};

const USAGE: &[u8] = b"usage: ash [--root name=path]... <entry-file>\n";

fn main() -> ExitCode {
    let mut stdout = io::stdout().lock();
    let mut stderr = io::stderr().lock();
    ExitCode::from(execute(env::args_os().skip(1), &mut stdout, &mut stderr))
}

fn execute<I, O, E>(arguments: I, stdout: &mut O, stderr: &mut E) -> u8
where
    I: IntoIterator<Item = OsString>,
    O: Write,
    E: Write,
{
    execute_with_runner(arguments, stdout, stderr, run_path)
}

fn execute_with_runner<I, O, E, R>(arguments: I, stdout: &mut O, stderr: &mut E, runner: R) -> u8
where
    I: IntoIterator<Item = OsString>,
    O: Write,
    E: Write,
    R: FnOnce(RunConfiguration) -> Result<Observation, FileFailure>,
{
    let configuration = match configuration(arguments) {
        Ok(configuration) => configuration,
        Err(ConfigurationFailure::Usage) => {
            let _ = write_output(stderr, USAGE);
            return 2;
        }
        Err(ConfigurationFailure::Roots(failure)) => {
            let failure = FileFailure::Graph(LoadGraphError::Module(failure).into());
            let _ = write_output(stderr, render::file_failure(&failure).as_bytes());
            return 2;
        }
    };

    match runner(configuration) {
        Ok(observation) => {
            if write_output(stdout, render::observation(&observation).as_bytes()).is_ok() {
                0
            } else {
                let _ = write_output(
                    stderr,
                    b"internal.output-write\nfailed to write standard output\n",
                );
                2
            }
        }
        Err(failure) => {
            if let Some(PipelineFailure::Runtime(RuntimeFailure::Report(report))) =
                failure.pipeline_failure()
            {
                let _ = render::write_runtime_report(stderr, report);
                return 2;
            }
            let status = if failure.is_source_rejection() { 1 } else { 2 };
            if write_output(stderr, render::file_failure(&failure).as_bytes()).is_ok() {
                status
            } else {
                2
            }
        }
    }
}

fn write_output(writer: &mut impl Write, output: &[u8]) -> io::Result<()> {
    writer.write_all(output)?;
    writer.flush()
}

#[derive(Debug)]
enum ConfigurationFailure {
    Usage,
    Roots(ash::module::ModuleFailure),
}

fn configuration<I>(arguments: I) -> Result<RunConfiguration, ConfigurationFailure>
where
    I: IntoIterator<Item = OsString>,
{
    let mut arguments = arguments.into_iter();
    let mut roots = Vec::new();
    let mut entry = None;

    while let Some(argument) = arguments.next() {
        if argument == "--root" {
            if entry.is_some() {
                return Err(ConfigurationFailure::Usage);
            }
            let specification = arguments.next().ok_or(ConfigurationFailure::Usage)?;
            roots.push(parse_root_specification(specification)?);
        } else if argument.to_string_lossy().starts_with("--") || entry.is_some() {
            return Err(ConfigurationFailure::Usage);
        } else {
            entry = Some(PathBuf::from(argument));
        }
    }

    let entry = entry.ok_or(ConfigurationFailure::Usage)?;
    let roots = ModuleRoots::new(roots).map_err(ConfigurationFailure::Roots)?;
    Ok(RunConfiguration { entry, roots })
}

#[cfg(unix)]
fn parse_root_specification(
    specification: OsString,
) -> Result<(String, PathBuf), ConfigurationFailure> {
    use std::os::unix::ffi::{OsStrExt, OsStringExt};

    let bytes = specification.as_os_str().as_bytes();
    let separator = bytes
        .iter()
        .position(|byte| *byte == b'=')
        .ok_or(ConfigurationFailure::Usage)?;
    let name = std::str::from_utf8(&bytes[..separator]).map_err(|_| ConfigurationFailure::Usage)?;
    let path = &bytes[separator + 1..];
    if name.is_empty() || path.is_empty() {
        return Err(ConfigurationFailure::Usage);
    }
    Ok((
        name.to_owned(),
        PathBuf::from(OsString::from_vec(path.to_vec())),
    ))
}

#[cfg(not(unix))]
fn parse_root_specification(
    specification: OsString,
) -> Result<(String, PathBuf), ConfigurationFailure> {
    let specification = specification
        .into_string()
        .map_err(|_| ConfigurationFailure::Usage)?;
    let (name, path) = specification
        .split_once('=')
        .ok_or(ConfigurationFailure::Usage)?;
    if name.is_empty() || path.is_empty() {
        return Err(ConfigurationFailure::Usage);
    }
    Ok((name.to_owned(), PathBuf::from(path)))
}

#[cfg(test)]
mod tests {
    use std::{
        fs::{self, OpenOptions},
        io::{self, Write},
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::*;
    use ash::{
        core::{CoreBuilder, validate},
        driver::{FileFailure, PipelineFailure},
        eval::RuntimeFailure,
        integer::Integer,
        source::{ByteRange, Origin, SourceFile},
        types::Type,
    };

    static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

    struct AlwaysFails;

    impl Write for AlwaysFails {
        fn write(&mut self, _buffer: &[u8]) -> io::Result<usize> {
            Err(io::Error::new(
                io::ErrorKind::BrokenPipe,
                "deterministic test failure",
            ))
        }

        fn flush(&mut self) -> io::Result<()> {
            Err(io::Error::new(
                io::ErrorKind::BrokenPipe,
                "deterministic test failure",
            ))
        }
    }

    #[derive(Default)]
    struct FlushFails {
        bytes: Vec<u8>,
    }

    impl Write for FlushFails {
        fn write(&mut self, buffer: &[u8]) -> io::Result<usize> {
            self.bytes.extend_from_slice(buffer);
            Ok(buffer.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            Err(io::Error::new(
                io::ErrorKind::BrokenPipe,
                "deterministic flush failure",
            ))
        }
    }

    struct TempSource(PathBuf);

    impl TempSource {
        fn write(text: &[u8]) -> Self {
            loop {
                let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
                let path = std::env::temp_dir().join(format!(
                    "ash-main-write-failure-{}-{id}.ash",
                    std::process::id()
                ));
                match OpenOptions::new().write(true).create_new(true).open(&path) {
                    Ok(mut file) => {
                        file.write_all(text)
                            .expect("test source should be writable");
                        return Self(path);
                    }
                    Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                    Err(error) => panic!("test source should be creatable: {error}"),
                }
            }
        }

        fn valid() -> Self {
            Self::write(b"main : Unit -> Int\nmain () = 7\n")
        }

        fn rejected() -> Self {
            Self::write(b"main : Unit -> Int\nmain () = true + 1\n")
        }
    }

    impl Drop for TempSource {
        fn drop(&mut self) {
            let _ = fs::remove_file(&self.0);
        }
    }

    #[test]
    fn success_stdout_failure_returns_status_two_and_reports_on_stderr() {
        let source = TempSource::valid();
        let mut stdout = AlwaysFails;
        let mut stderr = Vec::new();

        let status = execute(
            [source.0.clone().into_os_string()],
            &mut stdout,
            &mut stderr,
        );

        assert_eq!(status, 2);
        assert_eq!(
            stderr,
            b"internal.output-write\nfailed to write standard output\n"
        );
    }

    #[test]
    fn usage_stderr_failure_returns_status_two_without_panicking() {
        let mut stdout = Vec::new();
        let mut stderr = AlwaysFails;

        let status = execute(std::iter::empty(), &mut stdout, &mut stderr);

        assert_eq!(status, 2);
        assert!(stdout.is_empty());
    }

    #[test]
    fn root_options_must_precede_the_entry_path() {
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let status = execute_with_runner(
            [
                OsString::from("entry.ash"),
                OsString::from("--root"),
                OsString::from("std=library"),
            ],
            &mut stdout,
            &mut stderr,
            |_| panic!("invalid invocation must not reach the runner"),
        );

        assert_eq!(status, 2);
        assert!(stdout.is_empty());
        assert_eq!(stderr, USAGE);
    }

    #[cfg(unix)]
    #[test]
    fn root_paths_retain_non_utf8_operating_system_bytes() {
        use std::os::unix::ffi::{OsStrExt, OsStringExt};

        let specification = OsString::from_vec(b"std=/tmp/ash-\xff".to_vec());
        let (name, path) =
            parse_root_specification(specification).expect("the root syntax should be valid");

        assert_eq!(name, "std");
        assert_eq!(path.as_os_str().as_bytes(), b"/tmp/ash-\xff");
    }

    #[test]
    fn source_diagnostic_stderr_failure_returns_status_two_without_panicking() {
        let source = TempSource::rejected();
        let mut stdout = Vec::new();
        let mut stderr = AlwaysFails;

        let status = execute(
            [source.0.clone().into_os_string()],
            &mut stdout,
            &mut stderr,
        );

        assert_eq!(status, 2);
        assert!(stdout.is_empty());
    }

    #[test]
    fn stdout_and_fallback_stderr_may_both_fail_without_panicking() {
        let source = TempSource::valid();
        let mut stdout = AlwaysFails;
        let mut stderr = AlwaysFails;

        let status = execute(
            [source.0.clone().into_os_string()],
            &mut stdout,
            &mut stderr,
        );

        assert_eq!(status, 2);
    }

    #[test]
    fn success_stdout_flush_failure_returns_status_two_and_reports_on_stderr() {
        let source = TempSource::valid();
        let mut stdout = FlushFails::default();
        let mut stderr = Vec::new();

        let status = execute(
            [source.0.clone().into_os_string()],
            &mut stdout,
            &mut stderr,
        );

        assert_eq!(status, 2);
        assert_eq!(stdout.bytes, b"7 : Int\n");
        assert_eq!(
            stderr,
            b"internal.output-write\nfailed to write standard output\n"
        );
    }

    #[test]
    fn source_diagnostic_stderr_flush_failure_returns_status_two_without_panicking() {
        let source = TempSource::rejected();
        let mut stdout = Vec::new();
        let mut stderr = FlushFails::default();

        let status = execute(
            [source.0.clone().into_os_string()],
            &mut stdout,
            &mut stderr,
        );

        assert_eq!(status, 2);
        assert!(stdout.is_empty());
        assert!(stderr.bytes.starts_with(b"type.operator-operand\n"));
    }

    #[test]
    fn injected_validator_failure_uses_internal_cli_observations() {
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let status = execute_with_runner(
            [OsString::from("injected.ash")],
            &mut stdout,
            &mut stderr,
            |_| Err(injected_validation_failure()),
        );

        assert_eq!(status, 2);
        assert!(stdout.is_empty());
        assert_eq!(stderr, b"core.validation.node-type\nnode: 0\n");
    }

    #[test]
    fn injected_runtime_failure_uses_internal_cli_observations() {
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let status = execute_with_runner(
            [OsString::from("injected.ash")],
            &mut stdout,
            &mut stderr,
            |_| {
                Err(FileFailure::from(PipelineFailure::Runtime(
                    RuntimeFailure::MissingBinding,
                )))
            },
        );

        assert_eq!(status, 2);
        assert!(stdout.is_empty());
        assert_eq!(
            stderr,
            b"runtime.missing-binding\nruntime lexical binding is absent\n"
        );
    }

    #[test]
    fn enriched_legacy_resource_report_uses_bounded_cause_writer() {
        use ash::eval::{
            CleanupStatus, ResourceFailure, ResourceFailureCause, RuntimePhase, RuntimeResource,
        };
        for (legacy, phase, cause) in [
            (
                RuntimeFailure::CapturedControlCapacity,
                RuntimePhase::Capture,
                ResourceFailureCause::ConfiguredCapacity,
            ),
            (
                RuntimeFailure::EnvironmentCapacity,
                RuntimePhase::Access,
                ResourceFailureCause::WorkBudgetExhausted,
            ),
            (
                RuntimeFailure::CapturedControlCapacity,
                RuntimePhase::Capture,
                ResourceFailureCause::StorageReservationFailed,
            ),
        ] {
            let RuntimeFailure::Report(mut report) =
                legacy.with_resource_details(ResourceFailure::new(
                    cause,
                    phase,
                    RuntimeResource::FrameStorage,
                    Some(1),
                    Some(0),
                ))
            else {
                panic!("report")
            };
            report.cleanup = CleanupStatus::Complete;
            let mut stdout = [0; 0];
            let mut output = [0; 512];
            let mut remaining = output.as_mut_slice();
            let status = execute_with_runner(
                [OsString::from("injected.ash")],
                &mut stdout.as_mut_slice(),
                &mut remaining,
                |_| {
                    Err(FileFailure::from(PipelineFailure::Runtime(
                        RuntimeFailure::Report(report),
                    )))
                },
            );
            assert_eq!(status, 2);
            let used = 512 - remaining.len();
            let output = std::str::from_utf8(&output[..used]).unwrap();
            assert!(output.starts_with(legacy.reason_code()));
            assert!(output.contains(&format!("cause: {}\n", cause.reason_code())));
            assert!(output.contains(&format!("phase: {}\n", phase.label())));
            assert!(output.ends_with("cleanup: complete\n"));
            assert_eq!(
                output.contains("underlying cause: undetermined"),
                cause == ResourceFailureCause::StorageReservationFailed
            );
        }
    }

    #[test]
    fn runtime_resource_failure_reports_primary_secondary_and_cleanup() {
        use ash::eval::{
            CleanupStatus, ResourceFailure, ResourceFailureCause, RuntimePhase, RuntimeResource,
        };
        let primary = RuntimeFailure::resource(ResourceFailure::new(
            ResourceFailureCause::WorkBudgetExhausted,
            RuntimePhase::Access,
            RuntimeResource::WorkUnits,
            Some(3),
            Some(2),
        ));
        let failure = primary.with_teardown_failure(
            ResourceFailure::new(
                ResourceFailureCause::AllocatorRefused,
                RuntimePhase::Teardown,
                RuntimeResource::FrameStorage,
                Some(8),
                None,
            ),
            CleanupStatus::Incomplete,
        );
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();
        let status = execute_with_runner(
            [OsString::from("injected.ash")],
            &mut stdout,
            &mut stderr,
            |_| Err(FileFailure::from(PipelineFailure::Runtime(failure))),
        );
        assert_eq!(status, 2);
        assert!(stdout.is_empty());
        assert_eq!(stderr, b"runtime.work-budget-exhausted\nphase: access\nresource: runtime work units\nrequested: 3\navailable: 2\nteardown: runtime.allocator-refused\nphase: teardown\nresource: control frames\nrequested: 8\ncleanup: incomplete\n");
    }

    #[test]
    fn resource_diagnostic_stops_at_first_writer_error_without_retry_or_flush() {
        use ash::eval::{ResourceFailure, ResourceFailureCause, RuntimePhase, RuntimeResource};
        struct Refuses {
            calls: usize,
        }
        impl Write for Refuses {
            fn write(&mut self, _: &[u8]) -> io::Result<usize> {
                self.calls += 1;
                Err(io::ErrorKind::Interrupted.into())
            }
            fn flush(&mut self) -> io::Result<()> {
                panic!("must stop on write failure")
            }
        }
        let failure = RuntimeFailure::resource(ResourceFailure::new(
            ResourceFailureCause::AllocatorRefused,
            RuntimePhase::Acquisition,
            RuntimeResource::FrameStorage,
            None,
            None,
        ));
        let mut stdout = Vec::new();
        let mut stderr = Refuses { calls: 0 };
        let status = execute_with_runner(
            [OsString::from("injected.ash")],
            &mut stdout,
            &mut stderr,
            |_| Err(FileFailure::from(PipelineFailure::Runtime(failure))),
        );
        assert_eq!(status, 2);
        assert!(stdout.is_empty());
        assert_eq!(stderr.calls, 1);
    }

    #[test]
    fn resource_diagnostics_fit_stack_storage_with_maximum_and_zero_amounts() {
        use ash::eval::{
            CleanupStatus, ResourceFailure, ResourceFailureCause, RuntimePhase, RuntimeResource,
        };
        for (cause, phase, cleanup) in [
            (
                ResourceFailureCause::ConfiguredCapacity,
                RuntimePhase::Acquisition,
                CleanupStatus::Unknown,
            ),
            (
                ResourceFailureCause::AllocatorRefused,
                RuntimePhase::Capture,
                CleanupStatus::Incomplete,
            ),
            (
                ResourceFailureCause::WorkBudgetExhausted,
                RuntimePhase::Access,
                CleanupStatus::Complete,
            ),
            (
                ResourceFailureCause::StorageReservationFailed,
                RuntimePhase::Teardown,
                CleanupStatus::Unknown,
            ),
        ] {
            let RuntimeFailure::Report(mut report) =
                RuntimeFailure::resource(ResourceFailure::new(
                    cause,
                    phase,
                    RuntimeResource::WorkUnits,
                    Some(usize::MAX),
                    Some(0),
                ))
            else {
                panic!("report")
            };
            report.cleanup = cleanup;
            let mut output = [0; 512];
            let mut remaining = output.as_mut_slice();
            render::write_runtime_report(&mut remaining, &report).unwrap();
            let used = 512 - remaining.len();
            let output = &output[..used];
            assert!(output.starts_with(cause.reason_code().as_bytes()));
            assert!(
                output
                    .windows(b"available: 0\n".len())
                    .any(|part| part == b"available: 0\n")
            );
            assert!(
                output
                    .windows(phase.label().len())
                    .any(|part| part == phase.label().as_bytes())
            );
            let maximum = usize::MAX.to_string();
            assert!(
                output
                    .windows(maximum.len())
                    .any(|part| part == maximum.as_bytes())
            );
            assert!(output.ends_with(format!("cleanup: {}\n", cleanup.label()).as_bytes()));
            assert_eq!(
                output
                    .windows(b"underlying cause: undetermined\n".len())
                    .any(|part| part == b"underlying cause: undetermined\n"),
                cause == ResourceFailureCause::StorageReservationFailed
            );
        }
    }

    fn injected_validation_failure() -> FileFailure {
        let source = SourceFile::new("injected.ash", "1").expect("the test source should fit");
        let span = source
            .span(ByteRange::new(0, 1).expect("ordered fixture range"))
            .expect("fixture range should belong to the source");
        let mut builder = CoreBuilder::new();
        let root = builder
            .integer(
                Integer::parse_decimal("1").expect("valid fixture integer"),
                Type::Bool,
                Origin::Source(span),
            )
            .expect("unchecked construction should retain the malformed type");
        let error = validate(
            builder
                .finish(root)
                .expect("root should belong to its arena"),
            &[&source],
        )
        .expect_err("independent validation should reject the malformed type");
        FileFailure::from(PipelineFailure::Validation(error))
    }
}
