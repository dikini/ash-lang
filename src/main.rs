use std::{
    env,
    ffi::OsString,
    io::{self, Write},
    path::PathBuf,
    process::ExitCode,
};

use {
    ash::build::BuildConfiguration, ash::build::NativeLinkInput, ash::build::build_path,
    ash::driver::FileFailure, ash::driver::Observation, ash::driver::PipelineFailure,
    ash::driver::RunConfiguration, ash::driver::run_path, ash::module::LoadGraphError,
    ash::module::ModuleRoots, ash::render,
};

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
    let selected = ash::diagnostic_options::DiagnosticOptions::parse(
        arguments,
        [
            env::var_os("LC_ALL"),
            env::var_os("LC_MESSAGES"),
            env::var_os("LANG"),
        ],
    );
    execute_with_diagnostics(selected, stdout, stderr, runner)
}

fn execute_with_diagnostics<O: Write, E: Write, R>(
    selected: ash::diagnostic_options::DiagnosticOptions,
    stdout: &mut O,
    stderr: &mut E,
    runner: R,
) -> u8
where
    R: FnOnce(RunConfiguration) -> Result<Observation, FileFailure>,
{
    use ash::{diagnostic_options::MessageFormat, message::Catalogue, presentation};
    let format = selected.format;
    let catalogue = if format == MessageFormat::Json {
        None
    } else {
        Catalogue::new(selected.locale).ok()
    };
    if selected.invalid_options {
        let _ = presentation::write_compile_diagnostic(
            stderr,
            &presentation::compile_usage_diagnostic(),
            format,
            catalogue.as_ref(),
        );
        return 2;
    }
    let invocation = match invocation(selected.program_arguments) {
        Ok(configuration) => configuration,
        Err(ConfigurationFailure::Usage) => {
            let _ = presentation::write_compile_diagnostic(
                stderr,
                &presentation::compile_usage_diagnostic(),
                format,
                catalogue.as_ref(),
            );
            return 2;
        }
        Err(ConfigurationFailure::Roots(failure)) => {
            let failure = FileFailure::Graph(LoadGraphError::Module(failure).into());
            let _ = report_selected_failure(stderr, &failure, format, catalogue.as_ref(), None);
            return 2;
        }
    };
    let configuration = match invocation {
        Invocation::Run(configuration) => configuration,
        Invocation::Build(source, configuration) => {
            return execute_build(
                source,
                configuration,
                stdout,
                stderr,
                format,
                catalogue.as_ref(),
            );
        }
    };
    let runtime_messages = catalogue
        .as_ref()
        .and_then(|catalogue| render::PreparedRuntimeMessages::new(catalogue).ok());
    // Prepare the stdout-write diagnostic before execution too. Reporting that
    // failure must not depend on allocating or formatting another message.
    let mut output_failure = Vec::new();
    let _ = presentation::write_compile_diagnostic(
        &mut output_failure,
        &presentation::compile_output_write_diagnostic(),
        format,
        catalogue.as_ref(),
    );
    match runner(configuration) {
        Ok(observation) => {
            if write_output(stdout, render::observation(&observation).as_bytes()).is_ok() {
                0
            } else {
                let _ = write_output_no_retry(stderr, &output_failure);
                2
            }
        }
        Err(failure) => {
            let status = if failure.is_source_rejection() { 1 } else { 2 };
            if report_selected_failure(
                stderr,
                &failure,
                format,
                catalogue.as_ref(),
                runtime_messages.as_ref(),
            )
            .is_ok()
            {
                status
            } else {
                2
            }
        }
    }
}

fn execute_build(
    source: RunConfiguration,
    configuration: BuildConfiguration,
    stdout: &mut impl Write,
    stderr: &mut impl Write,
    format: ash::diagnostic_options::MessageFormat,
    catalogue: Option<&ash::message::Catalogue>,
) -> u8 {
    match build_path(source, configuration) {
        Ok(built) => {
            if writeln!(stdout, "{}", built.executable().display())
                .and_then(|()| stdout.flush())
                .is_ok()
            {
                0
            } else {
                let _ = ash::presentation::write_compile_diagnostic(
                    stderr,
                    &ash::presentation::compile_output_write_diagnostic(),
                    format,
                    catalogue,
                );
                2
            }
        }
        Err(failure) => {
            if let Some(source) = failure.source_failure() {
                let status = if source.is_source_rejection() { 1 } else { 2 };
                return if report_selected_failure(stderr, source, format, catalogue, None).is_ok() {
                    status
                } else {
                    2
                };
            }
            let detail = failure.to_string();
            let _ = ash::presentation::write_compile_diagnostic(
                stderr,
                &ash::presentation::compile_build_diagnostic(&failure, &detail),
                format,
                catalogue,
            );
            2
        }
    }
}

fn report_selected_failure(
    writer: &mut impl Write,
    failure: &FileFailure,
    format: ash::diagnostic_options::MessageFormat,
    catalogue: Option<&ash::message::Catalogue>,
    runtime_messages: Option<&render::PreparedRuntimeMessages>,
) -> Result<(), ash::presentation::RenderError> {
    use ash::presentation;
    if let Some(PipelineFailure::Runtime(error)) = failure.pipeline_failure() {
        return render::write_runtime_diagnostic(writer, *error, format, runtime_messages)
            .map_err(presentation::RenderError::Write);
    }
    match presentation::compile_file_diagnostics(failure) {
        Ok(diagnostics) => {
            for diagnostic in &diagnostics {
                presentation::write_compile_diagnostic(writer, diagnostic, format, catalogue)?;
            }
            Ok(())
        }
        Err(error) => presentation::write_unadapted_file_diagnostic(writer, failure, error),
    }
}

fn write_output_no_retry(writer: &mut impl Write, mut output: &[u8]) -> io::Result<()> {
    while !output.is_empty() {
        let count = writer.write(output)?;
        if count == 0 || count > output.len() {
            return Err(io::ErrorKind::WriteZero.into());
        }
        output = &output[count..];
    }
    writer.flush()
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

enum Invocation {
    Run(RunConfiguration),
    Build(RunConfiguration, BuildConfiguration),
}

fn invocation(arguments: Vec<OsString>) -> Result<Invocation, ConfigurationFailure> {
    if arguments.first().is_none_or(|argument| argument != "build") {
        return configuration(arguments).map(Invocation::Run);
    }
    let mut arguments = arguments.into_iter().skip(1);
    let mut source_arguments = Vec::new();
    let mut output = None;
    let mut target = None;
    let mut cache = None;
    let mut native_inputs = Vec::new();
    let mut entry_seen = false;
    while let Some(argument) = arguments.next() {
        if entry_seen {
            return Err(ConfigurationFailure::Usage);
        }
        match argument.to_str() {
            Some("--output") => {
                let path = arguments.next().ok_or(ConfigurationFailure::Usage)?;
                if output.replace(PathBuf::from(path)).is_some() {
                    return Err(ConfigurationFailure::Usage);
                }
            }
            Some("--target") => {
                let value = arguments.next().ok_or(ConfigurationFailure::Usage)?;
                let value = value
                    .into_string()
                    .map_err(|_| ConfigurationFailure::Usage)?;
                if target.replace(value).is_some() {
                    return Err(ConfigurationFailure::Usage);
                }
            }
            Some("--cargo-target-dir") => {
                let path = arguments.next().ok_or(ConfigurationFailure::Usage)?;
                if cache.replace(PathBuf::from(path)).is_some() {
                    return Err(ConfigurationFailure::Usage);
                }
            }
            Some("--native-static" | "--native-shared") => {
                let path = PathBuf::from(arguments.next().ok_or(ConfigurationFailure::Usage)?);
                native_inputs.push(if argument == "--native-static" {
                    NativeLinkInput::StaticArchive(path)
                } else {
                    NativeLinkInput::SharedLibrary(path)
                });
            }
            Some("--root") => {
                source_arguments.push(argument);
                source_arguments.push(arguments.next().ok_or(ConfigurationFailure::Usage)?);
            }
            _ if argument.as_encoded_bytes().starts_with(b"--") => {
                return Err(ConfigurationFailure::Usage);
            }
            _ => {
                source_arguments.push(argument);
                entry_seen = true;
            }
        }
    }
    let source = configuration(source_arguments)?;
    let mut build = BuildConfiguration::new(output.ok_or(ConfigurationFailure::Usage)?);
    if let Some(target) = target {
        build.target = target;
    }
    build.cargo_target_directory = cache;
    build.native_inputs = native_inputs;
    Ok(Invocation::Build(source, build))
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
    #[test]
    fn native_build_inputs_preserve_mixed_order_duplicates_and_paths() {
        let arguments = [
            "build",
            "--output",
            "program with spaces",
            "--native-shared",
            "shared library.so",
            "--native-static",
            "first archive.a",
            "--native-shared",
            "shared library.so",
            "--native-static",
            "last archive.a",
            "entry.ash",
        ];
        let Invocation::Build(_, build) =
            invocation(arguments.map(OsString::from).to_vec()).expect("repeatable native inputs")
        else {
            panic!("build invocation")
        };
        let inputs: Vec<_> = build
            .native_inputs
            .iter()
            .map(|input| match input {
                ash::build::NativeLinkInput::StaticArchive(path) => ("static", path.as_path()),
                ash::build::NativeLinkInput::SharedLibrary(path) => ("shared", path.as_path()),
            })
            .collect();
        assert_eq!(
            inputs,
            [
                ("shared", std::path::Path::new("shared library.so")),
                ("static", std::path::Path::new("first archive.a")),
                ("shared", std::path::Path::new("shared library.so")),
                ("static", std::path::Path::new("last archive.a"))
            ]
        );
        assert_eq!(build.output, PathBuf::from("program with spaces"));
    }

    #[cfg(unix)]
    #[test]
    fn native_build_inputs_preserve_non_utf8_operating_system_paths() {
        use std::os::unix::ffi::OsStringExt;
        for flag in ["--native-static", "--native-shared"] {
            let path = OsString::from_vec(b"native inputs/lib-\xff".to_vec());
            let Invocation::Build(_, build) = invocation(vec![
                "build".into(),
                "--output".into(),
                "program".into(),
                flag.into(),
                path.clone(),
                "entry.ash".into(),
            ])
            .expect("OS path") else {
                panic!("build invocation")
            };
            match &build.native_inputs[0] {
                ash::build::NativeLinkInput::StaticArchive(actual) => {
                    assert_eq!(flag, "--native-static");
                    assert_eq!(actual.as_os_str(), path);
                }
                ash::build::NativeLinkInput::SharedLibrary(actual) => {
                    assert_eq!(flag, "--native-shared");
                    assert_eq!(actual.as_os_str(), path);
                }
            }
        }
    }

    #[test]
    fn explicit_runtime_formats_use_the_separate_reporter() {
        for format in ["human", "short", "json"] {
            let mut stdout = Vec::new();
            let mut stderr = Vec::new();
            let status = execute_with_runner(
                ["--message-format", format, "--locale", "en", "injected.ash"].map(OsString::from),
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
            if format == "json" {
                let json: serde_json::Value = serde_json::from_slice(&stderr).unwrap();
                assert_eq!(json["reason"], "runtime.missing-binding");
                assert_eq!(json["responsibility"], "runtime");
            } else {
                assert!(
                    std::str::from_utf8(&stderr)
                        .unwrap()
                        .starts_with("The runtime could not find a variable's lexical binding.")
                );
            }
        }
    }

    #[test]
    fn explicit_internal_failure_preserves_its_category_in_json() {
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();
        let status = execute_with_runner(
            ["--message-format", "json", "injected.ash"].map(OsString::from),
            &mut stdout,
            &mut stderr,
            |_| {
                Err(FileFailure::from(PipelineFailure::Typing(
                    ash::elaborate::TypeError::Internal(
                        ash::elaborate::ElaborationFailure::InvalidState,
                    ),
                )))
            },
        );
        assert_eq!(status, 2);
        let json: serde_json::Value = serde_json::from_slice(&stderr).unwrap();
        assert_eq!(json["reason"], "type.internal");
        assert_eq!(json["responsibility"], "compiler");
        assert_eq!(json["facts"][0]["name"], "cause");
        assert_eq!(json["facts"][0]["value"], "invalid-state");
        assert!(json.get("developer_details").is_none());
    }

    #[test]
    fn explicit_diagnostics_never_retry_a_failed_stderr_write() {
        struct Refuses {
            calls: usize,
        }
        impl Write for Refuses {
            fn write(&mut self, _: &[u8]) -> io::Result<usize> {
                self.calls += 1;
                assert_eq!(self.calls, 1);
                Err(io::ErrorKind::Interrupted.into())
            }
            fn flush(&mut self) -> io::Result<()> {
                panic!("must not flush after failure")
            }
        }
        for format in ["human", "short", "json"] {
            let mut stdout = Vec::new();
            let mut stderr = Refuses { calls: 0 };
            assert_eq!(
                execute_with_runner(
                    ["--message-format", format, "injected.ash"].map(OsString::from),
                    &mut stdout,
                    &mut stderr,
                    |_| Err(FileFailure::from(PipelineFailure::Runtime(
                        RuntimeFailure::MissingBinding
                    ))),
                ),
                2
            );
            assert_eq!(stderr.calls, 1);
        }
    }

    #[test]
    fn explicit_stdout_failure_uses_the_prepared_json_report() {
        let source = TempSource::valid();
        let mut stdout = AlwaysFails;
        let mut stderr = Vec::new();
        let status = execute(
            [
                OsString::from("--message-format"),
                OsString::from("json"),
                source.0.clone().into_os_string(),
            ],
            &mut stdout,
            &mut stderr,
        );
        assert_eq!(status, 2);
        let json: serde_json::Value = serde_json::from_slice(&stderr).unwrap();
        assert_eq!(json["reason"], "internal.output-write");
    }

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
            [
                OsString::from("--locale"),
                OsString::from("en"),
                source.0.clone().into_os_string(),
            ],
            &mut stdout,
            &mut stderr,
        );

        assert_eq!(status, 2);
        assert_eq!(
            stderr,
            b"Ash could not write the program result to standard output.\nreason: internal.output-write\n"
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
        assert!(
            String::from_utf8(stderr)
                .unwrap()
                .contains("invocation.usage")
        );
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
            [
                OsString::from("--locale"),
                OsString::from("en"),
                source.0.clone().into_os_string(),
            ],
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
            [
                OsString::from("--locale"),
                OsString::from("en"),
                source.0.clone().into_os_string(),
            ],
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
            [
                OsString::from("--locale"),
                OsString::from("en"),
                source.0.clone().into_os_string(),
            ],
            &mut stdout,
            &mut stderr,
        );

        assert_eq!(status, 2);
        assert_eq!(stdout.bytes, b"7 : Int\n");
        assert_eq!(
            stderr,
            b"Ash could not write the program result to standard output.\nreason: internal.output-write\n"
        );
    }

    #[test]
    fn source_diagnostic_stderr_flush_failure_returns_status_two_without_panicking() {
        let source = TempSource::rejected();
        let mut stdout = Vec::new();
        let mut stderr = FlushFails::default();

        let status = execute(
            [
                OsString::from("--locale"),
                OsString::from("en"),
                source.0.clone().into_os_string(),
            ],
            &mut stdout,
            &mut stderr,
        );

        assert_eq!(status, 2);
        assert!(stdout.is_empty());
        assert!(
            String::from_utf8(stderr.bytes)
                .unwrap()
                .contains("reason: type.operator-operand\n")
        );
    }

    #[test]
    fn injected_validator_failure_uses_internal_cli_observations() {
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let status = execute_with_runner(
            ["--locale", "en", "injected.ash"].map(OsString::from),
            &mut stdout,
            &mut stderr,
            |_| Err(injected_validation_failure()),
        );

        assert_eq!(status, 2);
        assert!(stdout.is_empty());
        assert_eq!(stderr, b"The compiler produced inconsistent type information for a Core node or its checked evidence. Core node: 0.\nreason: core.validation.node-type\n");
    }

    #[test]
    fn injected_runtime_failure_uses_internal_cli_observations() {
        let mut stdout = Vec::new();
        let mut stderr = Vec::new();

        let status = execute_with_runner(
            ["--locale", "en", "injected.ash"].map(OsString::from),
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
            b"The runtime could not find a variable's lexical binding. [runtime.missing-binding]\nCleanup status: Host cleanup completion has not been established.\n"
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
                ["--locale", "en", "injected.ash"].map(OsString::from),
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
            assert!(output.contains(&format!("[{}]", legacy.reason_code())));
            assert!(output.contains(&format!("[{}]", cause.reason_code())));
            assert!(output.contains(phase.label()));
            assert!(output.ends_with("Cleanup status: Host cleanup completed.\n"));
            assert_eq!(
                output.contains("underlying cause is undetermined"),
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
            ["--locale", "en", "injected.ash"].map(OsString::from),
            &mut stdout,
            &mut stderr,
            |_| Err(FileFailure::from(PipelineFailure::Runtime(failure))),
        );
        assert_eq!(status, 2);
        assert!(stdout.is_empty());
        assert_eq!(stderr, b"The runtime work budget cannot admit the requested work. [runtime.work-budget-exhausted]\nPhase: effect access\nResource: runtime work units\nRequested additional units: 3\nAvailable additional units: 2\nFirst teardown failure: The host allocator refused a storage reservation. [runtime.allocator-refused]\nPhase: host teardown\nResource: control frames\nRequested additional units: 8\nCleanup status: Host cleanup stopped before all retained state was released.\n");
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
            ["--locale", "en", "injected.ash"].map(OsString::from),
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
