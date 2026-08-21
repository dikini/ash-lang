use std::{
    env,
    ffi::OsString,
    io::{self, Write},
    path::PathBuf,
    process::ExitCode,
};

use ash::{driver::run_path, render};

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
    let Some(path) = exactly_one(arguments.into_iter()) else {
        let _ = write_output(stderr, b"usage: ash <source-file>\n");
        return 2;
    };

    match run_path(PathBuf::from(path)) {
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

fn exactly_one(mut arguments: impl Iterator<Item = OsString>) -> Option<OsString> {
    let only = arguments.next()?;
    arguments.next().is_none().then_some(only)
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        io::{self, Write},
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::*;

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
        fn rejected() -> Self {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "ash-main-write-failure-{}-{id}.ash",
                std::process::id()
            ));
            fs::write(&path, b"true + 1\n").expect("test source should be writable");
            Self(path)
        }
    }

    impl Drop for TempSource {
        fn drop(&mut self) {
            let _ = fs::remove_file(&self.0);
        }
    }

    fn valid_fixture() -> OsString {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/first-stratum/valid/v001-precedence.ash")
            .into_os_string()
    }

    #[test]
    fn success_stdout_failure_returns_status_two_and_reports_on_stderr() {
        let mut stdout = AlwaysFails;
        let mut stderr = Vec::new();

        let status = execute([valid_fixture()], &mut stdout, &mut stderr);

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
        let mut stdout = AlwaysFails;
        let mut stderr = AlwaysFails;

        let status = execute([valid_fixture()], &mut stdout, &mut stderr);

        assert_eq!(status, 2);
    }

    #[test]
    fn success_stdout_flush_failure_returns_status_two_and_reports_on_stderr() {
        let mut stdout = FlushFails::default();
        let mut stderr = Vec::new();

        let status = execute([valid_fixture()], &mut stdout, &mut stderr);

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
}
