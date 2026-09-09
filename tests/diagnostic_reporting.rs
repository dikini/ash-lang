use ash::{
    diagnostic_options::MessageFormat,
    message::{Catalogue, Locale},
    module::{GraphDiagnostic, LoadGraphError},
    presentation::{
        compile_graph_diagnostics, write_compile_diagnostic, write_human, write_json, write_short,
    },
};
use std::io::{self, Write};

#[test]
fn compile_time_formats_stop_on_interrupted_writes() {
    struct Refuses {
        calls: usize,
    }
    impl Write for Refuses {
        fn write(&mut self, _: &[u8]) -> io::Result<usize> {
            self.calls += 1;
            assert_eq!(self.calls, 1, "must not retry a failed diagnostic write");
            Err(io::ErrorKind::Interrupted.into())
        }
        fn flush(&mut self) -> io::Result<()> {
            panic!("must not flush after write failure")
        }
    }
    let context = GraphDiagnostic::from(LoadGraphError::Read {
        path: "missing.ash".into(),
        kind: io::ErrorKind::NotFound,
        import_span: None,
    });
    let views = compile_graph_diagnostics(&context).unwrap();
    let catalogue = Catalogue::new(Locale::English).unwrap();
    for format in 0..3 {
        let mut writer = Refuses { calls: 0 };
        let result = match format {
            0 => write_human(&mut writer, &views[0], &catalogue),
            1 => write_short(&mut writer, &views[0], &catalogue),
            _ => write_json(&mut writer, &views[0]),
        };
        assert!(result.is_err());
        assert_eq!(writer.calls, 1);
    }
}

#[test]
fn compile_reporting_stops_at_every_output_failure_including_fallback() {
    struct Writer {
        remaining: usize,
        failed: bool,
        zero: bool,
    }
    impl Write for Writer {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            assert!(!self.failed, "must not retry or report an output error");
            if self.remaining == 0 {
                self.failed = true;
                return if self.zero {
                    Ok(0)
                } else {
                    Err(io::ErrorKind::Interrupted.into())
                };
            }
            let count = self.remaining.min(bytes.len()).min(3);
            self.remaining -= count;
            Ok(count)
        }
        fn flush(&mut self) -> io::Result<()> {
            assert!(!self.failed, "must not flush after output failure");
            Ok(())
        }
    }
    let context = GraphDiagnostic::from(LoadGraphError::Read {
        path: "missing.ash".into(),
        kind: io::ErrorKind::NotFound,
        import_span: None,
    });
    let views = compile_graph_diagnostics(&context).unwrap();
    for locale in [Locale::English, Locale::Bulgarian] {
        let catalogue = Catalogue::new(locale).unwrap();
        for catalogue in [Some(&catalogue), None] {
            for format in [
                MessageFormat::Human,
                MessageFormat::Short,
                MessageFormat::Json,
            ] {
                let mut expected = Vec::new();
                write_compile_diagnostic(&mut expected, &views[0], format, catalogue).unwrap();
                for zero in [false, true] {
                    for remaining in 0..expected.len() {
                        let mut writer = Writer {
                            remaining,
                            failed: false,
                            zero,
                        };
                        assert!(
                            write_compile_diagnostic(&mut writer, &views[0], format, catalogue)
                                .is_err()
                        );
                        assert!(writer.failed);
                    }
                    let mut writer = Writer {
                        remaining: expected.len(),
                        failed: false,
                        zero,
                    };
                    write_compile_diagnostic(&mut writer, &views[0], format, catalogue).unwrap();
                    assert_eq!(writer.remaining, 0);
                }
            }
        }
    }
}

#[test]
fn compile_reporting_does_not_retry_flush_failure() {
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
    let context = GraphDiagnostic::from(LoadGraphError::Read {
        path: "missing.ash".into(),
        kind: io::ErrorKind::NotFound,
        import_span: None,
    });
    let views = compile_graph_diagnostics(&context).unwrap();
    let catalogue = Catalogue::new(Locale::English).unwrap();
    for format in [
        MessageFormat::Human,
        MessageFormat::Short,
        MessageFormat::Json,
    ] {
        let mut writer = Writer { flushed: false };
        assert!(
            write_compile_diagnostic(&mut writer, &views[0], format, Some(&catalogue)).is_err()
        );
        assert!(writer.flushed);
    }
}
