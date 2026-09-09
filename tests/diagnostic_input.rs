use ash::{
    message::{Catalogue, Locale},
    module::{GraphDiagnostic, LoadGraphError},
    presentation::{compile_graph_diagnostics, write_human, write_json, write_short},
};

#[test]
fn projection_failures_retain_their_specific_compiler_cause() {
    use ash::{
        parser::{InternalReason, ProjectionError, ResourceFailure},
        source::SourceFile,
    };
    let mut cases = vec![
        (
            ProjectionError::RecoveryNodesPresent,
            "internal.projection.recovery-nodes",
            "recovery-nodes",
        ),
        (
            ProjectionError::ResourceLimit(ResourceFailure::StructuralDepth { limit: 128 }),
            "internal.resource.structural-depth",
            "",
        ),
        (
            ProjectionError::ResourceLimit(ResourceFailure::SyntaxWork { limit: 1234 }),
            "internal.resource.syntax-work",
            "",
        ),
    ];
    for (cause, name) in [
        (InternalReason::UnexpectedFinish, "unexpected-finish"),
        (InternalReason::UnclosedNode, "unclosed-node"),
        (InternalReason::InvalidRootCount, "invalid-root-count"),
        (InternalReason::TokenOutOfRange, "token-out-of-range"),
        (InternalReason::DuplicateToken, "duplicate-token"),
        (InternalReason::MissingToken, "missing-token"),
        (InternalReason::TokenOutOfOrder, "token-out-of-order"),
        (InternalReason::UnexpectedShape, "unexpected-shape"),
        (InternalReason::ForeignSpan, "foreign-span"),
        (InternalReason::InvalidSpan, "invalid-span"),
    ] {
        cases.push((
            ProjectionError::MalformedTree(cause),
            "internal.projection.malformed-tree",
            name,
        ));
    }
    for (error, reason, cause) in cases {
        let failure = GraphDiagnostic::from(LoadGraphError::Projection {
            source: SourceFile::new("source.ash", "").unwrap(),
            error,
            import_span: None,
        });
        let diagnostics = compile_graph_diagnostics(&failure).unwrap();
        let mut output = Vec::new();
        write_json(&mut output, &diagnostics[0]).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["responsibility"], "compiler");
        assert_eq!(json["reason"], reason);
        assert_eq!(json["labels"], serde_json::json!([]));
        match error {
            ProjectionError::ResourceLimit(
                ResourceFailure::StructuralDepth { limit } | ResourceFailure::SyntaxWork { limit },
            ) => assert_eq!(json["facts"][1]["value"], limit),
            _ => assert_eq!(json["facts"][1]["value"], cause),
        }
        for locale in [Locale::English, Locale::Bulgarian] {
            let mut output = Vec::new();
            write_short(
                &mut output,
                &diagnostics[0],
                &Catalogue::new(locale).unwrap(),
            )
            .unwrap();
            let text = String::from_utf8(output).unwrap();
            assert!(text.contains("source.ash"));
            if cause == "invalid-span" {
                assert!(text.contains(match locale {
                    Locale::English => "source spans or end-of-input markers are inconsistent",
                    Locale::Bulgarian => "диапазони или маркери за край на входа са несъгласувани",
                }));
            }
            if cause == "invalid-root-count" {
                assert!(text.contains(match locale {
                    Locale::English => "syntax events do not form one complete rooted tree",
                    Locale::Bulgarian =>
                        "синтактичните събития не образуват едно завършено дърво с корен",
                }));
            }
        }
    }
}

#[test]
fn graph_source_model_errors_preserve_causes_and_internal_quantities() {
    use ash::source::{ByteRange, SourceError, SourceFile};
    let first = SourceFile::new("first.ash", "").unwrap();
    let second = SourceFile::new("second.ash", "").unwrap();
    for (error, cause, responsibility) in [
        (
            SourceError::SourceIdExhausted,
            "source-id-exhausted",
            "compiler",
        ),
        (
            SourceError::DisplayPathTooLarge,
            "display-path-too-large",
            "input",
        ),
        (SourceError::TextTooLarge, "text-too-large", "input"),
        (SourceError::TooManyLines, "too-many-lines", "input"),
        (SourceError::LineTooLong, "line-too-long", "input"),
        (
            SourceError::RangeOutsideSource {
                range: ByteRange::new(3, 9).unwrap(),
                source_len: 4,
            },
            "range-outside-source",
            "compiler",
        ),
        (
            SourceError::ForeignSpan {
                expected: first.id(),
                found: second.id(),
            },
            "foreign-span",
            "compiler",
        ),
        (
            SourceError::OffsetOutsideSource {
                offset: u32::MAX,
                source_len: 4,
            },
            "offset-outside-source",
            "compiler",
        ),
        (
            SourceError::OffsetSplitsCodePoint { offset: 3 },
            "offset-splits-code-point",
            "compiler",
        ),
        (
            SourceError::InvalidLineState,
            "invalid-line-state",
            "compiler",
        ),
    ] {
        let failure = GraphDiagnostic::from(LoadGraphError::SourceModel {
            path: "source.ash".into(),
            error,
            operation: ash::source::SourceOperation::Admission,
            import_span: None,
        });
        let diagnostics = compile_graph_diagnostics(&failure).unwrap();
        for locale in [Locale::English, Locale::Bulgarian] {
            let mut output = Vec::new();
            write_short(
                &mut output,
                &diagnostics[0],
                &Catalogue::new(locale).unwrap(),
            )
            .unwrap();
            let output = String::from_utf8(output).unwrap();
            assert!(output.contains("source.ash"));
            if responsibility == "compiler" {
                assert!(output.contains("Ash"));
            }
        }
        let mut output = Vec::new();
        write_json(&mut output, &diagnostics[0]).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["reason"], "input.source-model");
        assert_eq!(json["responsibility"], responsibility);
        assert_eq!(json["labels"], serde_json::json!([]));
        assert_eq!(json["facts"][1]["value"], cause);
        let facts = json["facts"].as_array().unwrap();
        assert_eq!(
            facts[0],
            serde_json::json!({"name":"path", "kind":"path", "value":"source.ash"})
        );
        let expected_quantities = match cause {
            "range-outside-source" => vec![("start", 3), ("end", 9), ("source_len", 4)],
            "foreign-span" => vec![
                ("expected_source", first.id().value()),
                ("found_source", second.id().value()),
            ],
            "offset-outside-source" => vec![("offset", u32::MAX), ("source_len", 4)],
            "offset-splits-code-point" => vec![("offset", 3)],
            _ => Vec::new(),
        };
        assert_eq!(facts.len(), 3 + expected_quantities.len());
        assert_eq!(
            facts.last().unwrap(),
            &serde_json::json!({"name":"operation", "kind":"source-operation", "value":"admission"})
        );
        for (fact, (name, value)) in facts[2..].iter().zip(expected_quantities) {
            assert_eq!(
                *fact,
                serde_json::json!({"name":name, "kind":"integer", "value":value})
            );
        }
        if cause == "offset-outside-source" {
            assert_eq!(json["facts"][2]["value"], u32::MAX);
            assert_eq!(json["facts"][3]["value"], 4);
        }
    }
}

#[test]
fn an_unrepresentable_admitted_span_is_not_reported_as_oversized_input() {
    let failure = GraphDiagnostic::from(LoadGraphError::SourceModel {
        path: "source.ash".into(),
        error: ash::source::SourceError::TextTooLarge,
        operation: ash::source::SourceOperation::SpanConstruction,
        import_span: None,
    });
    let diagnostics = compile_graph_diagnostics(&failure).unwrap();
    let mut output = Vec::new();
    write_json(&mut output, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(json["responsibility"], "compiler");
    assert_eq!(
        json["facts"].as_array().unwrap().last().unwrap()["value"],
        "span-construction"
    );
    for (locale, expected) in [
        (
            Locale::English,
            "Ash encountered an unrepresentable source length or token offset while constructing a span for `source.ash`.",
        ),
        (
            Locale::Bulgarian,
            "Ash срещна непредставима дължина на изходен файл или отместване на токен при създаване на диапазон за `source.ash`.",
        ),
    ] {
        let mut output = Vec::new();
        write_short(
            &mut output,
            &diagnostics[0],
            &Catalogue::new(locale).unwrap(),
        )
        .unwrap();
        assert_eq!(
            String::from_utf8(output).unwrap(),
            format!("{expected} [input.source-model]\n")
        );
    }
}

#[test]
fn root_name_errors_are_invocation_diagnostics_with_localized_facts() {
    use ash::module::ModuleRoots;
    for (roots, reason, root, en, bg) in [
        (
            vec![("builtin", ".")],
            "invocation.reserved-root",
            "builtin",
            "The module root `builtin` is reserved by Ash.",
            "Коренът за модули `builtin` е запазен от Ash.",
        ),
        (
            vec![("std", "."), ("std", ".")],
            "invocation.duplicate-root",
            "std",
            "The module root `std` is configured more than once.",
            "Коренът за модули `std` е зададен повече от веднъж.",
        ),
        (
            vec![("Bad", ".")],
            "invocation.invalid-root-name",
            "Bad",
            "`Bad` is not a valid lowercase Ash identifier for a module root.",
            "`Bad` не е валиден идентификатор на Ash с малка начална буква за корен за модули.",
        ),
    ] {
        let failure =
            GraphDiagnostic::from(LoadGraphError::Module(ModuleRoots::new(roots).unwrap_err()));
        let diagnostics = compile_graph_diagnostics(&failure).unwrap();
        assert_eq!(diagnostics.len(), 1);
        for (locale, expected) in [(Locale::English, en), (Locale::Bulgarian, bg)] {
            let mut output = Vec::new();
            write_short(
                &mut output,
                &diagnostics[0],
                &Catalogue::new(locale).unwrap(),
            )
            .unwrap();
            assert_eq!(
                String::from_utf8(output).unwrap(),
                format!("{expected} [{reason}]\n")
            );
        }
        let mut output = Vec::new();
        write_json(&mut output, &diagnostics[0]).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["responsibility"], "invocation");
        assert_eq!(json["reason"], reason);
        assert_eq!(json["labels"], serde_json::json!([]));
        assert_eq!(
            json["facts"],
            serde_json::json!([{"name":"root", "kind":"identifier", "value":root}])
        );
    }
}

#[test]
fn unreadable_entry_has_input_responsibility_without_a_synthetic_location() {
    let failure = GraphDiagnostic::from(LoadGraphError::Read {
        path: "missing.ash".into(),
        kind: std::io::ErrorKind::NotFound,
        import_span: None,
    });
    let diagnostics = compile_graph_diagnostics(&failure).unwrap();
    assert_eq!(diagnostics.len(), 1);
    let diagnostic = &diagnostics[0];
    for (locale, explanation) in [
        (
            Locale::English,
            "Cannot read `missing.ash`: the file or directory does not exist.",
        ),
        (
            Locale::Bulgarian,
            "Не може да се прочете `missing.ash`: файлът или директорията не съществува.",
        ),
    ] {
        let catalogue = Catalogue::new(locale).unwrap();
        let mut output = Vec::new();
        write_human(&mut output, diagnostic, &catalogue).unwrap();
        assert_eq!(
            String::from_utf8(output).unwrap(),
            format!("{explanation}\nreason: input.read\n")
        );
        let mut output = Vec::new();
        write_short(&mut output, diagnostic, &catalogue).unwrap();
        assert_eq!(
            String::from_utf8(output).unwrap(),
            format!("{explanation} [input.read]\n")
        );
    }
    let mut output = Vec::new();
    write_json(&mut output, diagnostic).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(json["responsibility"], "input");
    assert_eq!(json["labels"], serde_json::json!([]));
    assert_eq!(
        json["facts"],
        serde_json::json!([
            {"name":"path", "kind":"path", "value":"missing.ash"},
            {"name":"io_kind", "kind":"io", "value":"not-found"}
        ])
    );
}

#[test]
fn invalid_utf8_has_a_distinct_explanation_and_reason() {
    let failure = GraphDiagnostic::from(LoadGraphError::InvalidUtf8 {
        path: "binary.ash".into(),
        import_span: None,
    });
    let diagnostics = compile_graph_diagnostics(&failure).unwrap();
    for (locale, explanation) in [
        (
            Locale::English,
            "`binary.ash` is not a valid UTF-8 source file.",
        ),
        (
            Locale::Bulgarian,
            "`binary.ash` не е валиден изходен файл в UTF-8.",
        ),
    ] {
        let mut output = Vec::new();
        write_short(
            &mut output,
            &diagnostics[0],
            &Catalogue::new(locale).unwrap(),
        )
        .unwrap();
        assert_eq!(
            String::from_utf8(output).unwrap(),
            format!("{explanation} [input.invalid-utf8]\n")
        );
    }
}
#[cfg(unix)]
#[test]
fn json_preserves_non_utf8_target_path_bytes() {
    use std::os::unix::ffi::OsStringExt;
    let bytes = b"bad-\xff.ash".to_vec();
    let failure = GraphDiagnostic::from(LoadGraphError::InvalidUtf8 {
        path: std::ffi::OsString::from_vec(bytes.clone()).into(),
        import_span: None,
    });
    let diagnostics = compile_graph_diagnostics(&failure).unwrap();
    let mut output = Vec::new();
    write_json(&mut output, &diagnostics[0]).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(json["facts"][0]["value"]["encoding"], "unix-bytes");
    assert_eq!(json["facts"][0]["value"]["units"], serde_json::json!(bytes));
    assert_eq!(json["facts"][0]["value"]["display"], "bad-\u{fffd}.ash");
}
#[test]
fn every_retained_io_category_has_a_precise_translation_and_machine_name() {
    use std::io::ErrorKind;
    let english = Catalogue::new(Locale::English).unwrap();
    let bulgarian = Catalogue::new(Locale::Bulgarian).unwrap();
    for (kind, code, en, bg) in [
        (
            ErrorKind::NotFound,
            "not-found",
            "the file or directory does not exist",
            "файлът или директорията не съществува",
        ),
        (
            ErrorKind::PermissionDenied,
            "permission-denied",
            "access is denied",
            "достъпът е отказан",
        ),
        (
            ErrorKind::ConnectionRefused,
            "connection-refused",
            "the connection was refused",
            "връзката е отказана",
        ),
        (
            ErrorKind::ConnectionReset,
            "connection-reset",
            "the connection was reset",
            "връзката е прекъсната принудително",
        ),
        (
            ErrorKind::HostUnreachable,
            "host-unreachable",
            "the host is unreachable",
            "хостът е недостъпен",
        ),
        (
            ErrorKind::NetworkUnreachable,
            "network-unreachable",
            "the network is unreachable",
            "мрежата е недостъпна",
        ),
        (
            ErrorKind::ConnectionAborted,
            "connection-aborted",
            "the connection was aborted",
            "връзката е прекратена",
        ),
        (
            ErrorKind::NotConnected,
            "not-connected",
            "the connection is not established",
            "връзката не е установена",
        ),
        (
            ErrorKind::AddrInUse,
            "addr-in-use",
            "the address is already in use",
            "адресът вече се използва",
        ),
        (
            ErrorKind::AddrNotAvailable,
            "addr-not-available",
            "the address is unavailable",
            "адресът е недостъпен",
        ),
        (
            ErrorKind::NetworkDown,
            "network-down",
            "the network is down",
            "мрежата не работи",
        ),
        (
            ErrorKind::BrokenPipe,
            "broken-pipe",
            "the pipe is closed",
            "каналът е затворен",
        ),
        (
            ErrorKind::AlreadyExists,
            "already-exists",
            "the target already exists",
            "целевият обект вече съществува",
        ),
        (
            ErrorKind::WouldBlock,
            "would-block",
            "the operation would block",
            "операцията би блокирала",
        ),
        (
            ErrorKind::NotADirectory,
            "not-a-directory",
            "a path component is not a directory",
            "компонент от пътя не е директория",
        ),
        (
            ErrorKind::IsADirectory,
            "is-a-directory",
            "the target is a directory",
            "целевият обект е директория",
        ),
        (
            ErrorKind::DirectoryNotEmpty,
            "directory-not-empty",
            "the directory is not empty",
            "директорията не е празна",
        ),
        (
            ErrorKind::ReadOnlyFilesystem,
            "read-only-filesystem",
            "the filesystem is read-only",
            "файловата система е само за четене",
        ),
        (
            ErrorKind::StaleNetworkFileHandle,
            "stale-network-file-handle",
            "the network file handle is stale",
            "дескрипторът на мрежовия файл вече е невалиден",
        ),
        (
            ErrorKind::InvalidInput,
            "invalid-input",
            "an input parameter is invalid",
            "входен параметър е невалиден",
        ),
        (
            ErrorKind::InvalidData,
            "invalid-data",
            "the operation encountered invalid data",
            "операцията срещна невалидни данни",
        ),
        (
            ErrorKind::TimedOut,
            "timed-out",
            "the operation timed out",
            "времето за изпълнение на операцията изтече",
        ),
        (
            ErrorKind::WriteZero,
            "write-zero",
            "the write operation made no progress",
            "операцията за запис не записа данни",
        ),
        (
            ErrorKind::StorageFull,
            "storage-full",
            "the storage is full",
            "хранилището е пълно",
        ),
        (
            ErrorKind::NotSeekable,
            "not-seekable",
            "the file does not support seeking",
            "файлът не поддържа позициониране",
        ),
        (
            ErrorKind::QuotaExceeded,
            "quota-exceeded",
            "a resource quota was exceeded",
            "квота за ресурс е превишена",
        ),
        (
            ErrorKind::FileTooLarge,
            "file-too-large",
            "the file exceeds a size limit",
            "файлът надвишава ограничение за размер",
        ),
        (
            ErrorKind::ResourceBusy,
            "resource-busy",
            "the resource is busy",
            "ресурсът е зает",
        ),
        (
            ErrorKind::ExecutableFileBusy,
            "executable-file-busy",
            "the executable file is busy",
            "изпълнимият файл е зает",
        ),
        (
            ErrorKind::Deadlock,
            "deadlock",
            "the operation would cause a deadlock",
            "операцията би причинила взаимно блокиране",
        ),
        (
            ErrorKind::CrossesDevices,
            "crosses-devices",
            "the operation crosses filesystem boundaries",
            "операцията пресича граници между файлови системи",
        ),
        (
            ErrorKind::TooManyLinks,
            "too-many-links",
            "the file has too many links",
            "файлът има твърде много връзки",
        ),
        (
            ErrorKind::InvalidFilename,
            "invalid-filename",
            "the file name is invalid or too long",
            "името на файла е невалидно или твърде дълго",
        ),
        (
            ErrorKind::ArgumentListTooLong,
            "argument-list-too-long",
            "the argument list is too long",
            "списъкът с аргументи е твърде дълъг",
        ),
        (
            ErrorKind::Interrupted,
            "interrupted",
            "the operation was interrupted",
            "операцията е прекъсната",
        ),
        (
            ErrorKind::Unsupported,
            "unsupported",
            "the operation is unsupported",
            "операцията не се поддържа",
        ),
        (
            ErrorKind::UnexpectedEof,
            "unexpected-eof",
            "the file ended unexpectedly",
            "файлът свърши неочаквано",
        ),
        (
            ErrorKind::OutOfMemory,
            "out-of-memory",
            "memory allocation failed",
            "заделянето на памет е неуспешно",
        ),
        (
            ErrorKind::Other,
            "other",
            "an uncategorized I/O error occurred",
            "възникна некатегоризирана входно-изходна грешка",
        ),
    ] {
        let failure = GraphDiagnostic::from(LoadGraphError::Read {
            path: "input.ash".into(),
            kind,
            import_span: None,
        });
        let diagnostics = compile_graph_diagnostics(&failure).unwrap();
        for (catalogue, prefix, explanation) in [
            (&english, "Cannot read", en),
            (&bulgarian, "Не може да се прочете", bg),
        ] {
            let mut output = Vec::new();
            write_short(&mut output, &diagnostics[0], catalogue).unwrap();
            assert_eq!(
                String::from_utf8(output).unwrap(),
                format!("{prefix} `input.ash`: {explanation}. [input.read]\n")
            );
        }
        let mut output = Vec::new();
        write_json(&mut output, &diagnostics[0]).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["facts"][1]["value"], code);
    }
}
#[test]
fn syntax_resource_failure_precedes_independent_source_diagnostics() {
    use ash::{
        lexer::lex, module::ModuleSyntaxFailure, parser::ResourceFailure, source::SourceFile,
    };
    for resource in [
        ResourceFailure::StructuralDepth { limit: 128 },
        ResourceFailure::SyntaxWork { limit: 1_500_000 },
        ResourceFailure::SyntaxWork { limit: usize::MAX },
    ] {
        let source = SourceFile::new("large.ash", "#").unwrap();
        let lexical = lex(&source).unwrap().diagnostics;
        let failure =
            GraphDiagnostic::from(LoadGraphError::Syntax(Box::new(ModuleSyntaxFailure {
                source,
                import_span: None,
                lexical,
                parser: Vec::new(),
                resource: Some(resource),
            })));
        let diagnostics = compile_graph_diagnostics(&failure).unwrap();
        assert_eq!(diagnostics.len(), 2);
        let mut output = Vec::new();
        write_json(&mut output, &diagnostics[0]).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["reason"], resource.reason_code());
        assert_eq!(json["responsibility"], "compiler");
        let limit = match resource {
            ResourceFailure::StructuralDepth { limit } | ResourceFailure::SyntaxWork { limit } => {
                limit
            }
        };
        assert_eq!(
            json["facts"][0],
            serde_json::json!({"name":"limit", "kind":"integer", "value":limit})
        );
        let mut output = Vec::new();
        write_json(&mut output, &diagnostics[1]).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["reason"], "lex.unknown-character");
        for locale in [Locale::English, Locale::Bulgarian] {
            let mut output = Vec::new();
            write_short(
                &mut output,
                &diagnostics[0],
                &Catalogue::new(locale).unwrap(),
            )
            .unwrap();
            let output = String::from_utf8(output).unwrap();
            assert!(output.contains("large.ash"));
            assert!(output.contains(&limit.to_string()));
        }
    }
}
