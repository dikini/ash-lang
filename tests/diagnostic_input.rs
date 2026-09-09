use ash::{
    message::{Catalogue, Locale},
    module::{GraphDiagnostic, LoadGraphError},
    presentation::{compile_graph_diagnostics, write_human, write_json, write_short},
};

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
