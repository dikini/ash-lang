//! Borrowed compile-time presentation. Runtime reporting is a separate path.

use std::{
    io::{self, Write},
    path::Path,
};

use crate::{
    diagnostic::{Diagnostic, compare_source_spans},
    elaborate::TypeReason,
    lexer::LexReason,
    message::{Catalogue, CatalogueError, Message},
    module::{GraphDiagnostic, LoadGraphError, ModuleSyntaxFailure, io_kind_name},
    parser::{FoundToken, ParseContext, ParseDiagnostic, ResourceFailure, SynchronizationBoundary},
    source::{SourceFile, Span},
};

/// A missing fact or unsupported adapter in the staged compile-time migration.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PresentationError {
    /// This diagnostic family has not yet been migrated.
    Unsupported,
    /// The phase did not retain a required causal fact.
    MissingFact,
    /// A causal span has no admitted source context.
    MissingSource,
}

/// A causal label resolved against an admitted source.
pub struct Label<'a> {
    source: &'a SourceFile,
    span: Span,
    message: Message<'a>,
    relationship: &'static str,
    facts: Vec<Fact<'a>>,
}

#[derive(Clone, Copy)]
struct Fact<'a> {
    name: &'static str,
    kind: &'static str,
    value: FactValue<'a>,
}

#[derive(Clone, Copy)]
enum FactValue<'a> {
    Text(&'a str),
    Path(&'a Path),
    Integer(usize),
}

impl serde::Serialize for FactValue<'_> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Text(value) => value.serialize(serializer),
            Self::Integer(value) => value.serialize(serializer),
            Self::Path(path) => {
                if let Some(text) = path.to_str() {
                    return text.serialize(serializer);
                }
                // A lossy display is not the native path. Preserve exact units as well.
                #[cfg(unix)]
                {
                    use std::os::unix::ffi::OsStrExt;
                    serde_json::json!({"display": path.to_string_lossy(), "encoding": "unix-bytes", "units": path.as_os_str().as_bytes()}).serialize(serializer)
                }
                #[cfg(windows)]
                {
                    use std::os::windows::ffi::OsStrExt;
                    serde_json::json!({"display": path.to_string_lossy(), "encoding": "windows-wide", "units": path.as_os_str().encode_wide().collect::<Vec<_>>()}).serialize(serializer)
                }
                #[cfg(not(any(unix, windows)))]
                {
                    serde_json::json!({"display": path.to_string_lossy(), "encoding": "os-encoded-bytes", "platform": std::env::consts::OS, "units": path.as_os_str().as_encoded_bytes()}).serialize(serializer)
                }
            }
        }
    }
}

/// A compile-time view borrowing its phase diagnostic and source context.
pub struct CompileDiagnostic<'a> {
    reason: String,
    responsibility: &'static str,
    message: Message<'a>,
    primary: Option<Label<'a>>,
    related: Vec<Label<'a>>,
    facts: Vec<Fact<'a>>,
}

/// Exposes retained type-error facts without inspecting diagnostic prose.
///
/// # Errors
/// Returns an unsupported family or a missing causal fact/source. This staged
/// adapter is not yet selected by the executable's default renderer.
pub fn compile_type_diagnostic<'a>(
    diagnostic: &'a Diagnostic<TypeReason>,
    sources: &[&'a SourceFile],
) -> Result<CompileDiagnostic<'a>, PresentationError> {
    if diagnostic.reason != TypeReason::BindingInitializer {
        return Err(PresentationError::Unsupported);
    }
    let expected = diagnostic
        .expected
        .as_deref()
        .ok_or(PresentationError::MissingFact)?;
    let found = diagnostic
        .found
        .as_deref()
        .ok_or(PresentationError::MissingFact)?;
    let [annotation] = diagnostic.related.as_slice() else {
        return Err(PresentationError::MissingFact);
    };
    // Machine fact names belong to the semantic adapter, not the catalogue.
    // Both representations borrow the phase's original values.
    let expected_fact = Fact {
        name: "expected",
        kind: "code",
        value: FactValue::Text(expected),
    };
    let found_fact = Fact {
        name: "found",
        kind: "code",
        value: FactValue::Text(found),
    };
    let label = |span: Span, message, relationship, fact| {
        let source = sources
            .iter()
            .copied()
            .find(|source| source.id() == span.source())
            .ok_or(PresentationError::MissingSource)?;
        source
            .location(span)
            .map_err(|_| PresentationError::MissingSource)?;
        Ok(Label {
            source,
            span,
            message,
            relationship,
            facts: vec![fact],
        })
    };
    Ok(CompileDiagnostic {
        reason: diagnostic.reason.to_string(),
        responsibility: "source",
        message: Message::binding_initializer(expected, found),
        primary: Some(label(
            diagnostic.primary.span(),
            Message::initializer(found),
            "initializer",
            found_fact,
        )?),
        related: vec![label(
            annotation.span(),
            Message::binding_annotation(expected),
            "binding_annotation",
            expected_fact,
        )?],
        facts: vec![expected_fact, found_fact],
    })
}

/// Exposes lexical facts without translating legacy expected/found descriptions.
///
/// # Errors
/// Returns a missing offending-text fact or admitted source context.
pub fn compile_lex_diagnostic<'a>(
    diagnostic: &'a Diagnostic<LexReason>,
    sources: &[&'a SourceFile],
) -> Result<CompileDiagnostic<'a>, PresentationError> {
    let found = diagnostic
        .found
        .as_deref()
        .ok_or(PresentationError::MissingFact)?;
    let span = diagnostic.primary.span();
    let source = sources
        .iter()
        .copied()
        .find(|source| source.id() == span.source())
        .ok_or(PresentationError::MissingSource)?;
    source
        .location(span)
        .map_err(|_| PresentationError::MissingSource)?;
    let fact = Fact {
        name: "found",
        kind: "code",
        value: FactValue::Text(found),
    };
    Ok(CompileDiagnostic {
        reason: diagnostic.reason.to_string(),
        responsibility: "source",
        message: diagnostic.reason.message(),
        primary: Some(Label {
            source,
            span,
            message: diagnostic.reason.message(),
            relationship: "invalid_token",
            facts: vec![fact],
        }),
        related: Vec::new(),
        facts: vec![fact],
    })
}

/// Exposes retained grammar and recovery facts without interpreting legacy prose.
///
/// # Errors
/// Returns a missing grammar fact or admitted source context.
pub fn compile_parse_diagnostic<'a>(
    diagnostic: &'a ParseDiagnostic,
    sources: &[&'a SourceFile],
) -> Result<CompileDiagnostic<'a>, PresentationError> {
    let message = diagnostic.message().ok_or(PresentationError::MissingFact)?;
    let mut facts = Vec::new();
    if let Some(expected) = diagnostic.expected_form() {
        facts.push(Fact {
            name: "expected",
            kind: "syntax",
            value: FactValue::Text(expected.diagnostic_name()),
        });
    }
    if let Some(found) = diagnostic.found_token() {
        facts.push(Fact {
            name: "found",
            kind: if matches!(found, FoundToken::Spelling(_)) {
                "code"
            } else {
                "syntax"
            },
            value: FactValue::Text(found.diagnostic_name()),
        });
    }
    let label = |span: Span, message, relationship, facts| {
        let source = sources
            .iter()
            .copied()
            .find(|source| source.id() == span.source())
            .ok_or(PresentationError::MissingSource)?;
        source
            .location(span)
            .map_err(|_| PresentationError::MissingSource)?;
        Ok(Label {
            source,
            span,
            message,
            relationship,
            facts,
        })
    };
    let primary = label(
        diagnostic.primary.span(),
        message.clone(),
        diagnostic.primary_relationship(),
        Vec::new(),
    )?;
    let mut related = Vec::new();
    if let Some(span) = diagnostic.recovery_position() {
        related.push(label(
            span,
            diagnostic
                .found_token()
                .map_or_else(Message::parse_recovery, Message::parse_found),
            "recovery_position",
            Vec::new(),
        )?);
    }
    for &ParseContext::Synchronization { boundary, span } in &diagnostic.context {
        let message = if boundary == SynchronizationBoundary::EndOfFile {
            Message::parse_found(FoundToken::EndOfFile)
        } else {
            Message::parse_synchronization()
        };
        related.push(label(
            span,
            message,
            "synchronization",
            vec![Fact {
                name: "boundary",
                kind: "syntax",
                value: FactValue::Text(boundary.diagnostic_name()),
            }],
        )?);
    }
    Ok(CompileDiagnostic {
        reason: diagnostic.reason.to_string(),
        responsibility: "source",
        message,
        primary: Some(primary),
        related,
        facts,
    })
}

/// Exposes input and graph failure facts. Syntax collections keep their causal order.
///
/// # Errors
/// Returns an unsupported staged family or missing admitted source context.
pub fn compile_graph_diagnostics(
    context: &GraphDiagnostic,
) -> Result<Vec<CompileDiagnostic<'_>>, PresentationError> {
    let failure = context.failure();
    if let LoadGraphError::Module(failure) = failure {
        let message = failure.message().ok_or(PresentationError::Unsupported)?;
        let mut facts = Vec::new();
        if let Some(root) = failure.root() {
            facts.push(Fact {
                name: "root",
                kind: "identifier",
                value: FactValue::Text(root),
            });
        }
        if let Some(path) = failure.path() {
            facts.push(Fact {
                name: "path",
                kind: "path",
                value: FactValue::Path(path),
            });
        }
        return Ok(vec![CompileDiagnostic {
            reason: failure.reason().to_string(),
            responsibility: if failure.is_source_rejection() {
                "source"
            } else {
                "invocation"
            },
            message,
            primary: import_label(context, "import_target")?,
            related: Vec::new(),
            facts,
        }]);
    }
    if let LoadGraphError::Syntax(failure) = failure {
        return compile_graph_syntax(context, failure);
    }
    let (reason, message, path, kind) = match failure {
        LoadGraphError::Read { path, kind, .. } => (
            "input.read",
            Message::input_read(path, *kind),
            path,
            Some(*kind),
        ),
        LoadGraphError::InvalidUtf8 { path, .. } => (
            "input.invalid-utf8",
            Message::input_invalid_utf8(path),
            path,
            None,
        ),
        _ => return Err(PresentationError::Unsupported),
    };
    let mut facts = vec![Fact {
        name: "path",
        kind: "path",
        value: FactValue::Path(path),
    }];
    if let Some(kind) = kind {
        facts.push(Fact {
            name: "io_kind",
            kind: "io",
            value: FactValue::Text(io_kind_name(kind)),
        });
    }
    let primary = import_label(context, "import_target")?;
    Ok(vec![CompileDiagnostic {
        reason: reason.into(),
        responsibility: "input",
        message,
        primary,
        related: Vec::new(),
        facts,
    }])
}

fn import_label<'a>(
    context: &'a GraphDiagnostic,
    relationship: &'static str,
) -> Result<Option<Label<'a>>, PresentationError> {
    context
        .failure()
        .import_span()
        .map(|span| {
            let source = context
                .sources()
                .find(|source| source.id() == span.source())
                .ok_or(PresentationError::MissingSource)?;
            source
                .location(span)
                .map_err(|_| PresentationError::MissingSource)?;
            Ok(Label {
                source,
                span,
                message: Message::import_target(),
                relationship,
                facts: Vec::new(),
            })
        })
        .transpose()
}

fn compile_graph_syntax<'a>(
    context: &'a GraphDiagnostic,
    failure: &'a ModuleSyntaxFailure,
) -> Result<Vec<CompileDiagnostic<'a>>, PresentationError> {
    let sources: Vec<_> = context.sources().collect();
    let mut diagnostics = Vec::new();
    if let Some(resource) = failure.resource {
        let path = failure.source.display_path();
        let (limit, message) = match resource {
            ResourceFailure::StructuralDepth { limit } => {
                (limit, Message::syntax_depth(path, limit))
            }
            ResourceFailure::SyntaxWork { limit } => (limit, Message::syntax_work(path, limit)),
        };
        diagnostics.push(CompileDiagnostic {
            reason: resource.reason_code().into(),
            responsibility: "compiler",
            message,
            primary: None,
            related: Vec::new(),
            facts: vec![
                Fact {
                    name: "limit",
                    kind: "integer",
                    value: FactValue::Integer(limit),
                },
                Fact {
                    name: "source_path",
                    kind: "path-display",
                    value: FactValue::Text(path),
                },
            ],
        });
    }
    // Merge the retained streams exactly as the established syntax reporter does.
    // Do not globally sort: parser insertion order also carries recovery causality.
    let mut lexical = failure.lexical.iter().peekable();
    let mut parser = failure.parser.iter().peekable();
    while lexical.peek().is_some() || parser.peek().is_some() {
        let take_parser = match (lexical.peek(), parser.peek()) {
            (Some(lexical), Some(parser)) => {
                compare_source_spans(parser.primary.span(), lexical.primary.span()).is_lt()
            }
            (None, Some(_)) => true,
            _ => false,
        };
        diagnostics.push(if take_parser {
            compile_parse_diagnostic(parser.next().expect("observed parser diagnostic"), &sources)?
        } else {
            compile_lex_diagnostic(
                lexical.next().expect("observed lexical diagnostic"),
                &sources,
            )?
        });
    }
    if diagnostics.is_empty() {
        return Err(PresentationError::MissingFact);
    }
    for diagnostic in &mut diagnostics {
        if let Some(import) = import_label(context, "import_context")? {
            diagnostic.related.push(import);
        }
    }
    Ok(diagnostics)
}

/// A renderer failure, distinct from the diagnostic being presented.
#[derive(Debug)]
pub enum RenderError {
    /// The output channel failed.
    Write(io::Error),
    /// The embedded message contract failed.
    Catalogue(CatalogueError),
    /// JSON serialization or its writer failed.
    Json(serde_json::Error),
}

impl From<io::Error> for RenderError {
    fn from(error: io::Error) -> Self {
        Self::Write(error)
    }
}

impl From<CatalogueError> for RenderError {
    fn from(error: CatalogueError) -> Self {
        Self::Catalogue(error)
    }
}

/// Writes one source-aware human diagnostic.
///
/// # Errors
/// Returns a catalogue or output failure without retrying the diagnostic.
pub fn write_human(
    writer: &mut impl Write,
    diagnostic: &CompileDiagnostic<'_>,
    catalogue: &Catalogue,
) -> Result<(), RenderError> {
    writeln!(writer, "{}", catalogue.format(&diagnostic.message)?)?;
    for label in diagnostic.primary.iter().chain(&diagnostic.related) {
        // Sources and spans were checked by the adapter above.
        let location = label
            .source
            .location(label.span)
            .expect("validated diagnostic span");
        let line = location.start().line();
        let column = location.start().column();
        writeln!(
            writer,
            "  --> {}:{line}:{column}",
            label.source.display_path()
        )?;
        let excerpt = label
            .source
            .text()
            .lines()
            .nth((line - 1) as usize)
            .unwrap_or("");
        writeln!(writer, "{line} | {excerpt}")?;
        writeln!(
            writer,
            "  | {}^ {}",
            " ".repeat((column - 1) as usize),
            catalogue.format(&label.message)?
        )?;
    }
    writeln!(writer, "reason: {}", diagnostic.reason)?;
    Ok(())
}

/// Writes one compact localized diagnostic.
///
/// # Errors
/// Returns a catalogue or output failure without retrying the diagnostic.
pub fn write_short(
    writer: &mut impl Write,
    diagnostic: &CompileDiagnostic<'_>,
    catalogue: &Catalogue,
) -> Result<(), RenderError> {
    if let Some(label) = &diagnostic.primary {
        let location = label
            .source
            .location(label.span)
            .expect("validated diagnostic span");
        write!(
            writer,
            "{}:{}:{}: ",
            label.source.display_path(),
            location.start().line(),
            location.start().column()
        )?;
    }
    writeln!(
        writer,
        "{} [{}]",
        catalogue.format(&diagnostic.message)?,
        diagnostic.reason
    )?;
    Ok(())
}

#[derive(serde::Serialize)]
struct JsonFact<'a> {
    name: &'static str,
    kind: &'static str,
    value: FactValue<'a>,
}

fn facts<'a>(source: &[Fact<'a>]) -> Vec<JsonFact<'a>> {
    source
        .iter()
        .map(|fact| JsonFact {
            name: fact.name,
            kind: fact.kind,
            value: fact.value,
        })
        .collect()
}

#[derive(serde::Serialize)]
struct JsonLabel<'a> {
    role: &'static str,
    relationship: &'static str,
    path: &'a str,
    byte_start: u32,
    byte_end: u32,
    facts: Vec<JsonFact<'a>>,
}

#[derive(serde::Serialize)]
struct JsonDiagnostic<'a> {
    schema_version: u8,
    reason: String,
    responsibility: &'static str,
    facts: Vec<JsonFact<'a>>,
    labels: Vec<JsonLabel<'a>>,
}

/// Writes one locale-independent compile-time JSON diagnostic and newline.
///
/// # Errors
/// Returns serialization or output failure; this allocating DTO path is not
/// suitable for reporting runtime resource failures.
pub fn write_json(
    writer: &mut impl Write,
    diagnostic: &CompileDiagnostic<'_>,
) -> Result<(), RenderError> {
    let labels = diagnostic
        .primary
        .iter()
        .map(|label| ("primary", label))
        .chain(diagnostic.related.iter().map(|label| ("related", label)))
        .map(|(role, label)| JsonLabel {
            role,
            relationship: label.relationship,
            path: label.source.display_path(),
            byte_start: label.span.range().start(),
            byte_end: label.span.range().end(),
            facts: facts(&label.facts),
        })
        .collect();
    let data = JsonDiagnostic {
        schema_version: 1,
        reason: diagnostic.reason.to_string(),
        responsibility: diagnostic.responsibility,
        facts: facts(&diagnostic.facts),
        labels,
    };
    serde_json::to_writer(&mut *writer, &data).map_err(RenderError::Json)?;
    writer.write_all(b"\n")?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{diagnostic::SourceLabel, source::ByteRange};

    #[test]
    fn changing_presentation_messages_cannot_change_json_facts() {
        let source = SourceFile::new("test.ash", "Bool 1").unwrap();
        let mut diagnostic = Diagnostic::new(
            TypeReason::BindingInitializer,
            SourceLabel::new(
                source.span(ByteRange::new(5, 6).unwrap()).unwrap(),
                "ignored",
            ),
        );
        diagnostic.related.push(SourceLabel::new(
            source.span(ByteRange::new(0, 4).unwrap()).unwrap(),
            "ignored",
        ));
        diagnostic.expected = Some("Bool".into());
        diagnostic.found = Some("Int".into());
        let mut view = compile_type_diagnostic(&diagnostic, &[&source]).unwrap();
        let mut before = Vec::new();
        write_json(&mut before, &view).unwrap();
        view.message = Message::initializer("presentation-only");
        view.primary.as_mut().unwrap().message = Message::binding_annotation("presentation-only");
        let mut after = Vec::new();
        write_json(&mut after, &view).unwrap();
        assert_eq!(before, after);
    }
}
