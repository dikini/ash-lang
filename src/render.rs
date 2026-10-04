//! Stable plain-text rendering at the executable boundary.

use std::fmt::Write;

mod runtime;
pub use runtime::{
    PreparedRuntimeMessages, write_runtime_diagnostic, write_runtime_human, write_runtime_short,
};

use crate::{
    diagnostic::{Diagnostic, compare_source_spans},
    driver::{FileFailure, Observation, PipelineFailure, SyntaxFailure},
    elaborate::TypeError,
    eval::{ResourceFailure as RuntimeResourceFailure, RuntimeFailureReport},
    lexer::LexReason,
    module::{LoadGraphError, ModuleFailure, ModuleReason, ModuleResource},
    parser::{InternalReason, ParseDiagnostic, ProjectionError, ResourceFailure},
    source::Span,
};

/// Writes a bounded runtime report without constructing a rich message.
///
/// The supplied writer owns its own storage policy. The reporter uses only
/// static fragments and a stack decimal buffer, and stops on any writer error.
///
/// # Errors
/// Returns the first write or flush failure without retrying it.
pub fn write_runtime_report(
    writer: &mut impl std::io::Write,
    report: &RuntimeFailureReport,
) -> std::io::Result<()> {
    fragment(writer, report.primary.reason_code().as_bytes())?;
    fragment(writer, b"\n")?;
    if let Some(failure) = report.primary.resource() {
        if report.primary.reason_code() != failure.cause.reason_code() {
            fragment(writer, b"cause: ")?;
            fragment(writer, failure.cause.reason_code().as_bytes())?;
            fragment(writer, b"\n")?;
        }
        resource_details(writer, failure)?;
    }
    if let Some(failure) = report.teardown {
        fragment(writer, b"teardown: ")?;
        fragment(writer, failure.cause.reason_code().as_bytes())?;
        fragment(writer, b"\n")?;
        resource_details(writer, failure)?;
    }
    fragment(writer, b"cleanup: ")?;
    fragment(writer, report.cleanup.label().as_bytes())?;
    fragment(writer, b"\n")?;
    writer.flush()
}

/// Writes one locale-independent JSON v1 runtime diagnostic.
///
/// This path reads only the existing fixed-size failure data. It constructs no
/// owned JSON tree, allocates no storage and invokes no catalogue formatter.
/// The writer supplies its own storage policy. Unknown amounts are omitted;
/// teardown facts remain distinct from the original failure.
///
/// # Errors
/// Stops at the first write or flush failure, including `Interrupted`, without
/// retrying or attempting to report the reporting failure.
pub fn write_runtime_json(
    writer: &mut impl std::io::Write,
    failure: crate::eval::RuntimeFailure,
) -> std::io::Result<()> {
    use crate::eval::{CleanupStatus, RuntimeFailure};
    fragment(writer, b"{\"schema_version\":1,\"reason\":")?;
    runtime_json_string(writer, failure.reason_code())?;
    fragment(
        writer,
        b",\"responsibility\":\"runtime\",\"labels\":[],\"facts\":[",
    )?;
    let cleanup = match failure {
        RuntimeFailure::Report(report) => report.cleanup,
        _ => CleanupStatus::Unknown,
    };
    fragment(
        writer,
        b"{\"name\":\"cleanup\",\"kind\":\"cleanup-status\",\"value\":",
    )?;
    runtime_json_string(writer, cleanup.label())?;
    fragment(writer, b"}")?;
    if let RuntimeFailure::Report(report) = failure {
        if let Some(resource) = report.primary.resource() {
            runtime_json_resource(writer, resource, "")?;
        }
        if let Some(resource) = report.teardown {
            runtime_json_resource(writer, resource, "teardown_")?;
        }
    }
    fragment(writer, b"]}\n")?;
    writer.flush()
}

fn runtime_json_resource(
    writer: &mut impl std::io::Write,
    failure: RuntimeResourceFailure,
    prefix: &'static str,
) -> std::io::Result<()> {
    for (name, kind, value) in [
        ("cause", "reason", failure.cause.reason_code()),
        ("phase", "runtime-phase", failure.phase.label()),
        ("resource", "runtime-resource", failure.resource.label()),
    ] {
        runtime_json_fact_start(writer, prefix, name, kind)?;
        runtime_json_string(writer, value)?;
        fragment(writer, b"}")?;
    }
    if failure.cause == crate::eval::ResourceFailureCause::StorageReservationFailed {
        runtime_json_fact_start(writer, prefix, "underlying_cause", "resource-cause")?;
        runtime_json_string(writer, "undetermined")?;
        fragment(writer, b"}")?;
    }
    for (name, amount) in [
        ("requested", failure.requested),
        ("available", failure.available),
    ] {
        if let Some(amount) = amount {
            runtime_json_fact_start(writer, prefix, name, "integer")?;
            decimal(writer, amount)?;
            fragment(writer, b"}")?;
        }
    }
    Ok(())
}

fn runtime_json_fact_start(
    writer: &mut impl std::io::Write,
    prefix: &'static str,
    name: &'static str,
    kind: &'static str,
) -> std::io::Result<()> {
    // Prefixes and names are private fixed ASCII identifiers, not user text.
    fragment(writer, b",{\"name\":\"")?;
    fragment(writer, prefix.as_bytes())?;
    fragment(writer, name.as_bytes())?;
    fragment(writer, b"\",\"kind\":")?;
    runtime_json_string(writer, kind)?;
    fragment(writer, b",\"value\":")
}

fn runtime_json_string(writer: &mut impl std::io::Write, value: &str) -> std::io::Result<()> {
    fragment(writer, b"\"")?;
    let bytes = value.as_bytes();
    let mut start = 0;
    for (index, &byte) in bytes.iter().enumerate() {
        if byte < 0x20 || byte == b'"' || byte == b'\\' {
            fragment(writer, &bytes[start..index])?;
            if byte < 0x20 {
                const HEX: &[u8; 16] = b"0123456789abcdef";
                fragment(
                    writer,
                    &[
                        b'\\',
                        b'u',
                        b'0',
                        b'0',
                        HEX[(byte >> 4) as usize],
                        HEX[(byte & 15) as usize],
                    ],
                )?;
            } else {
                fragment(writer, &[b'\\', byte])?;
            }
            start = index + 1;
        }
    }
    fragment(writer, &bytes[start..])?;
    fragment(writer, b"\"")
}

fn decimal(writer: &mut impl std::io::Write, mut amount: usize) -> std::io::Result<()> {
    let mut digits = [0; usize::BITS as usize];
    let mut start = digits.len();
    loop {
        start -= 1;
        digits[start] = b'0' + (amount % 10) as u8;
        amount /= 10;
        if amount == 0 {
            break;
        }
    }
    fragment(writer, &digits[start..])
}

fn resource_details(
    writer: &mut impl std::io::Write,
    failure: RuntimeResourceFailure,
) -> std::io::Result<()> {
    fragment(writer, b"phase: ")?;
    fragment(writer, failure.phase.label().as_bytes())?;
    fragment(writer, b"\n")?;
    fragment(writer, b"resource: ")?;
    fragment(writer, failure.resource.label().as_bytes())?;
    fragment(writer, b"\n")?;
    if failure.cause == crate::eval::ResourceFailureCause::StorageReservationFailed {
        fragment(writer, b"underlying cause: undetermined\n")?;
    }
    for (label, amount) in [
        (b"requested: ".as_slice(), failure.requested),
        (b"available: ".as_slice(), failure.available),
    ] {
        if let Some(amount) = amount {
            fragment(writer, label)?;
            decimal(writer, amount)?;
            fragment(writer, b"\n")?;
        }
    }
    Ok(())
}

/// Gives formatting and serialization the same no-retry write policy as runtime reporting.
pub(crate) struct DiagnosticWriter<'a, W>(pub(crate) &'a mut W);

impl<W: std::io::Write> std::io::Write for DiagnosticWriter<'_, W> {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        self.0.write(bytes)
    }

    fn write_all(&mut self, bytes: &[u8]) -> std::io::Result<()> {
        fragment(self.0, bytes)
    }

    fn flush(&mut self) -> std::io::Result<()> {
        self.0.flush()
    }
}

fn fragment(writer: &mut impl std::io::Write, mut bytes: &[u8]) -> std::io::Result<()> {
    // Unlike write_all, this does not retry Interrupted. Every successful
    // iteration consumes at least one byte of the fixed-size report.
    while !bytes.is_empty() {
        let count = writer.write(bytes)?;
        if count == 0 || count > bytes.len() {
            return Err(std::io::ErrorKind::WriteZero.into());
        }
        bytes = &bytes[count..];
    }
    Ok(())
}

/// Renders one successful observation with its required trailing newline.
#[must_use]
pub fn observation(observation: &Observation) -> String {
    format!(
        "{} : {}\n",
        observation.value_display(),
        observation.type_display()
    )
}

/// Renders one file or pipeline failure with its required trailing newline.
#[must_use]
pub fn file_failure(failure: &FileFailure) -> String {
    let mut output = match failure {
        FileFailure::Graph(error) => graph_failure(error.failure()),
        FileFailure::Read { path, kind } => {
            format!("input.read\n{}: {kind}", path.display())
        }
        FileFailure::InvalidUtf8 { path } => {
            format!("input.invalid-utf8\n{} is not UTF-8", path.display())
        }
        FileFailure::Source(error) => format!("input.source-model\n{error}"),
        FileFailure::Pipeline(context) => pipeline_failure(context.failure()),
    };
    output.push('\n');
    output
}

/// Renders one stage-preserving pipeline failure without a trailing newline.
#[must_use]
pub fn pipeline_failure(failure: &PipelineFailure) -> String {
    match failure {
        PipelineFailure::SourceModel(error) => format!("internal.source-model\n{error}"),
        PipelineFailure::Syntax(failure) => syntax_failure(failure),
        PipelineFailure::Projection(error) => projection_failure(*error),
        PipelineFailure::Resolution(error) => error.to_string(),
        PipelineFailure::Kind(crate::kind::KindFailure::Source(error)) => error.to_string(),
        PipelineFailure::Kind(error) => format!("{}\n{error}", error.reason_code()),
        PipelineFailure::Typing(error @ (TypeError::Source(_) | TypeError::Interface(_))) => {
            error.to_string()
        }
        PipelineFailure::Typing(error @ TypeError::Mismatch(_)) => {
            format!("type.mismatch\n{error}")
        }
        PipelineFailure::Typing(error @ TypeError::Internal(failure)) => {
            format!("{}\n{error}", failure.reason_code())
        }
        PipelineFailure::Entry(error) => error.diagnostic.render_plain(),
        PipelineFailure::EvidenceValidation(error) => {
            format!("{}\n{:?}", error.reason(), error.primary())
        }
        PipelineFailure::Validation(error) => match error.node() {
            Some(node) => format!("{}\nnode: {}", error.reason(), node.value()),
            None => error.reason().to_string(),
        },
        PipelineFailure::Runtime(error) => format!("{}\n{error}", error.reason_code()),
    }
}

fn graph_failure(error: &LoadGraphError) -> String {
    match error {
        LoadGraphError::Module(failure) => module_failure(failure),
        LoadGraphError::Read {
            path,
            kind,
            import_span,
        } => {
            let mut output = String::from("input.read");
            append_optional_import_primary(
                &mut output,
                *import_span,
                "this import selected the unreadable source",
            );
            append_detail(&mut output, "path", &path.display().to_string());
            append_detail(&mut output, "io", &format!("{kind:?}"));
            output
        }
        LoadGraphError::InvalidUtf8 { path, import_span } => {
            let mut output = String::from("input.invalid-utf8");
            append_optional_import_primary(
                &mut output,
                *import_span,
                "this import selected the invalid UTF-8 source",
            );
            append_detail(&mut output, "path", &path.display().to_string());
            output
        }
        LoadGraphError::SourceModel {
            path,
            error,
            import_span,
            ..
        } => {
            let mut output = String::from("input.source-model");
            append_optional_import_primary(
                &mut output,
                *import_span,
                "this import selected the source that could not be represented",
            );
            append_detail(&mut output, "path", &path.display().to_string());
            append_detail(&mut output, "detail", &error.to_string());
            output
        }
        LoadGraphError::Syntax(failure) => {
            let mut output =
                syntax_failure_parts(&failure.lexical, &failure.parser, failure.resource);
            append_detail(&mut output, "path", failure.source.display_path());
            output
        }
        LoadGraphError::Projection { source, error, .. } => {
            let mut output = projection_failure(*error);
            append_detail(&mut output, "path", source.display_path());
            output
        }
    }
}

fn module_failure(failure: &ModuleFailure) -> String {
    let mut output = failure.reason().to_string();
    append_optional_import_primary(
        &mut output,
        failure.primary_span(),
        module_primary_message(failure.reason()),
    );
    if let Some(path) = failure.path() {
        append_detail(&mut output, "path", &path.display().to_string());
    }
    if let Some(root) = failure.root() {
        append_detail(&mut output, "root", root);
    }
    if let Some(kind) = failure.io_kind() {
        append_detail(&mut output, "io", &format!("{kind:?}"));
    }
    if let Some(resource) = failure.resource_kind() {
        append_detail(&mut output, "resource", module_resource(resource));
    }
    output
}

const fn module_primary_message(reason: ModuleReason) -> &'static str {
    match reason {
        ModuleReason::UnknownBuiltin => "this import names no compiler-owned module",
        ModuleReason::UnknownForeign => "this import names no registered foreign module",
        ModuleReason::ReservedRoot => "the builtin module root is reserved",
        ModuleReason::UnknownRoot => "this import names an unknown module root",
        ModuleReason::NotFound => "this import target does not exist",
        ModuleReason::PathEscape => "this import target escapes its module root",
        ModuleReason::ImportCycle => "this import closes a dependency cycle",
        ModuleReason::InvalidPath => "this import path is invalid",
        ModuleReason::DuplicateRoot
        | ModuleReason::InvalidRootName
        | ModuleReason::RootUnavailable
        | ModuleReason::ResourceLimit => "this import caused the module failure",
    }
}

const fn module_resource(resource: ModuleResource) -> &'static str {
    resource.diagnostic_name()
}

fn append_optional_import_primary(output: &mut String, span: Option<Span>, message: &str) {
    if let Some(span) = span {
        output.push_str("\nprimary: source ");
        output.push_str(&span.source().value().to_string());
        output.push(' ');
        output.push_str(&span.range().start().to_string());
        output.push_str("..");
        output.push_str(&span.range().end().to_string());
        output.push_str(": ");
        output.push_str(message);
    }
}

fn append_detail(output: &mut String, name: &str, value: &str) {
    output.push('\n');
    output.push_str(name);
    output.push_str(": ");
    output.push_str(value);
}

fn syntax_failure(failure: &SyntaxFailure) -> String {
    syntax_failure_parts(&failure.lexical, &failure.parser, failure.resource)
}

fn syntax_failure_parts(
    lexical: &[Diagnostic<LexReason>],
    parser: &[ParseDiagnostic],
    resource: Option<ResourceFailure>,
) -> String {
    let mut output = String::new();
    if let Some(resource) = resource {
        output.push_str(&resource_failure(resource));
    }
    let mut lexical = lexical.iter().peekable();
    let mut parser = parser.iter().peekable();
    while lexical.peek().is_some() || parser.peek().is_some() {
        let take_parser = match (lexical.peek(), parser.peek()) {
            (Some(lexical), Some(parser)) => {
                compare_source_spans(parser.primary.span(), lexical.primary.span()).is_lt()
            }
            (None, Some(_)) => true,
            (Some(_), None) | (None, None) => false,
        };
        let rendered = if take_parser {
            parser
                .next()
                .expect("a parser diagnostic was observed")
                .render_plain()
        } else {
            lexical
                .next()
                .expect("a lexical diagnostic was observed")
                .render_plain()
        };
        append_section(&mut output, &rendered);
    }
    if output.is_empty() {
        output.push_str("internal.syntax\nsyntax stage failed without a diagnostic");
    }
    output
}

fn append_section(output: &mut String, section: &str) {
    if !output.is_empty() {
        output.push('\n');
    }
    output.push_str(section);
}

fn resource_failure(failure: ResourceFailure) -> String {
    match failure {
        ResourceFailure::StructuralDepth { limit } => {
            format!("{}\nlimit {limit}", failure.reason_code())
        }
        ResourceFailure::SyntaxWork { limit } => {
            format!("{}\nlimit {limit}", failure.reason_code())
        }
    }
}

fn projection_failure(failure: ProjectionError) -> String {
    match failure {
        ProjectionError::ResourceLimit(resource) => resource_failure(resource),
        ProjectionError::RecoveryNodesPresent => {
            "internal.projection.recovery-nodes\nrecovery-bearing syntax reached projection"
                .to_owned()
        }
        ProjectionError::MalformedTree(reason) => {
            let mut output = String::from("internal.projection.malformed-tree\n");
            let _ = write!(&mut output, "{}", internal_reason(reason));
            output
        }
    }
}

const fn internal_reason(reason: InternalReason) -> &'static str {
    match reason {
        InternalReason::UnexpectedFinish => "unexpected finish event",
        InternalReason::UnclosedNode => "unclosed concrete node",
        InternalReason::InvalidRootCount => "invalid concrete root count",
        InternalReason::TokenOutOfRange => "token index outside retained stream",
        InternalReason::DuplicateToken => "token retained more than once",
        InternalReason::MissingToken => "token omitted from concrete tree",
        InternalReason::TokenOutOfOrder => "tokens retained out of source order",
        InternalReason::UnexpectedShape => "concrete node has an unexpected shape",
        InternalReason::ForeignSpan => "concrete token belongs to another source",
        InternalReason::InvalidSpan => "concrete token span is invalid",
    }
}
