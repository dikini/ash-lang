//! Stable plain-text rendering at the executable boundary.

use std::fmt::Write;

use crate::{
    diagnostic::{Diagnostic, compare_source_spans},
    driver::{FileFailure, Observation, PipelineFailure, SyntaxFailure},
    elaborate::TypeError,
    lexer::LexReason,
    module::{LoadGraphError, ModuleFailure, ModuleReason, ModuleResource},
    parser::{InternalReason, ParseDiagnostic, ProjectionError, ResourceFailure},
    source::Span,
};

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
        FileFailure::Graph(error) => graph_failure(error),
        FileFailure::Read { path, kind } => {
            format!("input.read\n{}: {kind}", path.display())
        }
        FileFailure::InvalidUtf8 { path } => {
            format!("input.invalid-utf8\n{} is not UTF-8", path.display())
        }
        FileFailure::Source(error) => format!("input.source-model\n{error}"),
        FileFailure::Pipeline(failure) => pipeline_failure(failure),
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
        PipelineFailure::Typing(error @ TypeError::Source(_)) => error.to_string(),
        PipelineFailure::Typing(error @ TypeError::Mismatch(_)) => {
            format!("type.mismatch\n{error}")
        }
        PipelineFailure::Typing(error @ TypeError::Internal(failure)) => {
            format!("{}\n{error}", failure.reason_code())
        }
        PipelineFailure::Entry(error) => error.diagnostic.render_plain(),
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
        LoadGraphError::Projection { source, error } => {
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
    match resource {
        ModuleResource::GraphIdentities => "graph-identities",
        ModuleResource::Sources => "sources",
        ModuleResource::Edges => "edges",
        ModuleResource::PathSegments => "path-segments",
        ModuleResource::OwnerFacts => "owner-facts",
        ModuleResource::PendingWork => "pending-work",
    }
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
