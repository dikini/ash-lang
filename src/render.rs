//! Stable plain-text rendering at the executable boundary.

use std::fmt::Write;

use crate::{
    driver::{FileFailure, Observation, PipelineFailure, SyntaxFailure},
    parser::{InternalReason, ProjectionError, ResourceFailure},
};

/// Renders one successful observation with its required trailing newline.
#[must_use]
pub fn observation(observation: &Observation) -> String {
    format!("{} : {}\n", observation.value, observation.ty)
}

/// Renders one file or pipeline failure with its required trailing newline.
#[must_use]
pub fn file_failure(failure: &FileFailure) -> String {
    let mut output = match failure {
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
        PipelineFailure::Typing(error) => error.to_string(),
        PipelineFailure::Validation(error) => error.to_string(),
        PipelineFailure::Runtime(error) => format!("internal.runtime\n{error}"),
    }
}

fn syntax_failure(failure: &SyntaxFailure) -> String {
    let mut output = String::new();
    if let Some(resource) = failure.resource {
        output.push_str(&resource_failure(resource));
    }
    for diagnostic in &failure.lexical {
        append_section(&mut output, &diagnostic.render_plain());
    }
    for diagnostic in &failure.parser {
        append_section(&mut output, &diagnostic.render_plain());
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
            format!("internal.resource.structural-depth\nlimit {limit}")
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
