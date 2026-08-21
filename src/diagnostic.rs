//! Structured diagnostics kept separate from their presentation.

use std::fmt;

use crate::source::Span;

/// A source span and the explanation attached to that location.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceLabel {
    span: Span,
    message: String,
}

impl SourceLabel {
    /// Creates a label for a checked source span.
    pub fn new(span: Span, message: impl Into<String>) -> Self {
        Self {
            span,
            message: message.into(),
        }
    }

    /// Returns the source span carrying this label.
    #[must_use]
    pub const fn span(&self) -> Span {
        self.span
    }

    /// Returns the explanation attached to this location.
    #[must_use]
    pub fn message(&self) -> &str {
        &self.message
    }
}

/// A structured compiler diagnostic whose semantic reason is preserved as `R`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Diagnostic<R> {
    /// The phase-owned semantic reason for the failure.
    pub reason: R,
    /// The location that most directly caused the failure.
    pub primary: SourceLabel,
    /// Other locations needed to explain the causal relationship.
    pub related: Vec<SourceLabel>,
    /// The expected user-facing form, when relevant.
    pub expected: Option<String>,
    /// The form found by the compiler, when relevant.
    pub found: Option<String>,
    /// A correction justified by established compiler facts, when available.
    pub help: Option<String>,
}

impl<R> Diagnostic<R> {
    /// Creates a diagnostic with one primary label and no optional context.
    pub fn new(reason: R, primary: SourceLabel) -> Self {
        Self {
            reason,
            primary,
            related: Vec::new(),
            expected: None,
            found: None,
            help: None,
        }
    }
}

impl<R: fmt::Display> Diagnostic<R> {
    /// Renders a minimal, stable plain-text view of the structured fields.
    ///
    /// Later presentation code may add source excerpts without changing the
    /// semantic reason or labels stored here.
    #[must_use]
    pub fn render_plain(&self) -> String {
        let mut output = self.reason.to_string();
        append_label(&mut output, "primary", &self.primary);

        for label in &self.related {
            append_label(&mut output, "related", label);
        }
        if let Some(expected) = &self.expected {
            output.push_str("\nexpected ");
            output.push_str(expected);
        }
        if let Some(found) = &self.found {
            output.push_str("\nfound ");
            output.push_str(found);
        }
        if let Some(help) = &self.help {
            output.push_str("\nhelp: ");
            output.push_str(help);
        }

        output
    }
}

fn append_label(output: &mut String, kind: &str, label: &SourceLabel) {
    let span = label.span();
    output.push('\n');
    output.push_str(kind);
    output.push_str(": source ");
    output.push_str(&span.source().value().to_string());
    output.push(' ');
    output.push_str(&span.range().start().to_string());
    output.push_str("..");
    output.push_str(&span.range().end().to_string());
    output.push_str(": ");
    output.push_str(label.message());
}
