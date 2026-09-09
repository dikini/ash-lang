//! Borrowed compile-time presentation. Runtime reporting is a separate path.

use std::io::{self, Write};

use crate::{
    diagnostic::Diagnostic,
    elaborate::TypeReason,
    lexer::LexReason,
    message::{Catalogue, CatalogueError, Message},
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
    value: &'a str,
}

/// A compile-time view borrowing its phase diagnostic and source context.
pub struct CompileDiagnostic<'a> {
    reason: String,
    message: Message<'a>,
    primary: Label<'a>,
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
        value: expected,
    };
    let found_fact = Fact {
        name: "found",
        value: found,
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
        message: Message::binding_initializer(expected, found),
        primary: label(
            diagnostic.primary.span(),
            Message::initializer(found),
            "initializer",
            found_fact,
        )?,
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
        value: found,
    };
    Ok(CompileDiagnostic {
        reason: diagnostic.reason.to_string(),
        message: diagnostic.reason.message(),
        primary: Label {
            source,
            span,
            message: diagnostic.reason.message(),
            relationship: "invalid_token",
            facts: vec![fact],
        },
        related: Vec::new(),
        facts: vec![fact],
    })
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
    for label in std::iter::once(&diagnostic.primary).chain(&diagnostic.related) {
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
    let label = &diagnostic.primary;
    let location = label
        .source
        .location(label.span)
        .expect("validated diagnostic span");
    writeln!(
        writer,
        "{}:{}:{}: {} [{}]",
        label.source.display_path(),
        location.start().line(),
        location.start().column(),
        catalogue.format(&diagnostic.message)?,
        diagnostic.reason
    )?;
    Ok(())
}

#[derive(serde::Serialize)]
struct JsonFact<'a> {
    name: &'static str,
    kind: &'static str,
    value: &'a str,
}

fn facts<'a>(source: &[Fact<'a>]) -> Vec<JsonFact<'a>> {
    source
        .iter()
        .map(|fact| JsonFact {
            name: fact.name,
            kind: "code",
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
    let labels = std::iter::once(("primary", &diagnostic.primary))
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
        responsibility: "source",
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
        view.primary.message = Message::binding_annotation("presentation-only");
        let mut after = Vec::new();
        write_json(&mut after, &view).unwrap();
        assert_eq!(before, after);
    }
}
