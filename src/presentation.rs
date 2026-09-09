//! Borrowed compile-time presentation. Runtime reporting is a separate path.

use std::{
    io::{self, Write},
    path::Path,
};

use crate::{
    diagnostic::{Diagnostic, compare_source_spans},
    lexer::LexReason,
    message::{Catalogue, CatalogueError, Message},
    module::{GraphDiagnostic, LoadGraphError, ModuleSyntaxFailure, io_kind_name},
    parser::{FoundToken, ParseContext, ParseDiagnostic, ResourceFailure, SynchronizationBoundary},
    source::{SourceError, SourceFile, Span},
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

/// Exposes the general checking rule's retained source type spellings.
///
/// # Errors
/// Returns missing source context. No declaration location is invented when
/// the general checking rule retains only the mismatching expression.
pub fn compile_type_mismatch_diagnostic<'a>(
    mismatch: &'a crate::elaborate::TypeMismatch,
    sources: &[&'a SourceFile],
) -> Result<CompileDiagnostic<'a>, PresentationError> {
    let span = mismatch.span();
    let source = sources
        .iter()
        .copied()
        .find(|source| source.id() == span.source())
        .ok_or(PresentationError::MissingSource)?;
    source
        .location(span)
        .map_err(|_| PresentationError::MissingSource)?;
    let (expected, found) = mismatch.display_types();
    let found_fact = Fact {
        name: "found",
        kind: "code",
        value: FactValue::Text(found),
    };
    Ok(CompileDiagnostic {
        reason: "type.mismatch".into(),
        responsibility: "source",
        message: mismatch.message(),
        primary: Some(Label {
            source,
            span,
            message: Message::type_found(found),
            relationship: "expression",
            facts: vec![found_fact],
        }),
        related: Vec::new(),
        facts: vec![
            Fact {
                name: "expected",
                kind: "code",
                value: FactValue::Text(expected),
            },
            found_fact,
        ],
    })
}

/// Exposes retained type-error facts without inspecting diagnostic prose.
///
/// # Errors
/// Returns an unsupported family or a missing causal fact/source. This staged
/// adapter is not yet selected by the executable's default renderer.
pub fn compile_type_diagnostic<'a>(
    diagnostic: &'a crate::elaborate::TypeDiagnostic,
    sources: &[&'a SourceFile],
) -> Result<CompileDiagnostic<'a>, PresentationError> {
    if let Some(crate::elaborate::TypeSourceMessage {
        message,
        relationship,
        fact,
        fact_kind,
        minimum_related,
    }) = diagnostic.source_message()
    {
        // These failures need no expected/found type comparison.
        // Preserve the optional phase fact with its own semantic name.
        if diagnostic.related.len() < minimum_related {
            return Err(PresentationError::MissingFact);
        }
        let span = diagnostic.primary.span();
        let source = sources
            .iter()
            .copied()
            .find(|source| source.id() == span.source())
            .ok_or(PresentationError::MissingSource)?;
        source
            .location(span)
            .map_err(|_| PresentationError::MissingSource)?;
        let facts: Vec<_> = fact
            .into_iter()
            .map(|(name, value)| Fact {
                name,
                kind: fact_kind,
                value: FactValue::Text(value),
            })
            .collect();
        let mut related = Vec::with_capacity(diagnostic.related.len());
        for (index, original) in diagnostic.related.iter().enumerate() {
            let (message, relationship) = diagnostic
                .source_related_message(index)
                .ok_or(PresentationError::Unsupported)?;
            let span = original.span();
            let source = sources
                .iter()
                .copied()
                .find(|source| source.id() == span.source())
                .ok_or(PresentationError::MissingSource)?;
            source
                .location(span)
                .map_err(|_| PresentationError::MissingSource)?;
            related.push(Label {
                source,
                span,
                message,
                relationship,
                facts: Vec::new(),
            });
        }
        return Ok(CompileDiagnostic {
            reason: diagnostic.reason.to_string(),
            responsibility: "source",
            primary: Some(Label {
                source,
                span,
                message: message.clone(),
                relationship,
                facts: facts.clone(),
            }),
            message,
            related,
            facts,
        });
    }
    let expected = diagnostic
        .expected
        .as_deref()
        .ok_or(PresentationError::MissingFact)?;
    let found = diagnostic
        .found
        .as_deref()
        .ok_or(PresentationError::MissingFact)?;
    let message = diagnostic
        .reason
        .message(expected, found)
        .ok_or(PresentationError::Unsupported)?;
    if diagnostic.related.len() < diagnostic.comparison_minimum_related() {
        return Err(PresentationError::MissingFact);
    }
    let (primary_message, primary_relationship) = diagnostic
        .reason
        .primary_message(found)
        .ok_or(PresentationError::Unsupported)?;
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
    let mut related = Vec::with_capacity(diagnostic.related.len());
    for (index, original) in diagnostic.related.iter().enumerate() {
        let (message, relationship, expected) = diagnostic
            .comparison_related_message(index, expected)
            .ok_or(PresentationError::Unsupported)?;
        related.push(label(
            original.span(),
            message,
            relationship,
            expected.map(|_| expected_fact).into_iter().collect(),
        )?);
    }
    Ok(CompileDiagnostic {
        reason: diagnostic.reason.to_string(),
        responsibility: "source",
        message,
        primary: Some(label(
            diagnostic.primary.span(),
            primary_message,
            primary_relationship,
            vec![found_fact],
        )?),
        related,
        facts: vec![expected_fact, found_fact],
    })
}

/// Exposes phase-owned interface diagnostics without interpreting prose.
///
/// # Errors
/// Returns unsupported reasons, missing facts or missing source context.
pub fn compile_interface_diagnostic<'a>(
    error: &'a crate::interface::InterfaceDiagnostic,
    sources: &[&'a SourceFile],
) -> Result<CompileDiagnostic<'a>, PresentationError> {
    let (message, relationship) = error.message().ok_or(PresentationError::Unsupported)?;
    let comparison = error.determination_comparison();
    if comparison.is_none() && (error.expected.is_some() || error.found.is_some()) {
        return Err(PresentationError::Unsupported);
    }
    if error.related.len() < error.minimum_related() {
        return Err(PresentationError::MissingFact);
    }
    let mut facts = error
        .argument_counts()
        .map_or_else(Vec::new, |(expected, found)| {
            vec![
                Fact {
                    name: "expected_count",
                    kind: "count",
                    value: FactValue::Integer(expected),
                },
                Fact {
                    name: "supplied_count",
                    kind: "count",
                    value: FactValue::Integer(found),
                },
            ]
        });
    if let Some((key, expected, found)) = comparison {
        for (name, value) in [
            ("determinant_key", key),
            ("expected", expected),
            ("found", found),
        ] {
            facts.push(Fact {
                name,
                kind: "code",
                value: FactValue::Text(value),
            });
        }
    }
    if let Some(cause) = error.determination_failure() {
        facts.push(Fact {
            name: "determination_failure",
            kind: "determination-failure",
            value: FactValue::Text(cause),
        });
    }
    if let Some(cause) = error.parameter_failure() {
        facts.push(Fact {
            name: "parameter_failure",
            kind: "method-parameter-failure",
            value: FactValue::Text(cause),
        });
    }
    let label = |span: Span, message, relationship| {
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
            facts: Vec::new(),
        })
    };
    let mut related = Vec::with_capacity(error.related.len());
    for (index, original) in error.related.iter().enumerate() {
        let (message, relationship) = error
            .related_message(index)
            .ok_or(PresentationError::Unsupported)?;
        related.push(label(original.span(), message, relationship)?);
    }
    Ok(CompileDiagnostic {
        reason: error.reason.to_string(),
        responsibility: "source",
        primary: Some(label(error.primary.span(), message.clone(), relationship)?),
        message,
        related,
        facts,
    })
}

/// Exposes a compiler-owned elaboration failure, retaining any known source span.
///
/// # Errors
/// Returns unsupported for causes not yet presented, or missing source context.
pub fn compile_elaboration_failure<'a>(
    error: &crate::elaborate::ElaborationFailure,
    sources: &[&'a SourceFile],
) -> Result<CompileDiagnostic<'a>, PresentationError> {
    let (message, name, kind, value) = error
        .diagnostic_message()
        .ok_or(PresentationError::Unsupported)?;
    let mut primary = None;
    let mut related = Vec::new();
    if let crate::elaborate::ElaborationFailure::Kind { context, span } = error {
        let origin = context.span();
        let primary_span = span.unwrap_or(origin);
        for (location, is_primary) in [(primary_span, true), (origin, false)] {
            if !is_primary && location == primary_span {
                continue;
            }
            let source = sources
                .iter()
                .copied()
                .find(|source| source.id() == location.source())
                .ok_or(PresentationError::MissingSource)?;
            source
                .location(location)
                .map_err(|_| PresentationError::MissingSource)?;
            let label = Label {
                source,
                span: location,
                message: if is_primary && primary_span != origin {
                    Message::elaboration_kind_use()
                } else {
                    context.message()
                },
                relationship: if is_primary {
                    "elaboration_site"
                } else {
                    "kind_failure_origin"
                },
                facts: Vec::new(),
            };
            if is_primary {
                primary = Some(label);
            } else {
                related.push(label);
            }
        }
    }
    Ok(CompileDiagnostic {
        reason: error.reason_code().to_owned(),
        responsibility: "compiler",
        message,
        primary,
        related,
        facts: vec![Fact {
            name,
            kind,
            value: FactValue::Text(value),
        }],
    })
}

/// Exposes a compiler-owned failure while validating linked interface evidence.
///
/// # Errors
/// Returns unsupported for causes not yet retained precisely, or missing source context.
pub fn compile_evidence_failure<'a>(
    error: &crate::evidence_validation::EvidenceValidationFailure,
    sources: &[&'a SourceFile],
) -> Result<CompileDiagnostic<'a>, PresentationError> {
    let (message, relationship) = error
        .diagnostic_message()
        .ok_or(PresentationError::Unsupported)?;
    let span = error.primary();
    let source = sources
        .iter()
        .copied()
        .find(|source| source.id() == span.source())
        .ok_or(PresentationError::MissingSource)?;
    source
        .location(span)
        .map_err(|_| PresentationError::MissingSource)?;
    let mut facts = vec![Fact {
        name: "stage",
        kind: "compiler-stage",
        value: FactValue::Text("evidence-validation"),
    }];
    if let Some(resource) = error.diagnostic_resource() {
        facts.push(Fact {
            name: "resource",
            kind: "resource",
            value: FactValue::Text(resource),
        });
    }
    let mut primary_message = message.clone();
    let mut related = Vec::new();
    if let Some(cause) = error.kind_context() {
        let origin = cause.span();
        facts.push(Fact {
            name: "kind_cause",
            kind: "kind-internal-cause",
            value: FactValue::Text(cause.name()),
        });
        if origin != span {
            let origin_source = sources
                .iter()
                .copied()
                .find(|source| source.id() == origin.source())
                .ok_or(PresentationError::MissingSource)?;
            origin_source
                .location(origin)
                .map_err(|_| PresentationError::MissingSource)?;
            primary_message = Message::evidence_kind_use();
            related.push(Label {
                source: origin_source,
                span: origin,
                message: cause.message(),
                relationship: "kind_failure_origin",
                facts: Vec::new(),
            });
        }
    }
    Ok(CompileDiagnostic {
        reason: error.reason().to_string(),
        responsibility: "compiler",
        primary: Some(Label {
            source,
            span,
            message: primary_message,
            relationship,
            facts: Vec::new(),
        }),
        message,
        related,
        facts,
    })
}

/// Exposes a compiler-owned Core validation failure, its optional arena-local
/// node and retained capture-analysis source relationships.
///
/// # Errors
/// Returns unsupported for causes not yet presented or a node handle that cannot be represented.
/// Returns missing source when a retained causal span cannot be resolved.
pub fn compile_core_validation_failure<'a>(
    error: &crate::core::validate::ValidationError,
    sources: &[&'a SourceFile],
) -> Result<CompileDiagnostic<'a>, PresentationError> {
    let message = error
        .diagnostic_message()
        .ok_or(PresentationError::Unsupported)?;
    let mut facts = Vec::new();
    if let Some(node) = error.node() {
        facts.push(Fact {
            name: "core_node",
            kind: "core-node",
            value: FactValue::Integer(
                usize::try_from(node.value()).map_err(|_| PresentationError::Unsupported)?,
            ),
        });
    }
    if let Some(cause) = error.cause_name() {
        facts.push(Fact {
            name: "cause",
            kind: "core-validation-cause",
            value: FactValue::Text(cause),
        });
    }
    let mut primary = None;
    let mut related = Vec::new();
    for (span, message, relationship) in error.capture_labels() {
        let source = sources
            .iter()
            .copied()
            .find(|source| source.id() == span.source())
            .ok_or(PresentationError::MissingSource)?;
        source
            .location(span)
            .map_err(|_| PresentationError::MissingSource)?;
        let label = Label {
            source,
            span,
            message,
            relationship,
            facts: Vec::new(),
        };
        if primary.is_none() {
            primary = Some(label);
        } else {
            related.push(label);
        }
    }
    if let Some(arm) = error.arm_number() {
        facts.push(Fact {
            name: "arm",
            kind: "match-arm-number",
            value: FactValue::Integer(arm),
        });
    }
    if let Some(error) = error.origin_span_failure() {
        facts.push(Fact {
            name: "source_failure",
            kind: "source-model-failure",
            value: FactValue::Text(error.diagnostic_name()),
        });
        match error {
            crate::source::SourceError::RangeOutsideSource { range, source_len } => {
                for (name, kind, value) in [
                    ("start", "byte-offset", range.start()),
                    ("end", "byte-offset", range.end()),
                    ("source_length", "byte-count", source_len),
                ] {
                    facts.push(Fact {
                        name,
                        kind,
                        value: FactValue::Integer(value as usize),
                    });
                }
            }
            crate::source::SourceError::OffsetSplitsCodePoint { offset } => {
                facts.push(Fact {
                    name: "offset",
                    kind: "byte-offset",
                    value: FactValue::Integer(offset as usize),
                });
            }
            _ => {}
        }
    }
    Ok(CompileDiagnostic {
        reason: error.reason().to_string(),
        responsibility: "compiler",
        message,
        primary,
        related,
        facts,
    })
}

/// Exposes the entry module's local-main contract failure.
///
/// # Errors
/// Returns missing source context.
pub fn compile_entry_diagnostic<'a>(
    error: &'a crate::driver::EntryFailure,
    sources: &[&'a SourceFile],
) -> Result<CompileDiagnostic<'a>, PresentationError> {
    let span = error.diagnostic.primary.span();
    let source = sources
        .iter()
        .copied()
        .find(|source| source.id() == span.source())
        .ok_or(PresentationError::MissingSource)?;
    source
        .location(span)
        .map_err(|_| PresentationError::MissingSource)?;
    let (message, relationship) = error.primary_message();
    Ok(CompileDiagnostic {
        reason: error.reason().to_string(),
        responsibility: "source",
        message: error.message(),
        primary: Some(Label {
            source,
            span,
            message,
            relationship,
            facts: Vec::new(),
        }),
        related: Vec::new(),
        facts: Vec::new(),
    })
}

/// Presents source kind errors or compiler resource failures through distinct classifications.
///
/// # Errors
/// Returns missing source context or a missing internal-state cause.
pub fn compile_kind_failure<'a>(
    error: &'a crate::kind::KindFailure,
    sources: &[&'a SourceFile],
) -> Result<CompileDiagnostic<'a>, PresentationError> {
    if let crate::kind::KindFailure::Source(error) = error {
        return compile_kind_diagnostic(error, sources);
    }
    let (span, message, fact) = if let Some((span, message)) = error.resource_presentation() {
        (
            span,
            message,
            Fact {
                name: "resource",
                kind: "resource",
                value: FactValue::Text("type-work"),
            },
        )
    } else if let Some((span, message, cause)) = error.internal_presentation() {
        (
            span,
            message,
            Fact {
                name: "cause",
                kind: "kind-internal-cause",
                value: FactValue::Text(cause),
            },
        )
    } else {
        return Err(PresentationError::Unsupported);
    };
    let source = sources
        .iter()
        .copied()
        .find(|source| source.id() == span.source())
        .ok_or(PresentationError::MissingSource)?;
    source
        .location(span)
        .map_err(|_| PresentationError::MissingSource)?;
    Ok(CompileDiagnostic {
        reason: error.reason_code(),
        responsibility: "compiler",
        primary: Some(Label {
            source,
            span,
            message: message.clone(),
            relationship: "kind_checking_site",
            facts: Vec::new(),
        }),
        message,
        related: Vec::new(),
        facts: vec![
            Fact {
                name: "stage",
                kind: "compiler-stage",
                value: FactValue::Text("kind-checking"),
            },
            fact,
        ],
    })
}

/// Exposes phase-owned kind facts without interpreting diagnostic prose.
///
/// # Errors
/// Returns missing kind facts or source context.
pub fn compile_kind_diagnostic<'a>(
    error: &'a crate::kind::KindError,
    sources: &[&'a SourceFile],
) -> Result<CompileDiagnostic<'a>, PresentationError> {
    let expected = error
        .diagnostic()
        .expected
        .as_deref()
        .ok_or(PresentationError::MissingFact)?;
    let found = error
        .diagnostic()
        .found
        .as_deref()
        .ok_or(PresentationError::MissingFact)?;
    let (shape, expected_format) = match error.expectation() {
        crate::kind::KindExpectation::Exact(_) => ("exact", "kind"),
        crate::kind::KindExpectation::Function { .. } => ("function", "kind-pattern"),
    };
    let expected_fact = Fact {
        name: "expected_kind",
        kind: expected_format,
        value: FactValue::Text(expected),
    };
    let found_fact = Fact {
        name: "found_kind",
        kind: "kind",
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
    let mut related = Vec::with_capacity(error.related.len());
    for original in &error.related {
        let (message, relationship, kind) = error
            .related_message()
            .ok_or(PresentationError::MissingFact)?;
        related.push(label(
            original.span(),
            message,
            relationship,
            Fact {
                name: "kind",
                kind: "kind",
                value: FactValue::Text(kind),
            },
        )?);
    }
    Ok(CompileDiagnostic {
        reason: error.reason.to_string(),
        responsibility: "source",
        message: error.message().ok_or(PresentationError::MissingFact)?,
        primary: Some(label(
            error.primary.span(),
            Message::kind_found(found),
            "kind_mismatch",
            found_fact,
        )?),
        related,
        facts: vec![
            expected_fact,
            found_fact,
            Fact {
                name: "expectation_shape",
                kind: "kind-expectation",
                value: FactValue::Text(shape),
            },
        ],
    })
}

/// Exposes phase-owned resolution facts without interpreting diagnostic prose.
///
/// # Errors
/// Returns an unsupported staged family, missing facts or source context.
pub fn compile_resolve_diagnostic<'a>(
    error: &'a crate::resolve::ResolveError,
    sources: &[&'a SourceFile],
) -> Result<CompileDiagnostic<'a>, PresentationError> {
    let message = error.message().ok_or(PresentationError::Unsupported)?;
    let subject = error.subject_fact().map(|(name, kind, value)| Fact {
        name,
        kind,
        value: FactValue::Text(value),
    });
    let (primary_message, primary_relationship) = error
        .primary_message()
        .ok_or(PresentationError::Unsupported)?;
    let span = error.primary.span();
    let source = sources
        .iter()
        .copied()
        .find(|source| source.id() == span.source())
        .ok_or(PresentationError::MissingSource)?;
    source
        .location(span)
        .map_err(|_| PresentationError::MissingSource)?;
    let mut facts: Vec<_> = subject.into_iter().collect();
    if error.resource_name().is_some() || error.kind_context().is_some() {
        facts.push(Fact {
            name: "stage",
            kind: "compiler-stage",
            value: FactValue::Text("resolution"),
        });
    }
    if let Some(usage) = error.name_use() {
        facts.push(Fact {
            name: "name_use",
            kind: "name-use",
            value: FactValue::Text(usage),
        });
    }
    if let Some(expected) = error.expected_name() {
        facts.push(Fact {
            name: "expected_name",
            kind: "identifier",
            value: FactValue::Text(expected),
        });
    }
    if let Some(access) = error.access_name() {
        facts.push(Fact {
            name: "access",
            kind: "name-access",
            value: FactValue::Text(access),
        });
    }
    if let Some(scope) = error.lookup_scope_name() {
        facts.push(Fact {
            name: "lookup_scope",
            kind: "lookup-scope",
            value: FactValue::Text(scope),
        });
    }
    let mut related = Vec::with_capacity(error.related.len());
    if let Some(context) = error.kind_context() {
        let origin = context.span();
        if origin != span {
            let source = sources
                .iter()
                .copied()
                .find(|source| source.id() == origin.source())
                .ok_or(PresentationError::MissingSource)?;
            source
                .location(origin)
                .map_err(|_| PresentationError::MissingSource)?;
            related.push(Label {
                source,
                span: origin,
                message: context.message(),
                relationship: "kind_failure_origin",
                facts: Vec::new(),
            });
        }
    }
    for (index, label) in error.related.iter().enumerate() {
        let (message, relationship) = error
            .related_message(index)
            .ok_or(PresentationError::Unsupported)?;
        let span = label.span();
        let source = sources
            .iter()
            .copied()
            .find(|source| source.id() == span.source())
            .ok_or(PresentationError::MissingSource)?;
        source
            .location(span)
            .map_err(|_| PresentationError::MissingSource)?;
        related.push(Label {
            source,
            span,
            message,
            relationship,
            facts: error
                .related_name()
                .map(|value| Fact {
                    value: FactValue::Text(value),
                    name: "name",
                    kind: "identifier",
                })
                .into_iter()
                .collect(),
        });
    }
    Ok(CompileDiagnostic {
        reason: error.reason.to_string(),
        responsibility: if error.is_source_rejection() {
            "source"
        } else {
            "compiler"
        },
        message,
        primary: Some(Label {
            source,
            span,
            message: primary_message,
            relationship: primary_relationship,
            facts: subject.into_iter().collect(),
        }),
        related,
        facts,
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

/// Dispatches a file failure to its existing compile-time phase adapter.
///
/// Source files remain borrowed from the failure owner. Runtime failures are
/// deliberately excluded and must use the separate runtime reporting interface.
///
/// # Errors
/// Returns an unsupported staged cause or missing source context. Legacy bare
/// syntax failures do not identify their owning
/// source; graph-loading failures retain that context and use the graph adapter.
pub fn compile_file_diagnostics(
    failure: &crate::driver::FileFailure,
) -> Result<Vec<CompileDiagnostic<'_>>, PresentationError> {
    use crate::{
        driver::{FileFailure, PipelineFailure},
        elaborate::TypeError,
    };
    let sources: Vec<_> = failure.sources().iter().collect();
    let diagnostic = match failure {
        FileFailure::Graph(context) => return compile_graph_diagnostics(context),
        FileFailure::Read { path, kind } => compile_input_diagnostic(path, Some(*kind)),
        FileFailure::InvalidUtf8 { path } => compile_input_diagnostic(path, None),
        FileFailure::Source(error) => compile_source_model_error(
            error,
            crate::source::SourceOperation::Admission,
            None,
            "input.source-model",
        ),
        FileFailure::Pipeline(context) => match context.failure() {
            PipelineFailure::Resolution(error) => compile_resolve_diagnostic(error, &sources)?,
            PipelineFailure::Kind(error) => compile_kind_failure(error, &sources)?,
            PipelineFailure::Typing(TypeError::Source(error)) => {
                compile_type_diagnostic(error, &sources)?
            }
            PipelineFailure::Typing(TypeError::Interface(error)) => {
                compile_interface_diagnostic(error, &sources)?
            }
            PipelineFailure::Typing(TypeError::Mismatch(error)) => {
                compile_type_mismatch_diagnostic(error, &sources)?
            }
            PipelineFailure::Typing(TypeError::Internal(error)) => {
                compile_elaboration_failure(error, &sources)?
            }
            PipelineFailure::Entry(error) => compile_entry_diagnostic(error, &sources)?,
            PipelineFailure::EvidenceValidation(error) => {
                compile_evidence_failure(error, &sources)?
            }
            PipelineFailure::Validation(error) => compile_core_validation_failure(error, &sources)?,
            PipelineFailure::Runtime(_) => return Err(PresentationError::Unsupported),
            PipelineFailure::SourceModel(error) => compile_source_model_error(
                error,
                crate::source::SourceOperation::SpanConstruction,
                None,
                "internal.source-model",
            ),
            PipelineFailure::Projection(error) => compile_projection_error(error, None),
            PipelineFailure::Syntax(error) => {
                return compile_syntax_diagnostics(
                    &error.lexical,
                    &error.parser,
                    error.resource,
                    &sources,
                    None,
                );
            }
        },
    };
    Ok(vec![diagnostic])
}

fn compile_projection_error<'a>(
    error: &crate::parser::ProjectionError,
    path: Option<&'a str>,
) -> CompileDiagnostic<'a> {
    let mut facts = Vec::new();
    if let Some(path) = path {
        facts.push(Fact {
            name: "source_path",
            kind: "path-display",
            value: FactValue::Text(path),
        });
    }
    match error {
        crate::parser::ProjectionError::ResourceLimit(
            ResourceFailure::StructuralDepth { limit } | ResourceFailure::SyntaxWork { limit },
        ) => facts.push(Fact {
            name: "limit",
            kind: "integer",
            value: FactValue::Integer(*limit),
        }),
        crate::parser::ProjectionError::RecoveryNodesPresent => facts.push(Fact {
            name: "cause",
            kind: "projection",
            value: FactValue::Text("recovery-nodes"),
        }),
        crate::parser::ProjectionError::MalformedTree(cause) => facts.push(Fact {
            name: "cause",
            kind: "projection",
            value: FactValue::Text(cause.diagnostic_name()),
        }),
    }
    CompileDiagnostic {
        reason: error.reason_code().into(),
        responsibility: "compiler",
        message: path.map_or_else(|| error.message_without_path(), |path| error.message(path)),
        primary: None,
        related: Vec::new(),
        facts,
    }
}

fn compile_source_model_error<'a>(
    error: &crate::source::SourceError,
    operation: crate::source::SourceOperation,
    path: Option<&'a std::path::Path>,
    reason: &'static str,
) -> CompileDiagnostic<'a> {
    let mut facts = Vec::new();
    if let Some(path) = path {
        facts.push(Fact {
            name: "path",
            kind: "path",
            value: FactValue::Path(path),
        });
    }
    facts.push(Fact {
        name: "cause",
        kind: "source-model",
        value: FactValue::Text(error.diagnostic_name()),
    });
    let mut quantity = |name, value: u32| {
        facts.push(Fact {
            name,
            kind: "integer",
            value: FactValue::Integer(value as usize),
        })
    };
    match error {
        SourceError::RangeOutsideSource { range, source_len } => {
            quantity("start", range.start());
            quantity("end", range.end());
            quantity("source_len", *source_len);
        }
        SourceError::ForeignSpan { expected, found } => {
            quantity("expected_source", expected.value());
            quantity("found_source", found.value());
        }
        SourceError::OffsetOutsideSource { offset, source_len } => {
            quantity("offset", *offset);
            quantity("source_len", *source_len);
        }
        SourceError::OffsetSplitsCodePoint { offset } => quantity("offset", *offset),
        SourceError::SourceIdExhausted
        | SourceError::DisplayPathTooLarge
        | SourceError::TextTooLarge
        | SourceError::TooManyLines
        | SourceError::LineTooLong
        | SourceError::InvalidLineState => {}
    }
    CompileDiagnostic {
        reason: reason.into(),
        responsibility: error.responsibility(operation),
        message: path.map_or_else(
            || error.message_without_path(operation),
            |path| error.message(path, operation),
        ),
        primary: None,
        related: Vec::new(),
        facts: {
            facts.push(Fact {
                name: "operation",
                kind: "source-operation",
                value: FactValue::Text(match operation {
                    crate::source::SourceOperation::Admission => "admission",
                    crate::source::SourceOperation::SpanConstruction => "span-construction",
                }),
            });
            facts
        },
    }
}

/// Presents the executable's invocation grammar without inventing source labels.
#[must_use]
pub fn compile_usage_diagnostic() -> CompileDiagnostic<'static> {
    CompileDiagnostic {
        reason: "invocation.usage".into(),
        responsibility: "invocation",
        message: Message::invocation_usage(),
        primary: None,
        related: Vec::new(),
        facts: Vec::new(),
    }
}

/// Presents the executable's failed standard-output write.
#[must_use]
pub fn compile_output_write_diagnostic() -> CompileDiagnostic<'static> {
    CompileDiagnostic {
        reason: "internal.output-write".into(),
        responsibility: "compiler",
        message: Message::output_write(),
        primary: None,
        related: Vec::new(),
        facts: Vec::new(),
    }
}

/// Writes retained legacy details when a staged adapter cannot construct a view.
///
/// This explicitly marked fallback is not presentation coverage. It emits JSON
/// in every format and retains the original reason and existing diagnostic
/// details without parsing them. Runtime failures must not use this allocating path.
///
/// # Errors
/// Stops at the first serialization, write or flush failure without retry.
pub fn write_unadapted_file_diagnostic(
    writer: &mut impl Write,
    failure: &crate::driver::FileFailure,
    error: PresentationError,
) -> Result<(), RenderError> {
    if matches!(
        failure.pipeline_failure(),
        Some(crate::driver::PipelineFailure::Runtime(_))
    ) {
        return Err(RenderError::Write(io::ErrorKind::InvalidInput.into()));
    }
    let writer = &mut crate::render::DiagnosticWriter(writer);
    let responsibility = match failure {
        crate::driver::FileFailure::Source(error) => {
            error.responsibility(crate::source::SourceOperation::Admission)
        }
        crate::driver::FileFailure::Read { .. }
        | crate::driver::FileFailure::InvalidUtf8 { .. } => "input",
        crate::driver::FileFailure::Graph(context) => match context.failure() {
            LoadGraphError::Module(error) => error.responsibility(),
            LoadGraphError::Read { .. } | LoadGraphError::InvalidUtf8 { .. } => "input",
            LoadGraphError::SourceModel {
                error, operation, ..
            } => error.responsibility(*operation),
            _ if failure.is_source_rejection() => "source",
            _ => "compiler",
        },
        _ if failure.is_source_rejection() => "source",
        _ => "compiler",
    };
    let data = serde_json::json!({
        "schema_version": 1,
        "reason": failure.reason_code(),
        "responsibility": responsibility,
        "facts": [],
        "labels": [],
        "developer_details": {
            "presentation_error": match error {
                PresentationError::Unsupported => "unsupported",
                PresentationError::MissingFact => "missing-fact",
                PresentationError::MissingSource => "missing-source",
            },
            "retained_diagnostic": crate::render::file_failure(failure),
        },
    });
    serde_json::to_writer(&mut *writer, &data).map_err(RenderError::Json)?;
    writer.write_all(b"\n")?;
    writer.flush().map_err(RenderError::Write)
}

/// Exposes input and graph failure facts. Syntax collections keep their causal order.
///
/// # Errors
/// Returns an unsupported staged family or missing admitted source context.
pub fn compile_graph_diagnostics(
    context: &GraphDiagnostic,
) -> Result<Vec<CompileDiagnostic<'_>>, PresentationError> {
    let failure = context.failure();
    if let LoadGraphError::Projection { source, error, .. } = failure {
        let mut diagnostic = compile_projection_error(error, Some(source.display_path()));
        diagnostic.primary = import_label(context, "import_context")?;
        return Ok(vec![diagnostic]);
    }
    if let LoadGraphError::SourceModel {
        path,
        error,
        operation,
        ..
    } = failure
    {
        let mut diagnostic =
            compile_source_model_error(error, *operation, Some(path), "input.source-model");
        diagnostic.primary = import_label(context, "import_target")?;
        return Ok(vec![diagnostic]);
    }
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
        if let Some(resource) = failure.resource_kind() {
            facts.push(Fact {
                name: "resource",
                kind: "resource",
                value: FactValue::Text(resource.diagnostic_name()),
            });
        }
        if let Some(kind) = failure.io_kind() {
            facts.push(Fact {
                name: "io_kind",
                kind: "io",
                value: FactValue::Text(io_kind_name(kind)),
            });
        }
        if let Some(cause) = failure.path_cause_name() {
            facts.push(Fact {
                name: "cause",
                kind: "module-path",
                value: FactValue::Text(cause),
            });
        }
        return Ok(vec![CompileDiagnostic {
            reason: failure.reason().to_string(),
            responsibility: failure.responsibility(),
            message,
            primary: import_label(context, "import_target")?,
            related: Vec::new(),
            facts,
        }]);
    }
    if let LoadGraphError::Syntax(failure) = failure {
        return compile_graph_syntax(context, failure);
    }
    let mut diagnostic = match failure {
        LoadGraphError::Read { path, kind, .. } => compile_input_diagnostic(path, Some(*kind)),
        LoadGraphError::InvalidUtf8 { path, .. } => compile_input_diagnostic(path, None),
        _ => return Err(PresentationError::Unsupported),
    };
    diagnostic.primary = import_label(context, "import_target")?;
    Ok(vec![diagnostic])
}

fn compile_input_diagnostic(path: &Path, kind: Option<io::ErrorKind>) -> CompileDiagnostic<'_> {
    let (reason, message) = match kind {
        Some(kind) => ("input.read", Message::input_read(path, kind)),
        None => ("input.invalid-utf8", Message::input_invalid_utf8(path)),
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
    CompileDiagnostic {
        reason: reason.into(),
        responsibility: "input",
        message,
        primary: None,
        related: Vec::new(),
        facts,
    }
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
    let mut diagnostics = compile_syntax_diagnostics(
        &failure.lexical,
        &failure.parser,
        failure.resource,
        &sources,
        Some(failure.source.display_path()),
    )?;
    for diagnostic in &mut diagnostics {
        if let Some(import) = import_label(context, "import_context")? {
            diagnostic.related.push(import);
        }
    }
    Ok(diagnostics)
}

fn compile_syntax_diagnostics<'a>(
    lexical: &'a [Diagnostic<LexReason>],
    parser: &'a [ParseDiagnostic],
    resource: Option<ResourceFailure>,
    sources: &[&'a SourceFile],
    path: Option<&'a str>,
) -> Result<Vec<CompileDiagnostic<'a>>, PresentationError> {
    let mut diagnostics = Vec::new();
    if let Some(resource) = resource {
        let (limit, message) = match resource {
            ResourceFailure::StructuralDepth { limit } => (
                limit,
                path.map_or_else(
                    || Message::syntax_depth_unlocated(limit),
                    |path| Message::syntax_depth(path, limit),
                ),
            ),
            ResourceFailure::SyntaxWork { limit } => (
                limit,
                path.map_or_else(
                    || Message::syntax_work_unlocated(limit),
                    |path| Message::syntax_work(path, limit),
                ),
            ),
        };
        diagnostics.push(CompileDiagnostic {
            reason: resource.reason_code().into(),
            responsibility: "compiler",
            message,
            primary: None,
            related: Vec::new(),
            facts: {
                let mut facts = vec![Fact {
                    name: "limit",
                    kind: "integer",
                    value: FactValue::Integer(limit),
                }];
                if let Some(path) = path {
                    facts.push(Fact {
                        name: "source_path",
                        kind: "path-display",
                        value: FactValue::Text(path),
                    });
                }
                facts
            },
        });
    }
    // Merge the retained streams exactly as the established syntax reporter does.
    // Do not globally sort: parser insertion order also carries recovery causality.
    let mut lexical = lexical.iter().peekable();
    let mut parser = parser.iter().peekable();
    while lexical.peek().is_some() || parser.peek().is_some() {
        let take_parser = match (lexical.peek(), parser.peek()) {
            (Some(lexical), Some(parser)) => {
                compare_source_spans(parser.primary.span(), lexical.primary.span()).is_lt()
            }
            (None, Some(_)) => true,
            _ => false,
        };
        diagnostics.push(if take_parser {
            compile_parse_diagnostic(parser.next().expect("observed parser diagnostic"), sources)?
        } else {
            compile_lex_diagnostic(
                lexical.next().expect("observed lexical diagnostic"),
                sources,
            )?
        });
    }
    if diagnostics.is_empty() {
        return Err(PresentationError::MissingFact);
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
    // Finish catalogue work before publishing any text. A failed catalogue can
    // then fall back without leaving a half-written localized diagnostic.
    let message = catalogue.format(&diagnostic.message)?;
    let label_messages = diagnostic
        .primary
        .iter()
        .chain(&diagnostic.related)
        .map(|label| catalogue.format(&label.message))
        .collect::<Result<Vec<_>, _>>()?;
    let writer = &mut crate::render::DiagnosticWriter(writer);
    writeln!(writer, "{message}")?;
    for (label, message) in diagnostic
        .primary
        .iter()
        .chain(&diagnostic.related)
        .zip(label_messages)
    {
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
        let mut last_line = location.end().line();
        if last_line > line && location.end().column() == 1 {
            last_line -= 1; // The span excludes the beginning of this line.
        }
        for (offset, excerpt) in label
            .source
            .text()
            .split('\n')
            .skip((line - 1) as usize)
            .take((last_line - line + 1) as usize)
            .enumerate()
        {
            let excerpt = excerpt.strip_suffix('\r').unwrap_or(excerpt);
            let prefix: String = excerpt
                .chars()
                .take(if offset == 0 {
                    (column - 1) as usize
                } else {
                    0
                })
                .collect();
            let indent = unicode_width::UnicodeWidthStr::width(expand_tabs(&prefix).as_str());
            let excerpt = expand_tabs(excerpt);
            let displayed_line = line as usize + offset;
            let gutter = displayed_line.to_string().len();
            writeln!(writer, "{displayed_line} | {excerpt}")?;
            writeln!(
                writer,
                "{} | {}^ {}",
                " ".repeat(gutter),
                " ".repeat(indent),
                message
            )?;
        }
    }
    writeln!(writer, "reason: {}", diagnostic.reason)?;
    Ok(())
}

fn expand_tabs(line: &str) -> String {
    let mut expanded = String::new();
    let mut width = 0;
    for (index, part) in line.split('\t').enumerate() {
        if index != 0 {
            let spaces = 4 - width % 4;
            expanded.extend(std::iter::repeat_n(' ', spaces));
            width += spaces;
        }
        expanded.push_str(part);
        width += unicode_width::UnicodeWidthStr::width(part);
    }
    expanded
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
    let message = catalogue.format(&diagnostic.message)?;
    let writer = &mut crate::render::DiagnosticWriter(writer);
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
    writeln!(writer, "{} [{}]", message, diagnostic.reason)?;
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
    let writer = &mut crate::render::DiagnosticWriter(writer);
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

/// Writes and flushes one compile-time diagnostic in the selected format.
///
/// An absent or defective catalogue falls back to the same locale-independent
/// JSON record, preserving the original reason, facts and labels. JSON output
/// never needs a catalogue. This allocating compile-time interface must not be
/// used for runtime resource failures.
///
/// # Errors
/// Returns the first output failure without retrying, flushing after a failed
/// write, or recursively reporting the reporting failure.
pub fn write_compile_diagnostic(
    writer: &mut impl Write,
    diagnostic: &CompileDiagnostic<'_>,
    format: crate::diagnostic_options::MessageFormat,
    catalogue: Option<&Catalogue>,
) -> Result<(), RenderError> {
    use crate::diagnostic_options::MessageFormat;
    let result = match (format, catalogue) {
        (MessageFormat::Json, _) | (_, None) => write_json(writer, diagnostic),
        (MessageFormat::Human, Some(catalogue)) => write_human(writer, diagnostic, catalogue),
        (MessageFormat::Short, Some(catalogue)) => write_short(writer, diagnostic, catalogue),
    };
    match result {
        Err(RenderError::Catalogue(_)) => write_json(writer, diagnostic)?,
        other => other?,
    }
    writer.flush().map_err(RenderError::Write)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{diagnostic::SourceLabel, elaborate::TypeReason, source::ByteRange};

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
        let diagnostic = diagnostic.into();
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
