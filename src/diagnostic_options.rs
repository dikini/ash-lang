//! Diagnostic option selection, independent of program and root validation.
//!
//! The executable supplies the locale environment once. Selection scans the
//! whole argument list so an earlier invocation error does not hide a later
//! valid reporting option before the entry path. This module does not execute
//! programs, initialize catalogues or write diagnostics.

use std::ffi::OsString;

use crate::message::Locale;

/// Supported diagnostic output contracts.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum MessageFormat {
    /// Localized explanation and source context.
    #[default]
    Human,
    /// Compact localized text, not a machine protocol.
    Short,
    /// Locale-independent JSON-lines diagnostics.
    Json,
}

/// Selected reporting settings and untouched program arguments.
///
/// An invalid diagnostic option is an invocation error, but does not discard
/// the settings needed to report that error. Program/root validation remains
/// separate and must run before execution.
#[derive(Debug)]
pub struct DiagnosticOptions {
    /// Exactly one valid format before the entry path, or human output.
    pub format: MessageFormat,
    /// Explicit locale or process locale, with supported-language fallback.
    pub locale: Locale,
    /// Arguments remaining after removing diagnostic options and their values.
    pub program_arguments: Vec<OsString>,
    /// A diagnostic option was missing a value, invalid, repeated or misplaced.
    pub invalid_options: bool,
}

impl DiagnosticOptions {
    /// Selects reporting options while preserving ordinary CLI arguments.
    ///
    /// `environment` supplies LC_ALL, LC_MESSAGES and LANG, in that order.
    /// The first nonempty value wins; an unsupported value falls back to English
    /// rather than consulting a lower-priority variable. Exactly one explicit
    /// locale overrides the environment, including an empty or unsupported name.
    /// Repeated locale options are invalid and leave environment fallback in use.
    #[must_use]
    pub fn parse(
        arguments: impl IntoIterator<Item = OsString>,
        environment: [Option<OsString>; 3],
    ) -> Self {
        let mut arguments = arguments.into_iter().peekable();
        let mut program_arguments = Vec::new();
        let mut entry_seen = false;
        let mut build = false;
        let mut invalid_options = false;
        let mut format_count = 0_usize;
        let mut locale_count = 0_usize;
        let mut format = None;
        let mut explicit_locale = None;
        while let Some(argument) = arguments.next() {
            if argument == "--message-format" || argument == "--locale" {
                if entry_seen {
                    invalid_options = true;
                    program_arguments.push(argument);
                    continue;
                }
                let is_format = argument == "--message-format";
                if is_format {
                    format_count += 1;
                } else {
                    locale_count += 1;
                }
                let Some(value) =
                    arguments.next_if(|value| !value.as_encoded_bytes().starts_with(b"--"))
                else {
                    invalid_options = true;
                    continue;
                };
                if is_format {
                    format = match value.to_str() {
                        Some("human") => Some(MessageFormat::Human),
                        Some("short") => Some(MessageFormat::Short),
                        Some("json") => Some(MessageFormat::Json),
                        _ => {
                            invalid_options = true;
                            None
                        }
                    };
                } else {
                    explicit_locale = Some(value);
                }
            } else if argument == "build" && !entry_seen && !build {
                build = true;
                program_arguments.push(argument);
            } else if !entry_seen
                && (argument == "--root"
                    || build
                        && matches!(
                            argument.to_str(),
                            Some(
                                "--output"
                                    | "--target"
                                    | "--cargo-target-dir"
                                    | "--native-static"
                                    | "--native-shared"
                            )
                        ))
            {
                program_arguments.push(argument);
                // Program option values belong to their command parser, even
                // when they resemble a diagnostic option.
                if let Some(specification) = arguments.next() {
                    program_arguments.push(specification);
                }
            } else {
                if !argument.as_encoded_bytes().starts_with(b"--") {
                    entry_seen = true;
                }
                program_arguments.push(argument);
            }
        }
        invalid_options |= format_count > 1 || locale_count > 1;
        let environment_locale = environment
            .into_iter()
            .flatten()
            .find(|value| !value.is_empty());
        let locale_name = if locale_count == 1 {
            explicit_locale.or(environment_locale)
        } else {
            environment_locale
        };
        Self {
            format: if format_count == 1 {
                format.unwrap_or_default()
            } else {
                MessageFormat::Human
            },
            locale: Locale::from_name(
                locale_name
                    .as_deref()
                    .and_then(|name| name.to_str())
                    .unwrap_or(""),
            ),
            program_arguments,
            invalid_options,
        }
    }
}
