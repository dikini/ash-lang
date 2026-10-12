use ash::diagnostic_options::{DiagnosticOptions, MessageFormat};
use ash::message::Locale;
use std::ffi::OsString;

fn options(arguments: &[&str], environment: [Option<&str>; 3]) -> DiagnosticOptions {
    DiagnosticOptions::parse(
        arguments.iter().map(OsString::from),
        environment.map(|s| s.map(OsString::from)),
    )
}

#[test]
fn diagnostic_defaults_and_explicit_options_follow_the_accepted_precedence() {
    for (arguments, environment, format, locale) in [
        (
            vec!["entry.ash"],
            [None, None, None],
            MessageFormat::Human,
            Locale::English,
        ),
        (
            vec!["entry.ash"],
            [Some(""), Some("bg_BG.UTF-8"), Some("en")],
            MessageFormat::Human,
            Locale::Bulgarian,
        ),
        (
            vec!["entry.ash"],
            [Some("C"), Some("bg"), Some("bg")],
            MessageFormat::Human,
            Locale::English,
        ),
        (
            vec!["entry.ash"],
            [None, Some(""), Some("bg-BG")],
            MessageFormat::Human,
            Locale::Bulgarian,
        ),
        (
            vec!["--message-format", "json", "--locale", "en", "entry.ash"],
            [Some("bg"), None, None],
            MessageFormat::Json,
            Locale::English,
        ),
        (
            vec!["--locale", "bg", "--message-format", "short", "entry.ash"],
            [Some("C"), None, None],
            MessageFormat::Short,
            Locale::Bulgarian,
        ),
    ] {
        let selected = options(&arguments, environment);
        assert!(!selected.invalid_options);
        assert_eq!(selected.format, format);
        assert_eq!(selected.locale, locale);
        assert_eq!(selected.program_arguments, [OsString::from("entry.ash")]);
    }
}

#[test]
fn invocation_errors_keep_format_selection_independent_of_early_parse_errors() {
    for arguments in [
        vec!["--bad", "build", "--message-format", "json", "entry.ash"],
        vec!["--bad", "--message-format", "json", "entry.ash"],
        vec!["--message-format", "json", "--bad", "entry.ash"],
        vec![
            "--root",
            "bad-root",
            "--message-format",
            "json",
            "entry.ash",
        ],
        vec![
            "--message-format",
            "json",
            "--root",
            "bad-root",
            "entry.ash",
        ],
    ] {
        let selected = options(&arguments, [None; 3]);
        assert_eq!(selected.format, MessageFormat::Json);
        // Ordinary invocation/root validation remains with the program parser.
        assert!(!selected.invalid_options);
    }
    for arguments in [
        vec!["--message-format"],
        vec!["--message-format", "yaml", "entry.ash"],
        vec![
            "--message-format",
            "json",
            "--message-format",
            "json",
            "entry.ash",
        ],
        vec![
            "--message-format",
            "yaml",
            "--message-format",
            "json",
            "entry.ash",
        ],
        vec!["entry.ash", "--message-format", "json"],
    ] {
        let selected = options(&arguments, [None; 3]);
        assert!(selected.invalid_options);
        assert_eq!(selected.format, MessageFormat::Human);
    }
}

#[test]
fn locale_fallback_is_independent_of_invalid_or_duplicate_options() {
    for name in ["", "C", "POSIX", "C.UTF-8", "not a locale", "zz"] {
        let selected = options(&["--locale", name, "entry.ash"], [Some("bg"); 3]);
        assert_eq!(selected.locale, Locale::English);
        assert!(!selected.invalid_options);
    }
    for arguments in [
        vec!["--locale", "bg", "--message-format", "bad", "entry.ash"],
        vec!["--message-format", "bad", "--locale", "bg", "entry.ash"],
    ] {
        let selected = options(&arguments, [Some("C"); 3]);
        assert_eq!(selected.locale, Locale::Bulgarian);
        assert!(selected.invalid_options);
    }
    for arguments in [
        vec!["--locale"],
        vec!["--locale", "bg", "--locale", "en", "entry.ash"],
    ] {
        assert!(options(&arguments, [None; 3]).invalid_options);
    }
}

#[test]
fn roots_and_entry_arguments_are_preserved_and_option_operands_are_not_reparsed() {
    let selected = options(
        &["--root", "lib=path", "--locale", "bg", "entry.ash"],
        [None, None, None],
    );
    assert_eq!(
        selected.program_arguments,
        ["--root", "lib=path", "entry.ash"].map(OsString::from)
    );
    let selected = options(&["--root", "--locale", "entry.ash"], [None; 3]);
    assert_eq!(
        selected.program_arguments,
        ["--root", "--locale", "entry.ash"].map(OsString::from)
    );
    assert_eq!(selected.locale, Locale::English);
}

#[test]
fn missing_or_misplaced_options_do_not_hide_an_independent_valid_selection() {
    for arguments in [
        vec!["--locale", "--message-format", "json", "entry.ash"],
        vec!["--message-format", "json", "--locale"],
        vec!["--message-format", "json", "entry.ash", "--locale", "en"],
        vec![
            "--message-format",
            "json",
            "entry.ash",
            "--message-format",
            "short",
        ],
    ] {
        let selected = options(&arguments, [Some("bg"), None, None]);
        assert!(selected.invalid_options);
        assert_eq!(selected.format, MessageFormat::Json);
        assert_eq!(selected.locale, Locale::Bulgarian);
    }
    for arguments in [
        vec!["--locale", "bg", "--locale", "en", "entry.ash"],
        vec!["--locale", "en", "--locale", "bg", "entry.ash"],
    ] {
        let selected = options(&arguments, [Some("bg"), None, None]);
        assert!(selected.invalid_options);
        assert_eq!(selected.locale, Locale::Bulgarian);
    }
}

#[cfg(unix)]
#[test]
fn non_utf8_values_preserve_paths_and_use_english_locale_fallback() {
    use std::os::unix::ffi::OsStringExt;
    let malformed = OsString::from_vec(vec![0xff]);
    let selected = DiagnosticOptions::parse(
        [
            OsString::from("--locale"),
            malformed.clone(),
            malformed.clone(),
        ],
        [Some(OsString::from("bg")), None, None],
    );
    assert_eq!(selected.locale, Locale::English);
    assert!(!selected.invalid_options);
    assert_eq!(selected.program_arguments, std::slice::from_ref(&malformed));
    let selected = DiagnosticOptions::parse(
        [OsString::from("entry.ash")],
        [Some(malformed.clone()), Some(OsString::from("bg")), None],
    );
    assert_eq!(selected.locale, Locale::English);
    let selected = DiagnosticOptions::parse(
        [
            OsString::from("--message-format"),
            malformed,
            OsString::from("entry.ash"),
        ],
        [None, None, None],
    );
    assert!(selected.invalid_options);
    assert_eq!(selected.format, MessageFormat::Human);
}
