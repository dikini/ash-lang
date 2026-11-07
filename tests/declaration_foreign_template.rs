use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{PipelineFailure, RunConfiguration, compile_path, execute},
    lexer::lex,
    module::ModuleRoots,
    parser::{parse, project_module},
    source::SourceFile,
};

static IDS: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new(source: &str) -> Self {
        loop {
            let id = IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-foreign-template-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => {
                    fs::write(path.join("entry.ash"), source).unwrap();
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("foreign template fixture: {error}"),
            }
        }
    }

    fn configuration(&self) -> RunConfiguration {
        RunConfiguration {
            entry: self.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn fixed_template() -> &'static str {
    let forms = include_str!("../docs/design/macros/fixtures/declarations/forms.ash");
    let start = forms
        .find("pub syntax declaration: (make_foreign)")
        .unwrap();
    let end = forms[start..]
        .find("\npub syntax declaration: (make_identity)")
        .unwrap();
    &forms[start..start + end]
}

fn entry(template: &str) -> String {
    format!("import @builtin.foreign as F\n\n{template}\nmain : Unit -> Int\nmain () = 42\n")
}

fn admits_template(template: &str) {
    let fixture = Fixture::new(&entry(template));
    let program = compile_path(fixture.configuration()).expect("template should be admitted");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn fixed_public_foreign_template_is_admitted() {
    admits_template(fixed_template());
}

#[test]
fn nonpublic_foreign_template_is_admitted() {
    let template = fixed_template().replacen("pub foreign library $L", "foreign library $L", 1);
    assert_ne!(template, fixed_template());
    admits_template(&template);
}

#[test]
fn library_placeholder_is_admitted_with_literal_symbol() {
    for visibility in ["", "pub "] {
        let template = fixed_template().replacen(
            "pub foreign library $L",
            &format!("{visibility}foreign library $L"),
            1,
        );
        admits_template(&template.replacen("symbol $S :", "symbol Make :", 1));
    }
}

#[test]
fn symbol_placeholder_is_admitted_with_literal_library() {
    for visibility in ["", "pub "] {
        let template = fixed_template().replacen(
            "pub foreign library $L",
            &format!("{visibility}foreign library $L"),
            1,
        );
        admits_template(&template.replacen("library $L {", "library Fixture {", 1));
    }
}

#[test]
fn lowercase_foreign_names_remain_invalid() {
    for visibility in ["", "pub "] {
        for (library, symbol) in [("lower", "Make"), ("Fixture", "lower")] {
            let text = format!(
                "{visibility}foreign library {library} {{\n    profile \"x86_64-unknown-linux-gnu\"\n    symbol {symbol} : Unit -> Unit {{ name \"fixture_make\" }}\n}}\n"
            );
            let source = SourceFile::new("lowercase.ash", text).unwrap();
            let tree = parse(lex(&source).unwrap());
            assert!(!tree.parse_diagnostics().is_empty());
            assert!(project_module(&source, &tree).is_err());
        }

        let template = fixed_template().replacen(
            "pub foreign library $L",
            &format!("{visibility}foreign library $L"),
            1,
        );
        for invalid in [
            template.replacen("library $L {", "library lower {", 1),
            template.replacen("symbol $S :", "symbol lower :", 1),
        ] {
            let fixture = Fixture::new(&entry(&invalid));
            let failure =
                compile_path(fixture.configuration()).expect_err("lowercase foreign name");
            assert!(matches!(
                failure.pipeline_failure(),
                Some(PipelineFailure::Syntax(_))
            ));
        }
    }
}
