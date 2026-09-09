use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

mod support;

use ash::{
    driver::{PipelineFailure, RunConfiguration, SyntaxFailure, run_path},
    elaborate::{TypeError, TypeReason, check_module},
    interface::InterfaceReason,
    kind::{KindExpectation, KindFailure, KindReason},
    lexer::lex,
    module::{LoadGraphError, LoadedModule, ModuleGraph, ModuleRoots, load_module_graph},
    parser::{
        ParseContext, ParseReason, ProjectionError, SynchronizationBoundary, parse, project_module,
    },
    render,
    resolve::{ResolveError, ResolveModuleError, ResolveReason, resolve_module},
    resolved::{
        ResolvedBinding, ResolvedBlock, ResolvedDefinitionKind, ResolvedExpr, ResolvedExprKind,
        ResolvedLocalDeclaration, ResolvedModule,
    },
    source::SourceFile,
    types::Kind,
};
use support::run_module;

const P002: &str = "main : Unit -> Int\nmain () = (41\n";
const P003: &str =
    "fn increment(value : Int) -> Int {\n    value +\n}\n\nmain : Unit -> Int\nmain () = (41\n";
const R001: &str = include_str!("fixtures/first-stratum/resolve/r001-unknown-name.ash");
const R002: &str = include_str!("fixtures/first-stratum/resolve/r002-duplicate-global.ash");
const EQUATION_NAME_MISMATCH: &str =
    include_str!("fixtures/first-stratum/resolve/equation-name-mismatch.ash");
const T001: &str = include_str!("fixtures/first-stratum/type/t001-definition-result.ash");
const T002: &str = include_str!("fixtures/first-stratum/type/t002-operator-operand.ash");
const T003: &str = include_str!("fixtures/first-stratum/type/t003-not-applicable.ash");
const T004: &str = include_str!("fixtures/first-stratum/type/t004-argument.ash");
const EQUATION_INTERFACE_NOT_FUNCTION: &str =
    include_str!("fixtures/first-stratum/type/equation-interface-not-function.ash");
const BINDING_INITIALIZER: &str =
    include_str!("fixtures/first-stratum/type/binding-initializer.ash");
const FUNCTION_NEEDS_CONTEXT: &str =
    include_str!("fixtures/first-stratum/type/function-needs-context.ash");
const FUNCTION_RESULT_NEEDS_CONTEXT: &str =
    include_str!("fixtures/first-stratum/type/function-result-needs-context.ash");
const FUNCTION_NON_FUNCTION_CONTEXT: &str =
    include_str!("fixtures/first-stratum/type/function-non-function-context.ash");

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct ModuleFixture {
    directory: PathBuf,
    graph: ModuleGraph,
}

impl ModuleFixture {
    fn load(name: &str, text: &str) -> Self {
        let directory = loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "ash-diagnostics-module-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&path) {
                Ok(()) => break path,
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("diagnostic fixture directory should be creatable: {error}"),
            }
        };
        let path = directory.join(name);
        fs::write(&path, text).expect("diagnostic fixture should be writable");
        let graph = load_module_graph(&path, &ModuleRoots::empty())
            .expect("diagnostic fixture module should load");
        Self { directory, graph }
    }

    fn loaded(&self) -> &LoadedModule {
        self.graph
            .modules()
            .iter()
            .find(|module| module.id() == self.graph.entry())
            .expect("entry module should remain loaded")
    }

    fn resolve(&self) -> ResolvedModule {
        let loaded = self.loaded();
        assert!(loaded.dependencies().is_empty());
        resolve_module(loaded, &[]).expect("diagnostic fixture should resolve")
    }
}

impl Drop for ModuleFixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}

fn source(name: &str, text: &str) -> SourceFile {
    SourceFile::new(name, text).expect("diagnostic fixture should fit the source model")
}

fn offset(value: usize) -> u32 {
    u32::try_from(value).expect("fixture offset should fit the source representation")
}

fn expect_resolution_error(error: ResolveModuleError) -> ResolveError {
    match error {
        ResolveModuleError::Resolution(error) => error,
        ResolveModuleError::Kind(error) => {
            panic!("resolution diagnostic fixture unexpectedly reached kind checking: {error:?}")
        }
    }
}

fn binding(block: &ResolvedBlock, index: usize) -> &ResolvedBinding {
    let ResolvedLocalDeclaration::Binding(binding) = &block.declarations[index] else {
        panic!("expected ordinary binding")
    };
    binding
}

fn main_body(module: &ResolvedModule) -> &ResolvedExpr {
    module
        .definitions()
        .iter()
        .find_map(|definition| match &definition.kind {
            ResolvedDefinitionKind::Equational(definition)
                if definition.interface.name.spelling == "main" =>
            {
                Some(
                    &definition
                        .equations
                        .first()
                        .expect("main should have an equation")
                        .body,
                )
            }
            ResolvedDefinitionKind::Equational(_)
            | ResolvedDefinitionKind::InlineOperational(_) => None,
        })
        .expect("fixture should declare equational main")
}

fn failure(name: &str, text: &str) -> PipelineFailure {
    run_module(name, text).expect_err("diagnostic fixture should be rejected")
}

#[test]
fn unresolved_term_retains_its_spelling_independently_of_legacy_prose() {
    let PipelineFailure::Resolution(error) = failure("unknown-term.ash", R001) else {
        panic!("the missing term must fail during resolution");
    };
    assert_eq!(error.reason, ResolveReason::UnknownName);
    assert_eq!(error.found.as_deref(), Some("missing"));
}

#[test]
fn unknown_name_presentation_distinguishes_terms_from_effect_operations() {
    use ash::{
        message::{Catalogue, Locale},
        presentation::{compile_resolve_diagnostic, write_json, write_short},
    };
    for (text, scope, english, bulgarian) in [
        (
            R001,
            "term",
            "No term named `missing` is in scope.",
            "Няма име `missing` за стойност в текущия обхват.",
        ),
        (
            "effect E {\nrun : Unit -> Unit\n}\nprobe : Unit -> Unit ! {E}\nprobe () = perform E.missing ()\n",
            "effect-operation",
            "The selected effect declares no operation named `missing`.",
            "Избраният ефект не декларира операция с име `missing`.",
        ),
    ] {
        let fixture = ModuleFixture::load("unknown.ash", text);
        let ResolveModuleError::Resolution(error) =
            resolve_module(fixture.loaded(), &[]).unwrap_err()
        else {
            panic!("expected resolution failure");
        };
        assert_eq!(error.found.as_deref(), Some("missing"));
        let diagnostic = compile_resolve_diagnostic(&error, &[fixture.loaded().source()]).unwrap();
        for (locale, expected) in [(Locale::English, english), (Locale::Bulgarian, bulgarian)] {
            let mut output = Vec::new();
            write_short(&mut output, &diagnostic, &Catalogue::new(locale).unwrap()).unwrap();
            assert!(String::from_utf8(output).unwrap().contains(expected));
        }
        let mut output = Vec::new();
        write_json(&mut output, &diagnostic).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["reason"], "resolve.unknown-name");
        assert_eq!(
            json["facts"],
            serde_json::json!([
                {"name":"name", "kind":"identifier", "value":"missing"},
                {"name":"lookup_scope", "kind":"lookup-scope", "value":scope},
            ])
        );
        assert_eq!(json["labels"][0]["relationship"], "unresolved_name");
    }
}

#[test]
fn unknown_type_presentation_retains_the_actual_parameter_scope() {
    use ash::{
        message::{Catalogue, Locale},
        presentation::{compile_resolve_diagnostic, write_json, write_short},
    };
    for (text, scope, en, bg) in [
        (
            "type Wrapped<A> = Wrapped(Missing)\n",
            "type",
            "No type named `Missing` is in scope.",
            "Няма тип с име `Missing` в текущия обхват.",
        ),
        (
            "probe<A> : A -> Unit ! {| Missing}\nprobe value = ()\n",
            "effect-row-parameter",
            "No effect-row parameter named `Missing` is in scope.",
            "Няма параметър за ред от ефекти с име `Missing` в текущия обхват.",
        ),
        (
            "fn probe(value : Unit) -> Unit ! {| Missing} {\n()\n}\n",
            "effect-row-parameter",
            "No effect-row parameter named `Missing` is in scope.",
            "Няма параметър за ред от ефекти с име `Missing` в текущия обхват.",
        ),
        (
            "interface Relation<A, B> where Missing -> B {\nrelate : A -> B\n}\n",
            "interface-parameter",
            "The owning interface has no parameter named `Missing`.",
            "Интерфейсът собственик няма параметър с име `Missing`.",
        ),
    ] {
        let fixture = ModuleFixture::load("unknown-type.ash", text);
        let ResolveModuleError::Resolution(error) =
            resolve_module(fixture.loaded(), &[]).unwrap_err()
        else {
            panic!("expected resolution failure");
        };
        assert_eq!(error.reason, ResolveReason::UnknownType);
        let diagnostic = compile_resolve_diagnostic(&error, &[fixture.loaded().source()]).unwrap();
        for (locale, expected) in [(Locale::English, en), (Locale::Bulgarian, bg)] {
            let mut output = Vec::new();
            write_short(&mut output, &diagnostic, &Catalogue::new(locale).unwrap()).unwrap();
            assert!(String::from_utf8(output).unwrap().contains(expected));
        }
        let mut output = Vec::new();
        write_json(&mut output, &diagnostic).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(
            json["facts"],
            serde_json::json!([
                {"name":"name", "kind":"identifier", "value":"Missing"},
                {"name":"lookup_scope", "kind":"lookup-scope", "value":scope},
            ])
        );
    }
}

#[test]
fn remaining_lookup_scopes_render_from_driver_retained_facts() {
    use ash::{
        message::{Catalogue, Locale},
        presentation::{compile_resolve_diagnostic, write_json, write_short},
    };
    for (text, reason, scope, english) in [
        (
            "main : Unit -> Int\nmain () = Missing\n",
            ResolveReason::UnknownConstructor,
            "constructor",
            "No constructor named `Missing` is in scope.",
        ),
        (
            "impl Missing<Int> {\n}\n",
            ResolveReason::UnknownInterface,
            "interface",
            "No interface named `Missing` is in scope.",
        ),
        (
            "probe : Unit -> Unit ! {Missing}\nprobe () = ()\n",
            ResolveReason::UnknownEffect,
            "effect",
            "No effect named `Missing` is in scope.",
        ),
        (
            "import @builtin.cell as Cell\nprobe : Unit -> Unit ! {Cell.Missing}\nprobe () = ()\n",
            ResolveReason::UnknownEffect,
            "exported-effect",
            "The selected module exports no effect named `Missing`.",
        ),
    ] {
        let fixture = ModuleFixture::load("lookup.ash", text);
        let failure = run_path(RunConfiguration {
            entry: fixture.loaded().canonical_path().to_path_buf(),
            roots: ModuleRoots::empty(),
        })
        .unwrap_err();
        let Some(PipelineFailure::Resolution(error)) = failure.pipeline_failure() else {
            panic!("expected resolution failure: {failure:?}");
        };
        assert_eq!(error.reason, reason);
        let sources: Vec<_> = failure.sources().iter().collect();
        let diagnostic = compile_resolve_diagnostic(error, &sources).unwrap();
        for locale in [Locale::English, Locale::Bulgarian] {
            let mut output = Vec::new();
            write_short(&mut output, &diagnostic, &Catalogue::new(locale).unwrap()).unwrap();
            let text = String::from_utf8(output).unwrap();
            if locale == Locale::English {
                assert!(text.contains(english));
            } else {
                assert!(text.contains("`Missing`"));
            }
        }
        let mut output = Vec::new();
        write_json(&mut output, &diagnostic).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["facts"][0]["value"], "Missing");
        assert_eq!(json["facts"][1]["value"], scope);
    }
}

#[test]
fn duplicate_declarations_render_names_and_original_locations() {
    use ash::{
        message::{Catalogue, Locale},
        presentation::{compile_resolve_diagnostic, write_human, write_json},
    };
    for (text, reason, name, english) in [
        (
            R002,
            ResolveReason::DuplicateGlobal,
            "value",
            "The name `value` is already declared in this scope.",
        ),
        (
            "effect Read {\nread : Unit -> Int\nread : Unit -> Int\n}\n",
            ResolveReason::DuplicateGlobal,
            "read",
            "The name `read` is already declared in this scope.",
        ),
        (
            "type Thing = First\ntype Thing = Second\n",
            ResolveReason::DuplicateType,
            "Thing",
            "The name `Thing` is already used by a type, interface, or effect.",
        ),
        (
            "type Equal = Equal\ninterface Equal<A> {\nequal : (A, A) -> Bool\n}\n",
            ResolveReason::DuplicateType,
            "Equal",
            "The name `Equal` is already used by a type, interface, or effect.",
        ),
        (
            "interface Equal<A> {\nequal : (A, A) -> Bool\n}\nequal : Unit -> Bool\nequal () = true\n",
            ResolveReason::DuplicateGlobal,
            "equal",
            "The name `equal` is already declared in this scope.",
        ),
        (
            "equal : Unit -> Bool\nequal () = true\ninterface Equal<A> {\nequal : (A, A) -> Bool\n}\n",
            ResolveReason::DuplicateGlobal,
            "equal",
            "The name `equal` is already declared in this scope.",
        ),
        (
            "type One = Same\ntype Two = Same\n",
            ResolveReason::DuplicateConstructor,
            "Same",
            "The constructor `Same` is already declared.",
        ),
        (
            "import @builtin.cell as Cell\nimport @builtin.cell as Cell\n",
            ResolveReason::DuplicateModuleAlias,
            "Cell",
            "The module alias `Cell` is already bound.",
        ),
        (
            "type Pair<A, A> = Pair(Int, Int)\n",
            ResolveReason::DuplicateTypeParameter,
            "A",
            "The type parameter `A` is already declared in this scope.",
        ),
        (
            "interface Bad<A, A> {\nbad : A -> A\n}\n",
            ResolveReason::DuplicateTypeParameter,
            "A",
            "The type parameter `A` is already declared in this scope.",
        ),
        (
            "interface Bad<A> {\nbad<A> : A -> A\n}\n",
            ResolveReason::DuplicateTypeParameter,
            "A",
            "The type parameter `A` is already declared in this scope.",
        ),
        (
            "interface Bad<A> {\nbad<B, B> : (A, B) -> B\n}\n",
            ResolveReason::DuplicateTypeParameter,
            "B",
            "The type parameter `B` is already declared in this scope.",
        ),
        (
            "main : Unit -> Int\nmain () = {\nlet (value, value) = (1, 2)\nvalue\n}\n",
            ResolveReason::DuplicatePatternBinder,
            "value",
            "The pattern binds `value` more than once.",
        ),
        (
            "main : Unit -> Int\nmain () = {\nlet rec same : Unit -> Int = fn(value) {\n1\n}\nand same : Unit -> Int = fn(value) {\n2\n}\nsame ()\n}\n",
            ResolveReason::DuplicateRecursiveMember,
            "same",
            "The recursive group defines `same` more than once.",
        ),
    ] {
        let fixture = ModuleFixture::load("duplicate.ash", text);
        let failure = run_path(RunConfiguration {
            entry: fixture.loaded().canonical_path().to_path_buf(),
            roots: ModuleRoots::empty(),
        })
        .unwrap_err();
        let Some(PipelineFailure::Resolution(error)) = failure.pipeline_failure() else {
            panic!("expected resolution failure: {failure:?}");
        };
        assert_eq!(error.reason, reason);
        assert_eq!(error.found.as_deref(), Some(name));
        let sources: Vec<_> = failure.sources().iter().collect();
        let diagnostic = compile_resolve_diagnostic(error, &sources).unwrap();
        for locale in [Locale::English, Locale::Bulgarian] {
            let mut output = Vec::new();
            write_human(&mut output, &diagnostic, &Catalogue::new(locale).unwrap()).unwrap();
            let output = String::from_utf8(output).unwrap();
            assert!(output.contains(&format!("`{name}`")));
            if locale == Locale::English {
                assert!(output.contains(english), "{output}");
                assert!(output.contains("First declaration of this name."));
            } else {
                assert!(output.contains("Първа декларация на това име."));
            }
        }
        let mut output = Vec::new();
        write_json(&mut output, &diagnostic).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["facts"][0]["value"], name);
        let labels = json["labels"].as_array().unwrap();
        assert_eq!(labels.len(), error.related.len() + 1);
        assert_eq!(labels[0]["relationship"], "duplicate_name");
        assert_eq!(labels[1]["relationship"], "first_declaration");
        for (rendered, original) in labels
            .iter()
            .zip(std::iter::once(&error.primary).chain(&error.related))
        {
            assert_eq!(rendered["byte_start"], original.span().range().start());
            assert_eq!(rendered["byte_end"], original.span().range().end());
            assert_eq!(rendered["facts"][0]["value"], name);
        }
        if labels.len() == 3 {
            assert_eq!(labels[2]["relationship"], "first_definition");
        }
        assert!(compile_resolve_diagnostic(error, &[]).is_err());
    }
}

#[test]
fn declaration_name_requirements_render_retained_facts() {
    use ash::{
        message::{Catalogue, Locale},
        presentation::{compile_resolve_diagnostic, write_human, write_json},
    };
    for (text, reason, name, expected, english) in [
        (
            "value : Unit -> Int\nother () = 1\n",
            ResolveReason::EquationNameMismatch,
            "other",
            Some("value"),
            "The equation is named `other`, but its signature declares `value`. Rename the equation to `value`.",
        ),
        (
            "newtype Wrapper = Other(Int)\n",
            ResolveReason::NewtypeConstructorName,
            "Other",
            Some("Wrapper"),
            "The constructor is named `Other`, but this newtype requires `Wrapper`.",
        ),
        (
            "interface Bad<A> {\nbad<B, C> : (A, B) -> B\n}\n",
            ResolveReason::UnusedTypeParameter,
            "C",
            None,
            "The explicit type parameter `C` is not used in the declaration header.",
        ),
        (
            "import @builtin.cell as Cell\ntype Cell = Make\n",
            ResolveReason::ImportConflict,
            "Cell",
            None,
            "The name `Cell` conflicts with a binding already in scope for this file.",
        ),
    ] {
        let fixture = ModuleFixture::load("name-requirement.ash", text);
        let failure = run_path(RunConfiguration {
            entry: fixture.loaded().canonical_path().to_path_buf(),
            roots: ModuleRoots::empty(),
        })
        .unwrap_err();
        let Some(PipelineFailure::Resolution(error)) = failure.pipeline_failure() else {
            panic!("{failure:?}")
        };
        assert_eq!(error.reason, reason);
        assert_eq!(error.found.as_deref(), Some(name));
        assert_eq!(error.expected.as_deref(), expected);
        let sources: Vec<_> = failure.sources().iter().collect();
        let diagnostic = compile_resolve_diagnostic(error, &sources).unwrap();
        for locale in [Locale::English, Locale::Bulgarian] {
            let mut output = Vec::new();
            write_human(&mut output, &diagnostic, &Catalogue::new(locale).unwrap()).unwrap();
            let output = String::from_utf8(output).unwrap();
            assert!(output.contains(&format!("`{name}`")));
            if locale == Locale::English {
                assert!(output.contains(english), "{output}");
            }
            if let Some(expected) = expected {
                assert!(output.contains(&format!("`{expected}`")));
            }
        }
        let mut output = Vec::new();
        write_json(&mut output, &diagnostic).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["facts"][0]["value"], name);
        assert_eq!(
            json["labels"].as_array().unwrap().len(),
            error.related.len() + 1
        );
        if let Some(expected) = expected {
            assert_eq!(json["facts"][1]["name"], "expected_name");
            assert_eq!(json["facts"][1]["value"], expected);
            assert_eq!(
                json["labels"][1]["relationship"],
                "required_name_declaration"
            );
            assert_eq!(json["labels"][1]["facts"][0]["value"], expected);
        }
    }
}

fn occurrence_range(text: &str, needle: &str, occurrence: usize) -> (u32, u32) {
    let start = text
        .match_indices(needle)
        .nth(occurrence)
        .map(|(start, _)| start)
        .unwrap_or_else(|| {
            panic!("the diagnostic fixture should contain occurrence {occurrence} of {needle:?}")
        });
    (offset(start), offset(start + needle.len()))
}

#[derive(Clone, Copy)]
enum KindExpectationShape {
    Type,
    TypeConstructor,
    ApplicableToType,
}

struct KindDiagnosticCase {
    name: &'static str,
    source: String,
    reason: KindReason,
    primary: (&'static str, usize),
    primary_message: &'static str,
    related: (&'static str, usize),
    related_message: &'static str,
    expectation: KindExpectationShape,
}

fn assert_public_kind_diagnostic(case: &KindDiagnosticCase) {
    let fixture = ModuleFixture::load(case.name, &case.source);
    let failure = run_path(RunConfiguration {
        entry: fixture.loaded().canonical_path().to_path_buf(),
        roots: ModuleRoots::empty(),
    })
    .unwrap_err();
    let Some(PipelineFailure::Kind(KindFailure::Source(error))) = failure.pipeline_failure() else {
        panic!("{} should fail at the public kind boundary", case.name);
    };
    let diagnostic = error.diagnostic();

    assert_eq!(diagnostic.reason, case.reason, "case: {}", case.name);
    assert_eq!(
        (
            diagnostic.primary.span().range().start(),
            diagnostic.primary.span().range().end(),
        ),
        occurrence_range(&case.source, case.primary.0, case.primary.1),
        "primary span: {}",
        case.name,
    );
    assert_eq!(
        diagnostic.primary.message(),
        case.primary_message,
        "primary message: {}",
        case.name,
    );
    assert_eq!(diagnostic.related.len(), 1, "case: {}", case.name);
    assert_eq!(
        (
            diagnostic.related[0].span().range().start(),
            diagnostic.related[0].span().range().end(),
        ),
        occurrence_range(&case.source, case.related.0, case.related.1),
        "related span: {}",
        case.name,
    );
    assert_eq!(
        diagnostic.related[0].message(),
        case.related_message,
        "related message: {}",
        case.name,
    );

    match case.expectation {
        KindExpectationShape::Type => {
            assert_eq!(error.expectation(), &KindExpectation::Exact(Kind::Type));
            assert_eq!(
                error.found_kind(),
                Some(&Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)))
            );
            assert_eq!(diagnostic.expected.as_deref(), Some("Type"));
            assert_eq!(diagnostic.found.as_deref(), Some("Type -> Type"));
        }
        KindExpectationShape::TypeConstructor => {
            let constructor = Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
            assert_eq!(error.expectation(), &KindExpectation::Exact(constructor));
            assert_eq!(error.found_kind(), Some(&Kind::Type));
            assert_eq!(diagnostic.expected.as_deref(), Some("Type -> Type"));
            assert_eq!(diagnostic.found.as_deref(), Some("Type"));
        }
        KindExpectationShape::ApplicableToType => {
            assert_eq!(
                error.expectation(),
                &KindExpectation::Function { domain: Kind::Type }
            );
            assert_eq!(error.found_kind(), Some(&Kind::Type));
            assert_eq!(diagnostic.expected.as_deref(), Some("Type -> _"));
            assert_eq!(diagnostic.found.as_deref(), Some("Type"));
        }
    }
    use ash::{
        message::{Catalogue, Locale},
        presentation::{compile_kind_diagnostic, write_human, write_json},
    };
    let sources: Vec<_> = failure.sources().iter().collect();
    let view = compile_kind_diagnostic(error, &sources).unwrap();
    for locale in [Locale::English, Locale::Bulgarian] {
        let mut output = Vec::new();
        write_human(&mut output, &view, &Catalogue::new(locale).unwrap()).unwrap();
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains(&format!("`{}`", diagnostic.found.as_deref().unwrap())));
        if locale == Locale::English {
            let expected = diagnostic.expected.as_deref().unwrap();
            let found = diagnostic.found.as_deref().unwrap();
            let title = match case.reason {
                KindReason::ExpectedType => format!(
                    "This position requires a complete value type (kind `Type`), but has kind `{found}`."
                ),
                KindReason::NotApplicable => {
                    format!("The applied type has kind `{found}` and cannot take type arguments.")
                }
                KindReason::Argument => {
                    format!("This argument needs kind `{expected}`, but has kind `{found}`.")
                }
            };
            assert!(output.contains(&title), "{output}");
        }
    }
    let mut output = Vec::new();
    write_json(&mut output, &view).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(json["facts"][0]["name"], "expected_kind");
    assert_eq!(
        json["facts"][0]["value"],
        diagnostic.expected.as_deref().unwrap()
    );
    assert_eq!(json["facts"][1]["name"], "found_kind");
    assert_eq!(
        json["facts"][1]["value"],
        diagnostic.found.as_deref().unwrap()
    );
    assert_eq!(
        json["facts"][2]["value"],
        if case.reason == KindReason::NotApplicable {
            "function"
        } else {
            "exact"
        }
    );
    assert_eq!(
        json["labels"][1]["relationship"],
        if case.reason == KindReason::Argument {
            "required_kind_declaration"
        } else {
            "found_kind_declaration"
        }
    );
    for (label, original) in json["labels"]
        .as_array()
        .unwrap()
        .iter()
        .zip(std::iter::once(&diagnostic.primary).chain(&diagnostic.related))
    {
        assert_eq!(label["byte_start"], original.span().range().start());
        assert_eq!(label["byte_end"], original.span().range().end());
    }
    assert!(compile_kind_diagnostic(error, &[]).is_err());
}

#[test]
fn syntax_failure_reason_and_rendering_follow_source_order_across_stages() {
    let text = concat!(
        "import @ as Missing\n",
        "main : Unit -> Int\n",
        "main () = 42 #\n",
    );
    let fixture = ModuleFixture::load(
        "syntax-source-order.ash",
        "main : Unit -> Unit\nmain () = ()\n",
    );
    let entry = fixture.directory.join("syntax-source-order.ash");
    fs::write(&entry, text).expect("the syntax-order fixture should be writable");
    let file_error = run_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect_err("the module should retain both independent syntax failures");
    let Some(LoadGraphError::Syntax(syntax)) = file_error.graph_failure() else {
        panic!("the independent lexical and parser failures should retain graph syntax ownership")
    };
    let parser = syntax
        .parser
        .first()
        .expect("the malformed absolute path should retain a parser diagnostic");
    let lexical = syntax
        .lexical
        .first()
        .expect("the later unknown character should retain a lexical diagnostic");

    assert!(
        parser.primary.span().range().start() < lexical.primary.span().range().start(),
        "the fixture must place the parser cause before the lexical cause"
    );
    let pipeline_error = PipelineFailure::Syntax(Box::new(SyntaxFailure {
        lexical: syntax.lexical.clone(),
        parser: syntax.parser.clone(),
        resource: syntax.resource,
    }));
    assert!(file_error.is_source_rejection());
    assert!(pipeline_error.is_source_rejection());
    let expected = parser.reason.to_string();
    let file_rendered = render::file_failure(&file_error);
    let pipeline_rendered = render::pipeline_failure(&pipeline_error);
    let parser_position = pipeline_rendered
        .find(&expected)
        .expect("the earlier parser diagnostic should be rendered");
    let lexical_position = pipeline_rendered
        .find(&lexical.reason.to_string())
        .expect("the later lexical diagnostic should also be rendered");
    assert!(parser_position < lexical_position);
    assert_eq!(
        [
            file_error.reason_code(),
            file_rendered
                .lines()
                .next()
                .expect("file-rendered reason line")
                .to_owned(),
            pipeline_error.reason_code(),
            pipeline_rendered
                .lines()
                .next()
                .expect("pipeline-rendered reason line")
                .to_owned(),
        ],
        std::array::from_fn(|_| expected.clone()),
        "public reason selection and rendering must share source-order causality"
    );
}

#[test]
fn recursive_diagnostics_retain_exact_stage_facts() {
    let missing_member_text =
        "main : Unit -> Int\nmain () = {\nlet rec value : Int = 1\nand\nvalue\n}\n";
    let missing_member_source = source("missing-member.ash", missing_member_text);
    let missing_member = parse(lex(&missing_member_source).expect("fixture should lex"));
    let diagnostic = missing_member
        .parse_diagnostics()
        .iter()
        .find(|diagnostic| diagnostic.reason == ParseReason::ExpectedRecursiveMember)
        .expect("missing recursive member should be diagnosed");
    let boundary = missing_member_text.find("and\n").expect("and delimiter") + 3;
    assert_eq!(diagnostic.primary.span().range().start(), offset(boundary));
    assert_eq!(
        diagnostic.primary.span().range().end(),
        offset(boundary + 1)
    );
    assert_eq!(diagnostic.expected.as_deref(), Some("an identifier"));
    assert_eq!(diagnostic.found.as_deref(), Some("line end"));
    assert!(matches!(
        diagnostic.context.as_slice(),
        [ParseContext::Synchronization {
            boundary: SynchronizationBoundary::LogicalLineEnd,
            ..
        }]
    ));

    let missing_annotation_text =
        "main : Unit -> Int\nmain () = {\nlet rec value = fn(item) {\nitem\n}\nvalue\n}\n";
    let missing_annotation_source = source("missing-annotation.ash", missing_annotation_text);
    let missing_annotation = parse(lex(&missing_annotation_source).expect("fixture should lex"));
    let diagnostic = missing_annotation
        .parse_diagnostics()
        .iter()
        .find(|diagnostic| {
            diagnostic.reason == ParseReason::ExpectedForm
                && diagnostic.expected.as_deref() == Some(":")
        })
        .expect("missing annotation delimiter should be diagnosed");
    let equal = missing_annotation_text
        .find("value =")
        .expect("recursive binding")
        + "value ".len();
    assert_eq!(diagnostic.primary.span().range().start(), offset(equal));
    assert_eq!(diagnostic.found.as_deref(), Some("="));

    let stray_text = "main : Unit -> Int\nmain () = {\nand stray : Int = 1\n42\n}\n";
    let stray_source = source("stray-and.ash", stray_text);
    let stray = parse(lex(&stray_source).expect("fixture should lex"));
    let diagnostic = stray
        .parse_diagnostics()
        .iter()
        .find(|diagnostic| diagnostic.reason == ParseReason::UnexpectedAnd)
        .expect("stray and should be diagnosed");
    let stray_and = stray_text.find("and stray").expect("stray and");
    assert_eq!(diagnostic.primary.span().range().start(), offset(stray_and));
    assert_eq!(
        diagnostic.primary.span().range().end(),
        offset(stray_and + 3)
    );

    let unsafe_text = "main : Unit -> Int\nmain () = {\nlet rec value : Int = 1\nvalue\n}\n";
    let error = failure("unsafe-recursion.ash", unsafe_text);
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("expected source typing failure")
    };
    assert_eq!(diagnostic.reason, TypeReason::UnsafeRecursiveRoot);
    let initializer = unsafe_text.find("1\n").expect("initializer");
    assert_eq!(
        diagnostic.primary.span().range().start(),
        offset(initializer)
    );
    assert_eq!(diagnostic.related.len(), 2);
    assert_eq!(diagnostic.expected.as_deref(), None);
}

#[test]
fn p002_labels_the_opening_group_and_the_eof_close_requirement() {
    let source = source("p002.ash", P002);
    let tree = parse(lex(&source).expect("P-002 should lex"));

    assert_eq!(tree.parse_diagnostics().len(), 1);
    let diagnostic = &tree.parse_diagnostics()[0];
    assert_eq!(diagnostic.reason, ParseReason::UnclosedGroup);
    let opening = P002.rfind('(').expect("unclosed opening parenthesis");
    assert_eq!(diagnostic.primary.span().range().start(), offset(opening));
    assert_eq!(diagnostic.primary.span().range().end(), offset(opening + 1));
    assert_eq!(diagnostic.expected, Some(")".to_owned()));
    assert_eq!(diagnostic.found, Some("end of input".to_owned()));
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(
        diagnostic.related[0].span().range().start(),
        offset(P002.len())
    );
    assert_eq!(
        project_module(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
}

#[test]
fn p003_recovers_at_the_body_brace_then_reports_the_later_group_independently() {
    let source = source("p003.ash", P003);
    let tree = parse(lex(&source).expect("P-003 should lex"));

    assert_eq!(tree.parse_diagnostics().len(), 2);
    let operand = &tree.parse_diagnostics()[0];
    assert_eq!(operand.reason, ParseReason::ExpectedOperand);
    let operator = P003.find('+').expect("missing-operand operator");
    assert_eq!(operand.primary.span().range().start(), offset(operator));
    assert_eq!(operand.expected, Some("an operand".to_owned()));
    assert_eq!(operand.found, Some("line end".to_owned()));
    assert_eq!(operand.context.len(), 1);
    let ParseContext::Synchronization { boundary, span } = operand.context[0];
    assert_eq!(boundary, SynchronizationBoundary::BlockClosingBrace);
    assert_eq!(
        span.range().start(),
        offset(P003.find('}').expect("body closing brace"))
    );
    assert_eq!(operand.related.len(), 1);
    assert_eq!(operand.related[0].span(), span);

    let group = &tree.parse_diagnostics()[1];
    assert_eq!(group.reason, ParseReason::UnclosedGroup);
    let opening = P003.rfind('(').expect("later unclosed group");
    assert_eq!(group.primary.span().range().start(), offset(opening));
    assert_eq!(group.related.len(), 1);
    assert_eq!(group.related[0].span().range().start(), offset(P003.len()));
    assert_eq!(
        project_module(&source, &tree),
        Err(ProjectionError::RecoveryNodesPresent)
    );
}

#[test]
fn complete_declaration_without_a_logical_line_end_remains_diagnosed() {
    let text = "main : Unit -> Int\nmain () = 1";
    let source = source("missing-line-end.ash", text);
    let tree = parse(lex(&source).expect("the declaration should lex"));

    assert_eq!(tree.parse_diagnostics().len(), 1);
    let diagnostic = &tree.parse_diagnostics()[0];
    assert_eq!(diagnostic.reason, ParseReason::ExpectedForm);
    assert_eq!(
        diagnostic.primary.span().range().start(),
        offset(text.len())
    );
    assert_eq!(diagnostic.primary.span().range().end(), offset(text.len()));
    assert_eq!(diagnostic.expected.as_deref(), Some("a logical line end"));
    assert_eq!(diagnostic.found.as_deref(), Some("end of input"));
}

#[test]
fn r001_reports_only_the_unknown_occurrence_without_an_unjustified_suggestion() {
    let fixture = ModuleFixture::load("r001.ash", R001);
    let error = expect_resolution_error(
        resolve_module(fixture.loaded(), &[]).expect_err("R-001 should fail in resolution"),
    );

    assert_eq!(error.reason, ResolveReason::UnknownName);
    let missing = R001.find("missing").expect("unknown occurrence");
    assert_eq!(error.primary.span().range().start(), offset(missing));
    assert_eq!(
        error.primary.span().range().end(),
        offset(missing + "missing".len())
    );
    assert!(error.related.is_empty());
    assert!(error.expected.is_none());
    assert_eq!(error.found.as_deref(), Some("missing"));
    assert!(error.help.is_none());
}

#[test]
fn data_resolution_diagnostics_retain_names_and_binder_sites() {
    let duplicate_text =
        "type Thing =\nFirst\n\ntype Thing =\nSecond\n\nmain : Unit -> Thing\nmain () = First\n";
    let duplicate = ModuleFixture::load("duplicate-type.ash", duplicate_text);
    let error = expect_resolution_error(
        resolve_module(duplicate.loaded(), &[]).expect_err("duplicate type should fail"),
    );
    assert_eq!(error.reason, ResolveReason::DuplicateType);
    let first = duplicate_text.find("type Thing").expect("first type name") + "type ".len();
    let second = duplicate_text
        .find("type Thing =\nSecond")
        .expect("second type name")
        + "type ".len();
    assert_eq!(error.primary.span().range().start(), offset(second));
    assert_eq!(error.related.len(), 1);
    assert_eq!(error.related[0].span().range().start(), offset(first));
    assert!(error.expected.is_none() && error.help.is_none());
    assert_eq!(error.found.as_deref(), Some("Thing"));

    let binder_text = "main : Unit -> Int\nmain () = {\nlet (value, value) = (1, 2)\nvalue\n}\n";
    let binder_fixture = ModuleFixture::load("duplicate-pattern-binder.ash", binder_text);
    let error = expect_resolution_error(
        resolve_module(binder_fixture.loaded(), &[]).expect_err("duplicate binder should fail"),
    );
    assert_eq!(error.reason, ResolveReason::DuplicatePatternBinder);
    let first = binder_text.find("value").expect("first binder");
    let second = binder_text[first + 1..]
        .find("value")
        .map(|relative| relative + first + 1)
        .expect("second binder");
    assert_eq!(error.primary.span().range().start(), offset(second));
    assert_eq!(error.related.len(), 1);
    assert_eq!(error.related[0].span().range().start(), offset(first));

    let unknown_text = "main : Unit -> Unit\nmain () = Missing\n";
    let unknown = ModuleFixture::load("unknown-constructor.ash", unknown_text);
    let error = expect_resolution_error(
        resolve_module(unknown.loaded(), &[]).expect_err("unknown constructor should fail"),
    );
    assert_eq!(error.reason, ResolveReason::UnknownConstructor);
    assert_eq!(
        error.primary.span().range().start(),
        offset(unknown_text.find("Missing").expect("unknown constructor"))
    );
    assert_eq!(error.found.as_deref(), Some("Missing"));
    assert!(error.related.is_empty() && error.expected.is_none() && error.help.is_none());
}

#[test]
fn coverage_diagnostics_retain_arm_spans_and_concrete_witnesses() {
    let missing_text = "main : Unit -> Int\nmain () = match true {\ntrue => 1\n}\n";
    let missing = ModuleFixture::load("missing-case.ash", missing_text);
    let resolved = missing.resolve();
    let expected_span = main_body(&resolved).span;
    let TypeError::Source(diagnostic) = check_module(resolved).expect_err("false is uncovered")
    else {
        panic!("missing case should be a typed source diagnostic")
    };
    assert_eq!(diagnostic.reason, TypeReason::NonExhaustive);
    assert_eq!(diagnostic.primary.span(), expected_span);
    assert_eq!(diagnostic.found.as_deref(), Some("false"));
    assert!(diagnostic.related.is_empty() && diagnostic.expected.is_none());

    let redundant_text =
        "main : Unit -> Int\nmain () = match true {\ntrue => 1\nfalse => 2\nfalse => 3\n}\n";
    let redundant = ModuleFixture::load("redundant-case.ash", redundant_text);
    let resolved = redundant.resolve();
    let ResolvedExprKind::Match(match_expression) = &main_body(&resolved).kind else {
        panic!("fixture should resolve to a match")
    };
    let expected_span = match_expression.arms[2].span;
    let TypeError::Source(diagnostic) = check_module(resolved).expect_err("third arm is redundant")
    else {
        panic!("redundant case should be a typed source diagnostic")
    };
    assert_eq!(diagnostic.reason, TypeReason::RedundantCase);
    assert_eq!(diagnostic.primary.span(), expected_span);
    assert!(diagnostic.found.is_none() && diagnostic.related.is_empty());
}

#[test]
fn nominal_mismatches_render_source_declaration_spellings() {
    let declarations = "type Left =\nLeftValue\n\ntype Right =\nRightValue\n\n";
    let cases = [
        (
            "fn select(value : Left) -> Left {\nvalue\n}\n\nmain : Unit -> Left\nmain () = select RightValue\n",
            TypeReason::Argument,
        ),
        (
            "main : Unit -> Left\nmain () = {\nlet value : Left = RightValue\nvalue\n}\n",
            TypeReason::BindingInitializer,
        ),
        (
            "fn select(value : Left) -> Left {\nRightValue\n}\n\nmain : Unit -> Left\nmain () = select LeftValue\n",
            TypeReason::DefinitionResult,
        ),
    ];

    for (index, (program, reason)) in cases.into_iter().enumerate() {
        let text = format!("{declarations}{program}");
        let error = failure(&format!("nominal-mismatch-{index}.ash"), &text);
        let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
            panic!("nominal mismatch should be a typed source diagnostic")
        };

        assert_eq!(diagnostic.reason, reason);
        assert_eq!(diagnostic.expected.as_deref(), Some("Left"));
        assert_eq!(diagnostic.found.as_deref(), Some("Right"));
        assert!(!diagnostic.render_plain().contains("<type:"));
    }

    let text = format!(
        "{declarations}main : Unit -> Unit\nmain () = {{\nlet value = match true {{\ntrue => LeftValue\nfalse => RightValue\n}}\n()\n}}\n"
    );
    let error = failure("nominal-match-result.ash", &text);
    let PipelineFailure::Typing(error) = error else {
        panic!("match result mismatch should fail during typing")
    };
    assert_eq!(
        error.to_string(),
        "type mismatch: expected Left, found Right"
    );
    let TypeError::Mismatch(mismatch) = error else {
        panic!("match result mismatch should retain its structural types")
    };
    assert_ne!(mismatch.expected(), mismatch.found());
}

#[test]
fn checked_match_arms_retain_the_definition_result_cause() {
    let cases = [
        (
            "true => fn(value) {\nfalse\n}\nfalse => fn(value) {\nvalue\n}",
            "bad-first-match-arm.ash",
        ),
        (
            "true => fn(value) {\nvalue\n}\nfalse => fn(value) {\nfalse\n}",
            "bad-later-match-arm.ash",
        ),
    ];

    for (arms, name) in cases {
        let text = format!(
            "fn choose(flag : Bool) -> Int -> Int {{\nmatch flag {{\n{arms}\n}}\n}}\n\nmain : Unit -> Int\nmain () = choose true 0\n"
        );
        let bad_body = text
            .find("fn(value) {\nfalse\n}")
            .expect("bad anonymous-function body")
            + "fn(value) {\n".len();
        let declared_result =
            text.find("-> Int -> Int").expect("declared result") + "-> Int -> ".len();
        let error = failure(name, &text);
        let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
            panic!("checked match arm should retain a source diagnostic")
        };

        assert_eq!(diagnostic.reason, TypeReason::DefinitionResult);
        assert_eq!(diagnostic.primary.span().range().start(), offset(bad_body));
        assert_eq!(
            diagnostic.primary.span().range().end(),
            offset(bad_body + "false".len())
        );
        assert_eq!(diagnostic.expected.as_deref(), Some("Int"));
        assert_eq!(diagnostic.found.as_deref(), Some("Bool"));
        assert_eq!(diagnostic.related.len(), 1);
        assert_eq!(
            diagnostic.related[0].span().range().start(),
            offset(declared_result)
        );
        assert_eq!(
            diagnostic.related[0].span().range().end(),
            offset(declared_result + "Int".len())
        );
    }
}

#[test]
fn unguarded_recursive_use_retains_the_transporting_expression_span() {
    let text = "type Stream =\nNext(Int, Stream)\n\nfn identity(value : Stream) -> Stream {\nvalue\n}\n\nmain : Unit -> Stream\nmain () = {\nlet rec stream : Stream = Next(1, identity stream)\nstream\n}\n";
    let error = failure("unguarded-recursion.ash", text);
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("unguarded use should be a typed source diagnostic")
    };
    assert_eq!(diagnostic.reason, TypeReason::UnguardedRecursiveUse);
    let start = text.find("identity stream").expect("transporting call");
    assert_eq!(diagnostic.primary.span().range().start(), offset(start));
    assert_eq!(
        diagnostic.primary.span().range().end(),
        offset(start + "identity stream".len())
    );
    assert!(diagnostic.related.is_empty());
    assert!(diagnostic.expected.is_none() && diagnostic.found.is_none());
}

#[test]
fn r002_relates_the_second_global_to_the_first_name_and_definition() {
    let fixture = ModuleFixture::load("r002.ash", R002);
    let surface = fixture.loaded().surface();
    let first = &surface.definitions[0];
    let second = &surface.definitions[1];
    let error = expect_resolution_error(
        resolve_module(fixture.loaded(), &[]).expect_err("R-002 should fail in resolution"),
    );

    assert_eq!(error.reason, ResolveReason::DuplicateGlobal);
    assert_eq!(
        error.primary.span().range().start(),
        offset(R002.find("fn value").expect("second global") + 3)
    );
    assert_eq!(error.related.len(), 2);
    assert!(
        error
            .related
            .iter()
            .any(|label| label.span().range().start() == 0)
    );
    assert!(error.related.iter().any(|label| label.span() == first.span));
    assert_ne!(error.primary.span(), second.span);
    assert!(error.expected.is_none());
    assert_eq!(error.found.as_deref(), Some("value"));
}

#[test]
fn equation_name_mismatch_retains_both_names_and_a_justified_correction() {
    let fixture = ModuleFixture::load("equation-name.ash", EQUATION_NAME_MISMATCH);
    let error = expect_resolution_error(
        resolve_module(fixture.loaded(), &[]).expect_err("the equation head should disagree"),
    );

    assert_eq!(error.reason, ResolveReason::EquationNameMismatch);
    assert_eq!(error.expected.as_deref(), Some("identity"));
    assert_eq!(error.found.as_deref(), Some("different"));
    assert_eq!(error.related.len(), 1);
    assert_eq!(error.related[0].span().range().start(), 0);
    assert_eq!(
        error.help.as_deref(),
        Some("rename the equation head to `identity`")
    );
}

#[test]
fn t001_definition_result_relates_the_body_to_the_interface_codomain() {
    let error = failure("t001.ash", T001);
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("T-001 should remain a typed source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::DefinitionResult);
    assert_eq!(
        diagnostic.primary.span().range().start(),
        offset(T001.find("value\n\n").expect("equation body"))
    );
    assert_eq!(diagnostic.expected.as_deref(), Some("Bool"));
    assert_eq!(diagnostic.found.as_deref(), Some("Int"));
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(
        diagnostic.related[0].span().range().start(),
        offset(T001.find("Bool").expect("declared codomain"))
    );
}

#[test]
fn t002_operator_operand_relates_the_bool_to_the_operator() {
    let error = failure("t002.ash", T002);
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("T-002 should remain a typed source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::OperatorOperand);
    let boolean = T002.find("true").expect("Boolean operand");
    assert_eq!(diagnostic.primary.span().range().start(), offset(boolean));
    assert_eq!(diagnostic.primary.span().range().end(), offset(boolean + 4));
    assert_eq!(diagnostic.expected.as_deref(), Some("Int"));
    assert_eq!(diagnostic.found.as_deref(), Some("Bool"));
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(
        diagnostic.related[0].span().range().start(),
        offset(T002.find('+').expect("primitive operator"))
    );
}

#[test]
fn unresolved_inference_is_anonymous_in_source_type_diagnostics() {
    let operator_text =
        "type Option<A> =\nNone\n| Some(A)\n\nmain : Unit -> Int\nmain () = Some + 1\n";
    let operator = failure("inferred-operator.ash", operator_text);
    let PipelineFailure::Typing(TypeError::Source(operator)) = operator else {
        panic!("the operator rejection should remain a typed source diagnostic");
    };
    assert_eq!(operator.reason, TypeReason::OperatorOperand);
    assert_eq!(operator.expected.as_deref(), Some("Int"));
    assert_eq!(operator.found.as_deref(), Some("_ -> Option<_>"));
    assert!(!operator.render_plain().contains('?'));

    let pattern_text = "main : Unit -> Int\nmain () = {\nlet split = fn(value) {\nlet (left, right) = value\nlet () = value\nleft\n}\nsplit\n}\n";
    let pattern = failure("inferred-pattern.ash", pattern_text);
    let PipelineFailure::Typing(TypeError::Source(pattern)) = pattern else {
        panic!("the pattern rejection should remain a typed source diagnostic");
    };
    assert_eq!(pattern.reason, TypeReason::PatternMismatch);
    assert_eq!(pattern.expected.as_deref(), Some("(_, _)"));
    assert!(!pattern.render_plain().contains('?'));
}

#[test]
fn t003_not_applicable_relates_the_function_position_to_the_application() {
    let error = failure("t003.ash", T003);
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("T-003 should remain a typed source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::NotApplicable);
    let function = T003.find("41 1").expect("non-function application");
    assert_eq!(diagnostic.primary.span().range().start(), offset(function));
    assert_eq!(
        diagnostic.primary.span().range().end(),
        offset(function + 2)
    );
    assert_eq!(diagnostic.expected.as_deref(), Some("function"));
    assert_eq!(diagnostic.found.as_deref(), Some("Int"));
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(
        diagnostic.related[0].span().range().start(),
        offset(function)
    );
    assert_eq!(
        diagnostic.related[0].span().range().end(),
        offset(function + 4)
    );
}

#[test]
fn t004_argument_relates_the_argument_to_the_declared_domain() {
    let error = failure("t004.ash", T004);
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("T-004 should remain a typed source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::Argument);
    assert_eq!(
        diagnostic.primary.span().range().start(),
        offset(T004.rfind("true").expect("argument"))
    );
    assert_eq!(diagnostic.expected.as_deref(), Some("Int"));
    assert_eq!(diagnostic.found.as_deref(), Some("Bool"));
    assert!(diagnostic.related.iter().any(|label| {
        label.span().range().start() == offset(T004.find("Int").expect("declared domain"))
    }));
}

#[test]
fn annotated_binding_initializer_relates_the_expression_to_its_annotation() {
    let fixture = ModuleFixture::load("binding-initializer.ash", BINDING_INITIALIZER);
    let resolved = fixture.resolve();
    let ResolvedExprKind::Block(block) = &main_body(&resolved).kind else {
        panic!("fixture should resolve to a block");
    };
    let binding = binding(block, 0);
    let annotation = binding.annotation.as_ref().expect("binding annotation");
    let initializer_span = binding.initializer.span;
    let annotation_span = annotation.span;
    let TypeError::Source(diagnostic) =
        check_module(resolved).expect_err("the initializer should not check")
    else {
        panic!("binding mismatch should be a categorized source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::BindingInitializer);
    assert_eq!(diagnostic.primary.span(), initializer_span);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span(), annotation_span);
    assert_eq!(diagnostic.expected.as_deref(), Some("Bool"));
    assert_eq!(diagnostic.found.as_deref(), Some("Int"));
    assert!(diagnostic.help.is_none());
}

#[test]
fn annotated_binding_keeps_the_whole_nested_initializer_as_primary() {
    let text = "main : Unit -> Bool\nmain () = {\n    let value : Bool = {\n        1\n    }\n    value\n}\n";
    let fixture = ModuleFixture::load("nested-binding-mismatch.ash", text);
    let resolved = fixture.resolve();
    let ResolvedExprKind::Block(block) = &main_body(&resolved).kind else {
        panic!("fixture should resolve to a block");
    };
    let binding = binding(block, 0);
    let initializer_span = binding.initializer.span;
    let TypeError::Source(diagnostic) =
        check_module(resolved).expect_err("the nested initializer should not check")
    else {
        panic!("nested binding mismatch should be categorized");
    };

    assert_eq!(diagnostic.reason, TypeReason::BindingInitializer);
    assert_eq!(diagnostic.primary.span(), initializer_span);
}

#[test]
fn equational_interface_shape_relates_the_annotation_to_the_equation_head() {
    let error = failure("interface.ash", EQUATION_INTERFACE_NOT_FUNCTION);
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("interface shape should remain a typed source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::EquationInterfaceNotFunction);
    assert_eq!(
        diagnostic.primary.span().range().start(),
        offset(
            EQUATION_INTERFACE_NOT_FUNCTION
                .find("Int")
                .expect("interface annotation"),
        )
    );
    assert_eq!(diagnostic.expected.as_deref(), Some("function"));
    assert_eq!(diagnostic.found.as_deref(), Some("Int"));
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(
        diagnostic.related[0].span().range().start(),
        offset(
            EQUATION_INTERFACE_NOT_FUNCTION
                .find("answer value")
                .expect("equation head"),
        )
    );
}

#[test]
fn anonymous_function_without_an_annotation_relates_to_the_binding_that_requires_synthesis() {
    let fixture = ModuleFixture::load("function-context.ash", FUNCTION_NEEDS_CONTEXT);
    let resolved = fixture.resolve();
    let ResolvedExprKind::Block(block) = &main_body(&resolved).kind else {
        panic!("fixture should resolve to a block");
    };
    let binding_span = binding(block, 0).span;
    let ResolvedExprKind::Block(initializer) = &binding(block, 0).initializer.kind else {
        panic!("fixture initializer should preserve its nested block");
    };
    let function_span = initializer.result.span;
    let TypeError::Source(diagnostic) =
        check_module(resolved).expect_err("the anonymous function cannot synthesize")
    else {
        panic!("missing function context should remain a typed source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert_eq!(diagnostic.primary.span(), function_span);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span(), binding_span);
    assert_eq!(
        diagnostic.help.as_deref(),
        Some("add a function type annotation to this binding")
    );
}

#[test]
fn anonymous_main_body_records_the_source_position_that_requires_synthesis() {
    let fixture = ModuleFixture::load("function-result-context.ash", FUNCTION_RESULT_NEEDS_CONTEXT);
    let resolved = fixture.resolve();
    let expected_span = main_body(&resolved).span;
    let TypeError::Source(diagnostic) =
        check_module(resolved).expect_err("the program result must synthesize")
    else {
        panic!("missing program-result context should be a source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert_eq!(diagnostic.primary.span(), expected_span);
    assert!(diagnostic.related.is_empty());
    assert!(diagnostic.help.is_none());
}

#[test]
fn anonymous_function_checked_against_a_non_function_keeps_the_accepted_context_category() {
    let error = failure("non-function-context.ash", FUNCTION_NON_FUNCTION_CONTEXT);
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("the provisional non-function context should be a source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert!(diagnostic.expected.is_none());
    assert!(diagnostic.found.is_none());
}

#[test]
fn anonymous_function_in_function_position_relates_to_the_application_that_requires_synthesis() {
    let text = "main : Unit -> Int\nmain () = (fn(value) {\n    value\n}) 1\n";
    let fixture = ModuleFixture::load("application-context.ash", text);
    let resolved = fixture.resolve();
    let result_span = main_body(&resolved).span;
    let ResolvedExprKind::Apply(application) = &main_body(&resolved).kind else {
        panic!("fixture should resolve to an application");
    };
    let function_span = application.function.span;
    let TypeError::Source(diagnostic) =
        check_module(resolved).expect_err("the function position must synthesize")
    else {
        panic!("missing application context should be a source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert_eq!(diagnostic.primary.span(), function_span);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span(), result_span);
}

#[test]
fn anonymous_function_operand_relates_to_the_operator_that_requires_synthesis() {
    let text = "main : Unit -> Int\nmain () = (fn(value) {\n    value\n}) + 1\n";
    let fixture = ModuleFixture::load("operator-context.ash", text);
    let resolved = fixture.resolve();
    let ResolvedExprKind::Add(addition) = &main_body(&resolved).kind else {
        panic!("fixture should resolve to addition");
    };
    let left_span = addition.left.span;
    let operator_span = addition.operator_span;
    let TypeError::Source(diagnostic) =
        check_module(resolved).expect_err("the operand must synthesize")
    else {
        panic!("missing operator context should be a source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert_eq!(diagnostic.primary.span(), left_span);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span(), operator_span);
}

#[test]
fn anonymous_function_right_operand_keeps_the_operator_synthesis_context() {
    let text = "main : Unit -> Int\nmain () = 1 + (fn(value) {\n    value\n})\n";
    let fixture = ModuleFixture::load("right-operator-context.ash", text);
    let resolved = fixture.resolve();
    let ResolvedExprKind::Add(addition) = &main_body(&resolved).kind else {
        panic!("fixture should resolve to addition");
    };
    let right_span = addition.right.span;
    let operator_span = addition.operator_span;
    let TypeError::Source(diagnostic) =
        check_module(resolved).expect_err("the right operand must synthesize")
    else {
        panic!("missing right-operator context should be a source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert_eq!(diagnostic.primary.span(), right_span);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span(), operator_span);
}

#[test]
fn nested_block_preserves_the_outer_binding_synthesis_context() {
    let text = "main : Unit -> Int\nmain () = {\n    let identity = {\n        fn(value) {\n            value\n        }\n    }\n    identity 1\n}\n";
    let fixture = ModuleFixture::load("nested-binding-context.ash", text);
    let resolved = fixture.resolve();
    let ResolvedExprKind::Block(block) = &main_body(&resolved).kind else {
        panic!("fixture should resolve to a block");
    };
    let outer_binding_span = binding(block, 0).span;
    let TypeError::Source(diagnostic) =
        check_module(resolved).expect_err("the nested function still cannot synthesize")
    else {
        panic!("nested missing context should be a source diagnostic");
    };

    assert_eq!(diagnostic.reason, TypeReason::FunctionNeedsContext);
    assert_eq!(diagnostic.related.len(), 1);
    assert_eq!(diagnostic.related[0].span(), outer_binding_span);
    assert_eq!(
        diagnostic.help.as_deref(),
        Some("add a function type annotation to this binding")
    );
}

#[test]
fn rank_one_resolution_and_kind_diagnostics_retain_exact_type_sites() {
    let duplicate_text =
        "type Pair<A, A> =\n    Pair(Int, Int)\n\nmain : Unit -> Int\nmain () = 0\n";
    let duplicate = failure("duplicate-type-parameter.ash", duplicate_text);
    let PipelineFailure::Resolution(duplicate) = duplicate else {
        panic!("duplicate parameters should fail during resolution");
    };
    assert_eq!(duplicate.reason, ResolveReason::DuplicateTypeParameter);
    let header_end = duplicate_text.find(" =").expect("declaration header");
    let second = duplicate_text[..header_end]
        .rfind('A')
        .expect("second type parameter");
    let first = duplicate_text[..second]
        .rfind('A')
        .expect("first type parameter");
    assert_eq!(duplicate.primary.span().range().start(), offset(second));
    assert_eq!(duplicate.primary.span().range().end(), offset(second + 1));
    assert_eq!(duplicate.related.len(), 1);
    assert_eq!(duplicate.related[0].span().range().start(), offset(first));

    let arity_text = "type Option<A> =\n    None\n    | Some(A)\n\nbad : Option -> Int\nbad _ = 0\n\nmain : Unit -> Int\nmain () = bad None\n";
    let arity = failure("type-argument-count.ash", arity_text);
    let PipelineFailure::Kind(KindFailure::Source(arity)) = arity else {
        panic!("a bare constructor at a value boundary should fail during kind checking");
    };
    assert_eq!(arity.reason, KindReason::ExpectedType);
    let bare = arity_text.find("Option ->").expect("bare nominal");
    assert_eq!(arity.primary.span().range().start(), offset(bare));
    assert_eq!(arity.primary.span().range().end(), offset(bare + 6));
    assert_eq!(arity.expected_kind(), Some(&Kind::Type));
    assert_eq!(
        arity.found_kind(),
        Some(&Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)))
    );

    let kind_text = "type Bad<A> =\n    Bad(A<Int>)\n\nmain : Unit -> Int\nmain () = 0\n";
    let kind = failure("type-kind.ash", kind_text);
    let PipelineFailure::Kind(KindFailure::Source(kind)) = kind else {
        panic!("an applied Type-kinded binder should fail during kind checking");
    };
    assert_eq!(kind.reason, KindReason::NotApplicable);
    assert_eq!(
        kind.expectation(),
        &KindExpectation::Function { domain: Kind::Type }
    );
    assert_eq!(kind.found_kind(), Some(&Kind::Type));
    let applied = kind_text.find("A<Int>").expect("applied parameter");
    assert_eq!(kind.primary.span().range().start(), offset(applied));
    assert_eq!(kind.primary.span().range().end(), offset(applied + 6));

    let unknown_text = "type Wrapped<A> =\n    Wrapped(B)\n\nmain : Unit -> Int\nmain () = 0\n";
    let unknown = failure("unknown-type-variable.ash", unknown_text);
    let PipelineFailure::Resolution(unknown) = unknown else {
        panic!("unknown types should fail during resolution");
    };
    assert_eq!(unknown.reason, ResolveReason::UnknownType);
    let unknown_site = unknown_text.find("(B)").expect("unknown payload") + 1;
    assert_eq!(unknown.primary.span().range().start(), offset(unknown_site));
    assert_eq!(
        unknown.primary.span().range().end(),
        offset(unknown_site + 1)
    );
    assert_eq!(unknown.found.as_deref(), Some("B"));
}

#[test]
fn relational_interface_resolution_diagnostics_retain_exact_parameter_sites() {
    let duplicate_text = "interface Bad<A, A> {\nbad : A -> A\n}\n";
    let PipelineFailure::Resolution(duplicate) =
        failure("duplicate-interface-parameter.ash", duplicate_text)
    else {
        panic!("a duplicate interface parameter should fail during resolution");
    };
    assert_eq!(duplicate.reason, ResolveReason::DuplicateTypeParameter);
    assert_eq!(
        (
            duplicate.primary.span().range().start(),
            duplicate.primary.span().range().end(),
        ),
        occurrence_range(duplicate_text, "A", 1),
    );
    assert_eq!(duplicate.related.len(), 1);
    assert_eq!(
        (
            duplicate.related[0].span().range().start(),
            duplicate.related[0].span().range().end(),
        ),
        occurrence_range(duplicate_text, "A", 0),
    );

    let unknown_text = "interface Bad<A, B> where A -> Missing {\nbad : A -> A\n}\n";
    let PipelineFailure::Resolution(unknown) =
        failure("unknown-determination-parameter.ash", unknown_text)
    else {
        panic!("an unknown determination name should fail during resolution");
    };
    assert_eq!(unknown.reason, ResolveReason::UnknownType);
    assert_eq!(unknown.expected.as_deref(), Some("interface parameter"));
    assert_eq!(unknown.found.as_deref(), Some("Missing"));
    assert_eq!(
        (
            unknown.primary.span().range().start(),
            unknown.primary.span().range().end(),
        ),
        occurrence_range(unknown_text, "Missing", 0),
    );
    assert!(unknown.related.is_empty());
}

#[test]
fn determination_partition_precedes_method_kind_checking_without_bypassing_valid_edges() {
    let invalid_partition_text = concat!(
        "interface Bad<A, B, C> where A -> B {\n",
        "bad : A<Int> -> B\n",
        "}\n",
    );
    let PipelineFailure::Typing(TypeError::Interface(partition)) = failure(
        "determination-before-method-kind.ash",
        invalid_partition_text,
    ) else {
        panic!("an invalid partition should retain interface-admission ownership");
    };
    assert_eq!(partition.reason, InterfaceReason::DeterminationParameter);

    let valid_partition_text = concat!(
        "interface Bad<A, B> where A -> B {\n",
        "bad : A<Int> -> B\n",
        "}\n",
    );
    let PipelineFailure::Kind(KindFailure::Source(kind)) =
        failure("valid-determination-method-kind.ash", valid_partition_text)
    else {
        panic!("a valid partition must not bypass ordinary method kind checking");
    };
    assert_eq!(kind.reason, KindReason::NotApplicable);
    assert_eq!(
        (
            kind.primary.span().range().start(),
            kind.primary.span().range().end(),
        ),
        occurrence_range(valid_partition_text, "A<Int>", 0),
    );
}

#[test]
fn determination_partition_precedes_every_interface_method_seed() {
    let source = concat!(
        "interface Earlier<A, B> {\n",
        "earlier : A -> A\n",
        "}\n\n",
        "interface Broken<A, B> where A -> A {\n",
        "broken : A -> A\n",
        "}\n",
    );
    let PipelineFailure::Typing(TypeError::Interface(diagnostic)) =
        failure("determination-before-earlier-method-seed.ash", source)
    else {
        panic!("the later partition should precede every interface method seed");
    };
    assert_eq!(diagnostic.reason, InterfaceReason::DeterminationParameter);
}

#[test]
fn application_shape_precedes_a_later_invalid_determination_for_every_header_owner() {
    let arity_cases = [
        (
            "forward global requirement",
            concat!(
                "use_value<A> : A -> A where Broken<A>\n",
                "use_value value = value\n\n",
                "interface Broken<A, B> where A -> A {\n",
                "broken : A -> A\n",
                "}\n",
            ),
        ),
        (
            "later global requirement",
            concat!(
                "interface Broken<A, B> where A -> A {\n",
                "broken : A -> A\n",
                "}\n\n",
                "use_value<A> : A -> A where Broken<A>\n",
                "use_value value = value\n",
            ),
        ),
        (
            "forward implementation head",
            concat!(
                "impl Broken<Int> {\n",
                "broken value = value\n",
                "}\n\n",
                "interface Broken<A, B> where A -> A {\n",
                "broken : A -> A\n",
                "}\n",
            ),
        ),
        (
            "later implementation head",
            concat!(
                "interface Broken<A, B> where A -> A {\n",
                "broken : A -> A\n",
                "}\n\n",
                "impl Broken<Int> {\n",
                "broken value = value\n",
                "}\n",
            ),
        ),
        (
            "forward implementation prerequisite",
            concat!(
                "interface Keep<A> {\n",
                "keep : A -> A\n",
                "}\n\n",
                "impl Keep<Int> where Broken<Int> {\n",
                "keep value = value\n",
                "}\n\n",
                "interface Broken<A, B> where A -> A {\n",
                "broken : A -> A\n",
                "}\n",
            ),
        ),
        (
            "later implementation prerequisite",
            concat!(
                "interface Keep<A> {\n",
                "keep : A -> A\n",
                "}\n\n",
                "interface Broken<A, B> where A -> A {\n",
                "broken : A -> A\n",
                "}\n\n",
                "impl Keep<Int> where Broken<Int> {\n",
                "keep value = value\n",
                "}\n",
            ),
        ),
    ];
    for (name, source) in arity_cases {
        let actual = failure("determination-arity-owner.ash", source);
        let PipelineFailure::Typing(TypeError::Interface(diagnostic)) = actual else {
            panic!("{name} should retain interface checking ownership, found {actual:?}");
        };
        assert_eq!(diagnostic.reason, InterfaceReason::ArgumentCount);
    }

    let kind_cases = [
        (
            "forward global requirement",
            concat!(
                "use_value<A> : A -> A where Broken<Int, A>\n",
                "use_value value = value\n\n",
                "interface Broken<F : Type -> Type, A> where F -> F {\n",
                "broken : F<A> -> A\n",
                "}\n",
            ),
        ),
        (
            "later global requirement",
            concat!(
                "interface Broken<F : Type -> Type, A> where F -> F {\n",
                "broken : F<A> -> A\n",
                "}\n\n",
                "use_value<A> : A -> A where Broken<Int, A>\n",
                "use_value value = value\n",
            ),
        ),
        (
            "forward implementation head",
            concat!(
                "impl Broken<Int, Bool> {\n",
                "broken value = false\n",
                "}\n\n",
                "interface Broken<F : Type -> Type, A> where F -> F {\n",
                "broken : F<A> -> A\n",
                "}\n",
            ),
        ),
        (
            "later implementation head",
            concat!(
                "interface Broken<F : Type -> Type, A> where F -> F {\n",
                "broken : F<A> -> A\n",
                "}\n\n",
                "impl Broken<Int, Bool> {\n",
                "broken value = false\n",
                "}\n",
            ),
        ),
        (
            "forward implementation prerequisite",
            concat!(
                "interface Keep<A> {\n",
                "keep : A -> A\n",
                "}\n\n",
                "impl Keep<Int> where Broken<Int, Bool> {\n",
                "keep value = value\n",
                "}\n\n",
                "interface Broken<F : Type -> Type, A> where F -> F {\n",
                "broken : F<A> -> A\n",
                "}\n",
            ),
        ),
        (
            "later implementation prerequisite",
            concat!(
                "interface Keep<A> {\n",
                "keep : A -> A\n",
                "}\n\n",
                "interface Broken<F : Type -> Type, A> where F -> F {\n",
                "broken : F<A> -> A\n",
                "}\n\n",
                "impl Keep<Int> where Broken<Int, Bool> {\n",
                "keep value = value\n",
                "}\n",
            ),
        ),
    ];
    for (name, source) in kind_cases {
        let actual = failure("determination-kind-owner.ash", source);
        let PipelineFailure::Kind(KindFailure::Source(kind)) = actual else {
            panic!("{name} should retain kind checking ownership, found {actual:?}");
        };
        assert_eq!(kind.reason, KindReason::Argument);
    }
}

#[test]
fn application_arity_preflight_precedes_valid_interface_method_seeds_for_every_header_owner() {
    let arity_cases = [
        (
            "implementation head",
            concat!(
                "interface Broken<A, B> where A -> B {\n",
                "broken : B -> B\n",
                "}\n\n",
                "interface Target<A, B> {\n",
                "target : (A, B) -> A\n",
                "}\n\n",
                "impl Target<Int> {\n",
                "target pair = 0\n",
                "}\n",
            ),
        ),
        (
            "global requirement",
            concat!(
                "interface Broken<A, B> where A -> B {\n",
                "broken : B -> B\n",
                "}\n\n",
                "interface Target<A, B> {\n",
                "target : (A, B) -> A\n",
                "}\n\n",
                "use_value<A> : A -> A where Target<A>\n",
                "use_value value = value\n",
            ),
        ),
        (
            "implementation prerequisite",
            concat!(
                "interface Broken<A, B> where A -> B {\n",
                "broken : B -> B\n",
                "}\n\n",
                "interface Target<A, B> {\n",
                "target : (A, B) -> A\n",
                "}\n\n",
                "interface Keep<A> {\n",
                "keep : A -> A\n",
                "}\n\n",
                "impl Keep<Int> where Target<Int> {\n",
                "keep value = value\n",
                "}\n",
            ),
        ),
    ];
    for (name, source) in arity_cases {
        let actual = failure("valid-determination-arity-preflight.ash", source);
        let PipelineFailure::Typing(TypeError::Interface(diagnostic)) = actual else {
            panic!("{name} arity should precede the earlier method seed, found {actual:?}");
        };
        assert_eq!(diagnostic.reason, InterfaceReason::ArgumentCount);
    }
}

#[test]
fn positional_kind_preflight_precedes_valid_interface_method_kinds_for_every_header_owner() {
    let kind_cases = [
        (
            "global requirement",
            concat!(
                "interface Broken<A, B> where A -> B {\n",
                "broken : A<Int> -> B\n",
                "}\n\n",
                "interface Target<F : Type -> Type, A> {\n",
                "target : F<A> -> A\n",
                "}\n\n",
                "use_value<A> : A -> A where Target<Int, A>\n",
                "use_value value = value\n",
            ),
        ),
        (
            "implementation head",
            concat!(
                "interface Broken<A, B> where A -> B {\n",
                "broken : A<Int> -> B\n",
                "}\n\n",
                "interface Target<F : Type -> Type, A> {\n",
                "target : F<A> -> A\n",
                "}\n\n",
                "impl Target<Int, Bool> {\n",
                "target value = false\n",
                "}\n",
            ),
        ),
        (
            "implementation prerequisite",
            concat!(
                "interface Broken<A, B> where A -> B {\n",
                "broken : A<Int> -> B\n",
                "}\n\n",
                "interface Target<F : Type -> Type, A> {\n",
                "target : F<A> -> A\n",
                "}\n\n",
                "interface Keep<A> {\n",
                "keep : A -> A\n",
                "}\n\n",
                "impl Keep<Int> where Target<Int, Bool> {\n",
                "keep value = value\n",
                "}\n",
            ),
        ),
    ];
    for (name, source) in kind_cases {
        let actual = failure("valid-determination-kind-preflight.ash", source);
        let PipelineFailure::Kind(KindFailure::Source(kind)) = actual else {
            panic!("{name} kind should precede the earlier method kind, found {actual:?}");
        };
        assert_eq!(kind.reason, KindReason::Argument);
    }
}

#[test]
fn invalid_determination_kind_preflight_installs_each_application_owner() {
    let cases = [
        (
            "global requirement binder",
            concat!(
                "interface Broken<F : Type -> Type, A> where F -> F {\n",
                "broken : F<A> -> A\n",
                "}\n\n",
                "use_value<F : Type -> Type, A> : F<A> -> F<A> where Broken<F, A>\n",
                "use_value value = value\n",
            ),
        ),
        (
            "implementation head binder",
            concat!(
                "interface Broken<F : Type -> Type, A> where F -> F {\n",
                "broken : F<A> -> A\n",
                "}\n\n",
                "impl<F : Type -> Type, A> Broken<F, A> {\n",
                "broken value = value\n",
                "}\n",
            ),
        ),
    ];
    for (name, source) in cases {
        let actual = failure("determination-kind-owner-binder.ash", source);
        let PipelineFailure::Typing(TypeError::Interface(diagnostic)) = actual else {
            panic!("{name} should reach determination admission, found {actual:?}");
        };
        assert_eq!(diagnostic.reason, InterfaceReason::DeterminationParameter);
    }

    let both_implementation_binder_partitions = concat!(
        "interface Keep<A> {\n",
        "keep : A -> A\n",
        "}\n\n",
        "impl<A> Keep<A> where Broken<A, F, Int, A> {\n",
        "keep value = value\n",
        "}\n\n",
        "interface Broken<A, F, G : Type -> Type, D> where A -> A {\n",
        "broken : (A, F, G<A>) -> D\n",
        "}\n",
    );
    let actual = failure(
        "determination-kind-owner-binder-partitions.ash",
        both_implementation_binder_partitions,
    );
    let PipelineFailure::Kind(KindFailure::Source(kind)) = actual else {
        panic!(
            "an implementation prerequisite must install both owner-binder partitions, found {actual:?}"
        );
    };
    assert_eq!(kind.reason, KindReason::Argument);
    assert_eq!(
        (
            kind.primary.span().range().start(),
            kind.primary.span().range().end(),
        ),
        occurrence_range(both_implementation_binder_partitions, "Int", 0),
    );
}

#[test]
fn determination_partition_diagnostics_point_to_the_causal_parameters() {
    struct Case {
        source: &'static str,
        primary: &'static str,
        primary_occurrence: usize,
        related: &'static str,
        related_occurrence: usize,
    }

    let cases = [
        Case {
            source: "interface Bad<A, B> where (A, A) -> B {\nbad : A -> B\n}\n",
            primary: "A",
            primary_occurrence: 2,
            related: "A",
            related_occurrence: 1,
        },
        Case {
            source: "interface Bad<A, B, C> where A -> B {\nbad : A -> B\n}\n",
            primary: "where A -> B",
            primary_occurrence: 0,
            related: "C",
            related_occurrence: 0,
        },
        Case {
            source: "interface Bad<A, B, C> where (B, A) -> C {\nbad : (A, B) -> C\n}\n",
            primary: "A",
            primary_occurrence: 1,
            related: "B",
            related_occurrence: 2,
        },
        Case {
            source: "interface Bad<A, B, C> where (A, B) -> (B, C) {\nbad : (A, B) -> C\n}\n",
            primary: "B",
            primary_occurrence: 3,
            related: "B",
            related_occurrence: 2,
        },
        Case {
            source: "interface Bad<A, B> where (A, B) -> A {\nbad : (A, B) -> A\n}\n",
            primary: "A",
            primary_occurrence: 2,
            related: "A",
            related_occurrence: 1,
        },
        Case {
            source: "interface Bad<A, B, C> where A -> (C, B) {\nbad : A -> (B, C)\n}\n",
            primary: "B",
            primary_occurrence: 2,
            related: "C",
            related_occurrence: 1,
        },
    ];

    for (index, case) in cases.into_iter().enumerate() {
        let PipelineFailure::Typing(TypeError::Interface(diagnostic)) =
            failure(&format!("determination-partition-{index}.ash"), case.source)
        else {
            panic!("a malformed total partition should fail during interface admission");
        };
        assert_eq!(diagnostic.reason, InterfaceReason::DeterminationParameter);
        assert_eq!(
            (
                diagnostic.primary.span().range().start(),
                diagnostic.primary.span().range().end(),
            ),
            occurrence_range(case.source, case.primary, case.primary_occurrence),
            "case {index} primary",
        );
        assert_eq!(diagnostic.related.len(), 1);
        assert_eq!(
            (
                diagnostic.related[0].span().range().start(),
                diagnostic.related[0].span().range().end(),
            ),
            occurrence_range(case.source, case.related, case.related_occurrence),
            "case {index} related",
        );
    }
}

#[test]
fn implementation_determination_diagnostics_retain_distinct_causes() {
    let coverage_text = concat!(
        "interface Relation<A, B> where A -> B {\n",
        "relate : A -> Int\n",
        "}\n\n",
        "impl<B> Relation<Int, B> {\n",
        "relate value = 0\n",
        "}\n",
    );
    let PipelineFailure::Typing(TypeError::Interface(coverage)) =
        failure("implementation-determination-coverage.ash", coverage_text)
    else {
        panic!("an uncovered dependent variable should fail implementation admission");
    };
    assert_eq!(coverage.reason, InterfaceReason::ImplDeterminationCoverage);
    assert_eq!(
        coverage.primary.message(),
        "this dependent argument contains a variable absent from the determinant key"
    );
    assert!(
        coverage
            .related
            .iter()
            .any(|label| { label.message() == "this dependent variable is bound here" })
    );
    assert!(coverage.related.iter().any(|label| {
        label.message() == "this determinant-key argument does not contain the dependent variable"
    }));

    let conflict_text = concat!(
        "interface Relation<A, B> where A -> B {\n",
        "relate : A -> Int\n",
        "}\n\n",
        "impl Relation<Int, Int> {\nrelate value = 0\n}\n\n",
        "impl Relation<Int, Bool> {\nrelate value = 0\n}\n",
    );
    let PipelineFailure::Typing(TypeError::Interface(conflict)) =
        failure("implementation-determination-conflict.ash", conflict_text)
    else {
        panic!("equal keys with unequal complete heads should fail coherence");
    };
    assert_eq!(conflict.reason, InterfaceReason::ImplDeterminationConflict);
    assert_eq!(
        conflict.primary.message(),
        "this implementation shares a determinant key with an earlier implementation but disagrees on dependents"
    );
    assert!(
        conflict.related.iter().any(|label| {
            label.message() == "the earlier conflicting implementation head is here"
        })
    );
}

#[test]
fn method_type_parameter_diagnostics_retain_boundary_and_spans() {
    let duplicate_text = "interface Bad<A> {\nbad<A> : A -> A\n}\n";
    let PipelineFailure::Resolution(duplicate) =
        failure("duplicate-method-owner-parameter.ash", duplicate_text)
    else {
        panic!("an interface-parameter duplicate should fail during resolution");
    };
    assert_eq!(duplicate.reason, ResolveReason::DuplicateTypeParameter);
    assert_eq!(
        (
            duplicate.primary.span().range().start(),
            duplicate.primary.span().range().end(),
        ),
        occurrence_range(duplicate_text, "A", 1),
    );
    assert_eq!(duplicate.related.len(), 1);
    assert_eq!(
        (
            duplicate.related[0].span().range().start(),
            duplicate.related[0].span().range().end(),
        ),
        occurrence_range(duplicate_text, "A", 0),
    );

    let unused_text = "interface Bad<A> {\nbad<B, C> : (A, B) -> B\n}\n";
    let PipelineFailure::Resolution(unused) = failure("unused-method-parameter.ash", unused_text)
    else {
        panic!("an unused method parameter should fail during resolution");
    };
    assert_eq!(unused.reason, ResolveReason::UnusedTypeParameter);
    assert_eq!(unused.found.as_deref(), Some("C"));
    assert_eq!(
        (
            unused.primary.span().range().start(),
            unused.primary.span().range().end(),
        ),
        occurrence_range(unused_text, "C", 0),
    );

    let unknown_text = "interface Bad<A> {\nbad<B> : (A, B, C) -> B\n}\n";
    let PipelineFailure::Resolution(unknown) =
        failure("unknown-method-parameter.ash", unknown_text)
    else {
        panic!("an unlisted method parameter should fail during resolution");
    };
    assert_eq!(unknown.reason, ResolveReason::UnknownType);
    assert_eq!(unknown.found.as_deref(), Some("C"));
    assert_eq!(
        (
            unknown.primary.span().range().start(),
            unknown.primary.span().range().end(),
        ),
        occurrence_range(unknown_text, "C", 0),
    );

    let kind_text = "interface Bad<A> {\nbad<F : Type -> Type> : F -> A\n}\n";
    let PipelineFailure::Kind(KindFailure::Source(kind)) =
        failure("method-parameter-kind.ash", kind_text)
    else {
        panic!("a method parameter kind mismatch should fail during kind checking");
    };
    assert_eq!(kind.reason, KindReason::ExpectedType);
    assert_eq!(kind.expected_kind(), Some(&Kind::Type));
    assert_eq!(
        kind.found_kind(),
        Some(&Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)))
    );
    assert_eq!(
        (
            kind.primary.span().range().start(),
            kind.primary.span().range().end(),
        ),
        occurrence_range(kind_text, "F", 1),
    );
    assert_eq!(kind.related.len(), 1);
    assert_eq!(
        (
            kind.related[0].span().range().start(),
            kind.related[0].span().range().end(),
        ),
        occurrence_range(kind_text, "F", 0),
    );

    let absent_text = "interface Bad<A> {\nbad : G<Int> -> A\n}\n";
    let PipelineFailure::Typing(TypeError::Interface(absent)) =
        failure("absent-method-parameter-list.ash", absent_text)
    else {
        panic!("an absent method list should retain interface-checking ownership");
    };
    assert_eq!(absent.reason.to_string(), "interface.method-parameter");
    assert_eq!(
        (
            absent.primary.span().range().start(),
            absent.primary.span().range().end(),
        ),
        occurrence_range(absent_text, "bad : G<Int> -> A", 0),
    );
    assert_eq!(
        absent.primary.message(),
        "this method signature must use its interface parameter and only declared type parameters"
    );
    assert_eq!(absent.related.len(), 1);
    assert_eq!(
        (
            absent.related[0].span().range().start(),
            absent.related[0].span().range().end(),
        ),
        occurrence_range(absent_text, "A", 0),
    );
    assert_eq!(
        absent.related[0].message(),
        "the interface parameter is declared here"
    );

    let shape_text = "interface Bad<A> {\nbad<B> : B\n}\n";
    let PipelineFailure::Typing(TypeError::Interface(shape)) =
        failure("method-parameter-before-shape.ash", shape_text)
    else {
        panic!("method parameter checking should precede the outer function-shape rule");
    };
    assert_eq!(shape.reason, InterfaceReason::MethodParameter);
    assert_eq!(
        (
            shape.primary.span().range().start(),
            shape.primary.span().range().end(),
        ),
        occurrence_range(shape_text, "bad<B> : B", 0),
    );
}

#[test]
fn method_parameter_higher_rank_exclusions_have_direct_source_diagnostics() {
    struct SyntaxCase {
        route: &'static str,
        source: &'static str,
        primary: &'static str,
        primary_occurrence: usize,
        expected: &'static str,
        found: &'static str,
    }

    let syntax_cases = [
        SyntaxCase {
            route: "source forall",
            source: "main : forall A. A -> A\nmain value = value\n",
            primary: "forall",
            primary_occurrence: 0,
            expected: "a type",
            found: "identifier",
        },
        SyntaxCase {
            route: "expression type application",
            source: concat!(
                "identity<A> : A -> A\n",
                "identity value = value\n\n",
                "main : Unit -> Int\n",
                "main () = identity<Int> 42\n",
            ),
            primary: "<",
            primary_occurrence: 1,
            expected: "a logical line end",
            found: "<",
        },
        SyntaxCase {
            route: "polymorphic parameter annotation",
            source: "fn consume(value : forall A. A -> A) -> Int {\n0\n}\n",
            primary: "forall",
            primary_occurrence: 0,
            expected: "a type",
            found: "identifier",
        },
        SyntaxCase {
            route: "polymorphic result annotation",
            source: "fn produce(value : Unit) -> forall A. A -> A {\nfn(item) {\nitem\n}\n}\n",
            primary: "forall",
            primary_occurrence: 0,
            expected: "a type",
            found: "identifier",
        },
        SyntaxCase {
            route: "polymorphic tuple field",
            source: "bad : (Int, forall A. A -> A) -> Int\nbad pair = 0\n",
            primary: "forall",
            primary_occurrence: 0,
            expected: "a type",
            found: "identifier",
        },
        SyntaxCase {
            route: "polymorphic constructor field",
            source: "type Box = Box(forall A. A -> A)\n",
            primary: "forall",
            primary_occurrence: 0,
            expected: "a type",
            found: "identifier",
        },
        SyntaxCase {
            route: "method scheme return",
            source: concat!(
                "interface Project<I> {\nproject<A> : I -> (I, A)\n}\n\n",
                "fn return_project(value : Int) -> forall A. Int -> (Int, A) ",
                "where Project<Int> {\nproject\n}\n",
            ),
            primary: "forall",
            primary_occurrence: 0,
            expected: "a type",
            found: "identifier",
        },
        SyntaxCase {
            route: "method requirement",
            source: concat!(
                "interface Project<I> {\n",
                "project<A> : I -> (I, A) where Project<A>\n",
                "}\n",
            ),
            primary: "where",
            primary_occurrence: 0,
            expected: "a logical line end",
            found: "where",
        },
    ];

    for case in syntax_cases {
        let PipelineFailure::Syntax(syntax) = failure("higher-rank-exclusion.ash", case.source)
        else {
            panic!("{} should remain unavailable in source syntax", case.route);
        };
        assert!(syntax.lexical.is_empty(), "route: {}", case.route);
        let diagnostic = syntax
            .parser
            .first()
            .unwrap_or_else(|| panic!("{} should retain a parser diagnostic", case.route));
        assert_eq!(
            diagnostic.reason,
            ParseReason::ExpectedForm,
            "route: {}",
            case.route
        );
        assert_eq!(
            (
                diagnostic.primary.span().range().start(),
                diagnostic.primary.span().range().end(),
            ),
            occurrence_range(case.source, case.primary, case.primary_occurrence),
            "primary span: {}",
            case.route,
        );
        assert_eq!(
            diagnostic.primary.message(),
            "required syntax is missing",
            "primary label: {}",
            case.route,
        );
        assert_eq!(
            diagnostic.expected.as_deref(),
            Some(case.expected),
            "route: {}",
            case.route
        );
        assert_eq!(
            diagnostic.found.as_deref(),
            Some(case.found),
            "route: {}",
            case.route
        );
    }

    let storage_text = concat!(
        "interface Project<I> {\nproject<A> : I -> (I, A)\n}\n\n",
        "store : Int -> Unit where Project<Int>\n",
        "store value = {\nlet stored = project\n()\n}\n",
    );
    let PipelineFailure::Typing(TypeError::Interface(storage)) =
        failure("method-scheme-storage.ash", storage_text)
    else {
        panic!("an uninstantiated stored method should keep its ambiguous interface obligation");
    };
    assert_eq!(storage.reason, InterfaceReason::Ambiguous);

    let passing_text = concat!(
        "interface Project<I> {\nproject<A> : I -> (I, A)\n}\n\n",
        "fn consume<A>(poly : Int -> (Int, A)) -> Unit {\n()\n}\n",
        "pass : Int -> Unit where Project<Int>\n",
        "pass value = consume(project)\n",
    );
    let PipelineFailure::Typing(TypeError::Source(passing)) =
        failure("method-scheme-passing.ash", passing_text)
    else {
        panic!("passing a method to an ordinary parameter should instantiate a monotype");
    };
    assert_eq!(passing.reason, TypeReason::AmbiguousType);

    let implicit_text = "interface Project<I> {\nproject : I -> (I, A)\n}\n";
    let PipelineFailure::Typing(TypeError::Interface(implicit)) =
        failure("implicit-method-binder.ash", implicit_text)
    else {
        panic!("an implicit method binder should fail at interface checking");
    };
    assert_eq!(implicit.reason, InterfaceReason::MethodParameter);
    assert_eq!(
        (
            implicit.primary.span().range().start(),
            implicit.primary.span().range().end(),
        ),
        occurrence_range(implicit_text, "project : I -> (I, A)", 0),
    );
    assert_eq!(
        implicit.primary.message(),
        "this method signature must use its interface parameter and only declared type parameters"
    );
    assert_eq!(implicit.related.len(), 1);
    assert_eq!(
        (
            implicit.related[0].span().range().start(),
            implicit.related[0].span().range().end(),
        ),
        occurrence_range(implicit_text, "I", 0),
    );
    assert_eq!(
        implicit.related[0].message(),
        "the interface parameter is declared here"
    );

    let recursive_text = concat!(
        "interface Repeat<I> {\nrepeat<A> : (I, A) -> A\n}\n\n",
        "impl Repeat<Int> {\n",
        "repeat (owner, value) = repeat((owner, (value, value)))\n",
        "}\n",
    );
    let PipelineFailure::Typing(TypeError::Source(recursive)) =
        failure("polymorphic-recursive-method.ash", recursive_text)
    else {
        panic!("a polymorphic recursive method self-use should fail during typing");
    };
    assert_eq!(recursive.reason, TypeReason::PolymorphicRecursion);
    assert_eq!(recursive.expected.as_deref(), Some("A"));
    assert_eq!(recursive.found.as_deref(), Some("(A, A)"));
    assert_eq!(
        recursive.primary.message(),
        "this recursive call requires a different type instantiation"
    );
    assert!(
        recursive.related.iter().any(|label| {
            label.message() == "this recursive function is checked monomorphically"
        })
    );
}

#[test]
fn public_kind_diagnostics_retain_complete_causal_rows() {
    const OPTION: &str = "type Option<A> =\nNone\n| Some(A)\n";
    const HIGHER: &str = concat!(
        "interface Higher<F : Type -> Type> {\n",
        "higher : F<Int> -> Unit\n",
        "}\n",
    );

    let cases = [
        KindDiagnosticCase {
            name: "kind-not-applicable.ash",
            source: "bad<A> : A<Int> -> Unit\nbad value = ()\n".to_owned(),
            reason: KindReason::NotApplicable,
            primary: ("A<Int>", 0),
            primary_message: "this type does not have a function kind",
            related: ("A", 0),
            related_message: "the applied type's kind is fixed by this declaration",
            expectation: KindExpectationShape::ApplicableToType,
        },
        KindDiagnosticCase {
            name: "kind-application-argument.ash",
            source: concat!(
                "type Box<F : Type -> Type> = Box\n",
                "bad : Box<Int> -> Unit\n",
                "bad value = ()\n",
            )
            .to_owned(),
            reason: KindReason::Argument,
            primary: ("Int", 0),
            primary_message: "this type argument has the wrong kind",
            related: ("type Box<F : Type -> Type> = Box", 0),
            related_message: "the applied type's parameter kind is declared here",
            expectation: KindExpectationShape::TypeConstructor,
        },
        KindDiagnosticCase {
            name: "kind-global-requirement.ash",
            source: format!("{HIGHER}bad : Unit -> Unit where Higher<Int>\nbad value = value\n"),
            reason: KindReason::Argument,
            primary: ("Int", 1),
            primary_message: "this interface argument has the wrong kind",
            related: ("F", 0),
            related_message: "the interface parameter kind is declared here",
            expectation: KindExpectationShape::TypeConstructor,
        },
        KindDiagnosticCase {
            name: "kind-implementation-head.ash",
            source: format!("{HIGHER}impl Higher<Int> {{\n}}\n"),
            reason: KindReason::Argument,
            primary: ("Int", 1),
            primary_message: "this interface argument has the wrong kind",
            related: ("F", 0),
            related_message: "the interface parameter kind is declared here",
            expectation: KindExpectationShape::TypeConstructor,
        },
        KindDiagnosticCase {
            name: "kind-implementation-prerequisite.ash",
            source: format!("{OPTION}{HIGHER}impl Higher<Option> where Higher<Int> {{\n}}\n"),
            reason: KindReason::Argument,
            primary: ("Int", 1),
            primary_message: "this interface argument has the wrong kind",
            related: ("F", 0),
            related_message: "the interface parameter kind is declared here",
            expectation: KindExpectationShape::TypeConstructor,
        },
        KindDiagnosticCase {
            name: "kind-constructor-payload.ash",
            source: format!("{OPTION}type Bad = Bad(Option)\n"),
            reason: KindReason::ExpectedType,
            primary: ("Option", 1),
            primary_message: "this value type must have kind Type",
            related: ("type Option<A> =\nNone\n| Some(A)", 0),
            related_message: "the found kind is fixed by this declaration",
            expectation: KindExpectationShape::Type,
        },
        KindDiagnosticCase {
            name: "kind-interface-method.ash",
            source: format!("{OPTION}interface Bad<A> {{\nmethod : Option\n}}\n"),
            reason: KindReason::ExpectedType,
            primary: ("Option", 1),
            primary_message: "this value type must have kind Type",
            related: ("type Option<A> =\nNone\n| Some(A)", 0),
            related_message: "the found kind is fixed by this declaration",
            expectation: KindExpectationShape::Type,
        },
        KindDiagnosticCase {
            name: "kind-equational-global.ash",
            source: format!("{OPTION}bad : Unit -> Option\nbad value = None\n"),
            reason: KindReason::ExpectedType,
            primary: ("Option", 1),
            primary_message: "this function codomain must have kind Type",
            related: ("type Option<A> =\nNone\n| Some(A)", 0),
            related_message: "the found kind is fixed by this declaration",
            expectation: KindExpectationShape::Type,
        },
        KindDiagnosticCase {
            name: "kind-inline-parameter.ash",
            source: format!("{OPTION}fn bad(value : Option) -> Unit {{\n()\n}}\n"),
            reason: KindReason::ExpectedType,
            primary: ("Option", 1),
            primary_message: "this value type must have kind Type",
            related: ("type Option<A> =\nNone\n| Some(A)", 0),
            related_message: "the found kind is fixed by this declaration",
            expectation: KindExpectationShape::Type,
        },
        KindDiagnosticCase {
            name: "kind-inline-result.ash",
            source: format!("{OPTION}fn bad(value : Unit) -> Option {{\nvalue\n}}\n"),
            reason: KindReason::ExpectedType,
            primary: ("Option", 1),
            primary_message: "this value type must have kind Type",
            related: ("type Option<A> =\nNone\n| Some(A)", 0),
            related_message: "the found kind is fixed by this declaration",
            expectation: KindExpectationShape::Type,
        },
        KindDiagnosticCase {
            name: "kind-sequential-let.ash",
            source: format!(
                "{OPTION}main : Unit -> Unit\nmain () = {{\nlet value : Option = None\n()\n}}\n"
            ),
            reason: KindReason::ExpectedType,
            primary: ("Option", 1),
            primary_message: "this value type must have kind Type",
            related: ("type Option<A> =\nNone\n| Some(A)", 0),
            related_message: "the found kind is fixed by this declaration",
            expectation: KindExpectationShape::Type,
        },
        KindDiagnosticCase {
            name: "kind-recursive-member.ash",
            source: format!(
                "{OPTION}main : Unit -> Unit\nmain () = {{\nlet rec value : Option = None\n()\n}}\n"
            ),
            reason: KindReason::ExpectedType,
            primary: ("Option", 1),
            primary_message: "this value type must have kind Type",
            related: ("type Option<A> =\nNone\n| Some(A)", 0),
            related_message: "the found kind is fixed by this declaration",
            expectation: KindExpectationShape::Type,
        },
    ];

    for case in &cases {
        assert_public_kind_diagnostic(case);
    }
}

#[test]
fn public_kind_failure_precedence_follows_causal_and_owner_order() {
    const OPTION: &str = "type Option<A> =\nNone\n| Some(A)\n";
    const HIGHER: &str = concat!(
        "interface Higher<F : Type -> Type> {\n",
        "higher : F<Int> -> Unit\n",
        "}\n",
    );
    let cases = vec![
        (
            "kind-precedence-inner-argument.ash",
            concat!(
                "type Box<F : Type -> Type> = Box\n",
                "bad<A> : A<Box<Int>> -> Unit\n",
                "bad value = ()\n",
            )
            .to_owned(),
            KindReason::Argument,
            ("Int", 0),
        ),
        (
            "kind-precedence-global-value.ash",
            format!("{OPTION}{HIGHER}bad : Option where Higher<Int>\nbad value = None\n"),
            KindReason::Argument,
            ("Int", 1),
        ),
        (
            "kind-precedence-implementation-head.ash",
            format!("{HIGHER}impl Higher<Int> where Higher<Bool> {{\n}}\n"),
            KindReason::Argument,
            ("Int", 1),
        ),
        (
            "kind-precedence-inline-parameter.ash",
            format!(
                "{OPTION}{HIGHER}fn bad(value : Option) -> Option where Higher<Bool> {{\nlet local : Option = None\nvalue\n}}\n"
            ),
            KindReason::Argument,
            ("Bool", 0),
        ),
        (
            "kind-precedence-inline-result.ash",
            format!(
                "{OPTION}{HIGHER}fn bad(value : Unit) -> Option where Higher<Bool> {{\nlet local : Option = None\nvalue\n}}\n"
            ),
            KindReason::Argument,
            ("Bool", 0),
        ),
        (
            "kind-precedence-inline-requirement.ash",
            format!(
                "{OPTION}{HIGHER}fn bad(value : Unit) -> Unit where Higher<Bool> {{\nlet local : Option = None\nvalue\n}}\n"
            ),
            KindReason::Argument,
            ("Bool", 0),
        ),
        (
            "kind-precedence-inline-body.ash",
            format!(
                "{OPTION}{HIGHER}fn bad(value : Unit) -> Unit where Higher<Option> {{\nlet local : Option = None\nvalue\n}}\n"
            ),
            KindReason::ExpectedType,
            ("Option", 2),
        ),
    ];

    for (name, source, reason, primary) in cases {
        let failure = failure(name, &source);
        let PipelineFailure::Kind(KindFailure::Source(error)) = failure else {
            panic!("{name} should retain public kind ownership, found {failure:?}");
        };
        assert_eq!(error.reason, reason, "case: {name}");
        assert_eq!(
            (
                error.primary.span().range().start(),
                error.primary.span().range().end(),
            ),
            occurrence_range(&source, primary.0, primary.1),
            "case: {name}",
        );
    }
}

#[test]
fn kind_presentation_handles_effect_and_type_arguments() {
    use ash::{
        message::{Catalogue, Locale},
        presentation::{compile_kind_diagnostic, write_json, write_short},
    };
    for (text, reason, related_count) in [
        (
            "bad<A> : A<Int> -> Unit\nbad value = ()\n",
            KindReason::NotApplicable,
            1,
        ),
        (
            "effect E<F : Type -> Type> {\nop : Unit -> F<Int>\n}\nprobe : Unit -> Unit ! {E<Int>}\nprobe () = ()\n",
            KindReason::Argument,
            1,
        ),
    ] {
        let fixture = ModuleFixture::load("kind-origin.ash", text);
        let failure = run_path(RunConfiguration {
            entry: fixture.loaded().canonical_path().to_path_buf(),
            roots: ModuleRoots::empty(),
        })
        .unwrap_err();
        let Some(PipelineFailure::Kind(KindFailure::Source(error))) = failure.pipeline_failure()
        else {
            panic!("{failure:?}")
        };
        assert_eq!(error.reason, reason);
        assert_eq!(error.related.len(), related_count);
        let sources: Vec<_> = failure.sources().iter().collect();
        let view = compile_kind_diagnostic(error, &sources).unwrap();
        for locale in [Locale::English, Locale::Bulgarian] {
            let mut output = Vec::new();
            write_short(&mut output, &view, &Catalogue::new(locale).unwrap()).unwrap();
            assert!(String::from_utf8(output).unwrap().contains("`Type`"));
        }
        let mut output = Vec::new();
        write_json(&mut output, &view).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["labels"].as_array().unwrap().len(), related_count + 1);
        assert_eq!(
            json["labels"][1]["facts"][0]["value"],
            if reason == KindReason::Argument {
                "Type -> Type"
            } else {
                "Type"
            }
        );
    }
}

#[test]
fn rank_one_inference_diagnostics_retain_exact_categories_and_types() {
    let rigid_text = "rigid : A -> A\nrigid value = 1\n\nmain : Unit -> Int\nmain () = 0\n";
    let rigid = failure("rigid-mismatch.ash", rigid_text);
    let PipelineFailure::Typing(TypeError::Source(rigid)) = rigid else {
        panic!("rigid mismatches should fail during typing");
    };
    assert_eq!(rigid.reason, TypeReason::DefinitionResult);
    assert_eq!(rigid.expected.as_deref(), Some("A"));
    assert_eq!(rigid.found.as_deref(), Some("Int"));
    let literal = rigid_text.find("= 1").expect("result literal") + 2;
    assert_eq!(rigid.primary.span().range().start(), offset(literal));
    assert_eq!(rigid.primary.span().range().end(), offset(literal + 1));

    let recursive_text = "loop : A -> Unit\nloop value = loop((value, value))\n\nmain : Unit -> Unit\nmain () = loop(1)\n";
    let recursive = failure("polymorphic-recursion.ash", recursive_text);
    let PipelineFailure::Typing(TypeError::Source(recursive)) = recursive else {
        panic!("polymorphic recursion should fail during typing");
    };
    assert_eq!(recursive.reason, TypeReason::PolymorphicRecursion);
    assert_eq!(recursive.expected.as_deref(), Some("A"));
    assert_eq!(recursive.found.as_deref(), Some("(A, A)"));
    let argument_text = "((value, value))";
    let argument = recursive_text
        .find(argument_text)
        .expect("recursive argument");
    assert_eq!(recursive.primary.span().range().start(), offset(argument));
    assert_eq!(
        recursive.primary.span().range().end(),
        offset(argument + argument_text.len())
    );

    let infinite_text =
        "main : Unit -> Int\nmain () = {\nlet omega = fn(value) {\nvalue(value)\n}\nomega\n}\n";
    let infinite = failure("infinite-type.ash", infinite_text);
    let PipelineFailure::Typing(TypeError::Source(infinite)) = infinite else {
        panic!("infinite types should fail during typing");
    };
    assert_eq!(infinite.reason, TypeReason::InfiniteType);
    let infinite_argument_text = "(value)";
    let self_application = infinite_text
        .rfind(infinite_argument_text)
        .expect("self-application argument");
    assert_eq!(
        infinite.primary.span().range().start(),
        offset(self_application)
    );
    assert_eq!(
        infinite.primary.span().range().end(),
        offset(self_application + infinite_argument_text.len())
    );

    let ambiguous_text = "main : Unit -> Unit\nmain () = {\nlet result = {\nlet constant = fn(ignored) {\n42\n}\nconstant\n}\n()\n}\n";
    let ambiguous = failure("ambiguous-type.ash", ambiguous_text);
    let PipelineFailure::Typing(TypeError::Source(ambiguous)) = ambiguous else {
        panic!("ambiguous types should fail during typing");
    };
    assert_eq!(ambiguous.reason, TypeReason::AmbiguousType);
    let result_start = ambiguous_text
        .rfind("constant\n")
        .expect("ambiguous synthesized result");
    let result_end = result_start + "constant".len();
    assert_eq!(
        ambiguous.primary.span().range().start(),
        offset(result_start)
    );
    assert_eq!(ambiguous.primary.span().range().end(), offset(result_end));
}

#[test]
fn unused_global_body_inference_labels_its_causal_initializer() {
    let text = "type Option<A> =\nNone\n| Some(A)\n\nunused : Unit -> Unit\nunused _ = {\nlet value = None\n()\n}\n\nmain : Unit -> Unit\nmain () = ()\n";
    let error = failure("unused-global-inference.ash", text);
    let PipelineFailure::Typing(TypeError::Source(error)) = error else {
        panic!("unsolved inference should be a source typing diagnostic")
    };
    let none_start = text.rfind("None").expect("initializer occurrence");

    assert_eq!(error.reason, TypeReason::AmbiguousType);
    assert_eq!(error.primary.span().range().start(), offset(none_start));
    assert_eq!(error.primary.span().range().end(), offset(none_start + 4));
}

#[test]
fn local_nominal_escape_labels_outward_expression_and_declaration() {
    let text = concat!(
        "main : Unit -> Int\n",
        "main () = {\n",
        "    let escaped = {\n",
        "        newtype Hidden = Hidden(Int)\n",
        "        Hidden(1)\n",
        "    }\n",
        "    0\n",
        "}\n",
    );
    let PipelineFailure::Typing(TypeError::Source(error)) =
        failure("local-nominal-escape.ash", text)
    else {
        panic!("local nominal escape should fail during typing")
    };
    assert_eq!(error.reason, TypeReason::LocalNominalEscape);
    assert_eq!(
        error.primary.span().range().start(),
        offset(text.find("Hidden(1)").expect("escaping expression")),
    );
    assert_eq!(error.related.len(), 1);
    assert_eq!(
        error.related[0].span().range().start(),
        offset(text.find("newtype Hidden").expect("local declaration")),
    );
}
