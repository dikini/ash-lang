use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

mod support;

use ash::{
    driver::{FileFailure, PipelineFailure, RunConfiguration, SyntaxFailure, run_path},
    elaborate::{TypeError, TypeReason, check_module},
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
    let failure = failure(case.name, &case.source);
    let PipelineFailure::Kind(KindFailure::Source(error)) = failure else {
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
    let FileFailure::Graph(LoadGraphError::Syntax(syntax)) = &file_error else {
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
    assert!(error.found.is_none());
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
    assert!(error.expected.is_none() && error.found.is_none() && error.help.is_none());

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
    assert!(error.found.is_none());
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
            KindReason::ExpectedType,
            ("Option", 1),
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
            KindReason::ExpectedType,
            ("Option", 1),
        ),
        (
            "kind-precedence-inline-result.ash",
            format!(
                "{OPTION}{HIGHER}fn bad(value : Unit) -> Option where Higher<Bool> {{\nlet local : Option = None\nvalue\n}}\n"
            ),
            KindReason::ExpectedType,
            ("Option", 1),
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
