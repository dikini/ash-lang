use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{FileFailure, PipelineFailure, RunConfiguration, run_path},
    elaborate::{TypeError, TypeReason},
    lexer::LexReason,
    module::{LoadGraphError, ModuleRoots},
    parser::ParseReason,
    resolve::ResolveReason,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempSource(PathBuf);

impl TempSource {
    fn write(text: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-corpus-inline-{}-{id}.ash", std::process::id()));
            match fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&path)
            {
                Ok(mut file) => {
                    use std::io::Write as _;
                    file.write_all(text.as_bytes())
                        .expect("the inline corpus source should be writable");
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("the inline corpus source should be creatable: {error}"),
            }
        }
    }
}

impl Drop for TempSource {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

struct ValidCase {
    id: &'static str,
    path: &'static str,
    expected_value: &'static str,
    expected_type: &'static str,
    expected_stdout: &'static str,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Stage {
    Lexical,
    Parser,
    Resolution,
    Typing,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ExpectedReason {
    Lexical {
        lexical: &'static [LexReason],
        parser: &'static [ParseReason],
    },
    Parser {
        parser: &'static [ParseReason],
        lexical: &'static [LexReason],
    },
    Resolution(ResolveReason),
    Typing(TypeReason),
}

struct InvalidCase {
    id: &'static str,
    path: &'static str,
    stage: Stage,
    reason: ExpectedReason,
}

struct MigrationCase {
    id: &'static str,
    path: &'static str,
    predecessor_outcome: &'static str,
    implemented_outcome: &'static str,
}

const MIGRATION_CASES: &[MigrationCase] = &[
    MigrationCase {
        id: "unsaturated-nominal",
        path: "tests/fixtures/explicit-kinds/migration-unsaturated-nominal.ash",
        predecessor_outcome: "resolve.type-argument-count",
        implemented_outcome: "kind.expected-type",
    },
    MigrationCase {
        id: "applied-Type-binder",
        path: "tests/fixtures/explicit-kinds/migration-applied-type-binder.ash",
        predecessor_outcome: "resolve.type-kind",
        implemented_outcome: "kind.not-applicable",
    },
    MigrationCase {
        id: "lowercase-inline-binder",
        path: "tests/fixtures/first-stratum/parse/excluded-polymorphism.ash",
        predecessor_outcome: "parse.polymorphic-header",
        implemented_outcome: "parse.expected-form",
    },
    MigrationCase {
        id: "uppercase-inline-binder",
        path: "tests/fixtures/explicit-kinds/migration-explicit-inline-binder.ash",
        predecessor_outcome: "parse.polymorphic-header",
        implemented_outcome: "accepted",
    },
];

const VALID_CASES: &[ValidCase] = &[
    ValidCase {
        id: "V-001",
        path: "tests/fixtures/first-stratum/valid/v001-precedence.ash",
        expected_value: "7",
        expected_type: "Int",
        expected_stdout: "7 : Int\n",
    },
    ValidCase {
        id: "V-002-equational",
        path: "tests/fixtures/first-stratum/valid/v002-equational.ash",
        expected_value: "42",
        expected_type: "Int",
        expected_stdout: "42 : Int\n",
    },
    ValidCase {
        id: "V-002-operational",
        path: "tests/fixtures/first-stratum/valid/v002-operational.ash",
        expected_value: "42",
        expected_type: "Int",
        expected_stdout: "42 : Int\n",
    },
    ValidCase {
        id: "V-003",
        path: "tests/fixtures/first-stratum/valid/v003-local-shadowing.ash",
        expected_value: "2",
        expected_type: "Int",
        expected_stdout: "2 : Int\n",
    },
    ValidCase {
        id: "V-004",
        path: "tests/fixtures/first-stratum/valid/v004-capture.ash",
        expected_value: "42",
        expected_type: "Int",
        expected_stdout: "42 : Int\n",
    },
    ValidCase {
        id: "V-005",
        path: "tests/fixtures/first-stratum/valid/v005-higher-order.ash",
        expected_value: "42",
        expected_type: "Int",
        expected_stdout: "42 : Int\n",
    },
    ValidCase {
        id: "V-006",
        path: "tests/fixtures/first-stratum/valid/v006-unit.ash",
        expected_value: "()",
        expected_type: "Unit",
        expected_stdout: "() : Unit\n",
    },
    ValidCase {
        id: "V-007",
        path: "tests/fixtures/first-stratum/valid/v007-equality.ash",
        expected_value: "true",
        expected_type: "Bool",
        expected_stdout: "true : Bool\n",
    },
    ValidCase {
        id: "V-008",
        path: "tests/fixtures/first-stratum/valid/v008-mixed.ash",
        expected_value: "42",
        expected_type: "Int",
        expected_stdout: "42 : Int\n",
    },
    ValidCase {
        id: "recursion-global-mutual",
        path: "tests/fixtures/recursion/valid/global-mutual.ash",
        expected_value: "42",
        expected_type: "Int",
        expected_stdout: "42 : Int\n",
    },
    ValidCase {
        id: "recursion-local-mutual",
        path: "tests/fixtures/recursion/valid/local-mutual.ash",
        expected_value: "42",
        expected_type: "Int",
        expected_stdout: "42 : Int\n",
    },
    ValidCase {
        id: "local-polymorphic-function",
        path: "tests/fixtures/first-stratum/valid/local-polymorphic-function.ash",
        expected_value: "1",
        expected_type: "Int",
        expected_stdout: "1 : Int\n",
    },
    ValidCase {
        id: "migration-explicit-inline-binder",
        path: "tests/fixtures/explicit-kinds/migration-explicit-inline-binder.ash",
        expected_value: "42",
        expected_type: "Int",
        expected_stdout: "42 : Int\n",
    },
    ValidCase {
        id: "ordinary-Type-nominal",
        path: "tests/fixtures/explicit-kinds/ordinary-type-nominal.ash",
        expected_value: "Type",
        expected_type: "Type",
        expected_stdout: "Type : Type\n",
    },
];

const INVALID_CASES: &[InvalidCase] = &[
    InvalidCase {
        id: "P-002",
        path: "tests/fixtures/first-stratum/parse/p002-unclosed-group.ash",
        stage: Stage::Parser,
        reason: ExpectedReason::Parser {
            parser: &[ParseReason::UnclosedGroup],
            lexical: &[],
        },
    },
    InvalidCase {
        id: "P-003",
        path: "tests/fixtures/first-stratum/parse/p003-independent-recovery.ash",
        stage: Stage::Parser,
        reason: ExpectedReason::Parser {
            parser: &[ParseReason::ExpectedOperand, ParseReason::UnclosedGroup],
            lexical: &[],
        },
    },
    InvalidCase {
        id: "excluded-polymorphism",
        path: "tests/fixtures/first-stratum/parse/excluded-polymorphism.ash",
        stage: Stage::Parser,
        reason: ExpectedReason::Parser {
            parser: &[ParseReason::ExpectedForm],
            lexical: &[],
        },
    },
    InvalidCase {
        id: "excluded-semicolon",
        path: "tests/fixtures/first-stratum/parse/excluded-semicolon.ash",
        stage: Stage::Parser,
        reason: ExpectedReason::Parser {
            parser: &[ParseReason::Semicolon],
            lexical: &[],
        },
    },
    InvalidCase {
        id: "excluded-comment",
        path: "tests/fixtures/first-stratum/parse/excluded-comment.ash",
        stage: Stage::Lexical,
        reason: ExpectedReason::Lexical {
            lexical: &[LexReason::Comment],
            parser: &[],
        },
    },
    InvalidCase {
        id: "excluded-negative-literal",
        path: "tests/fixtures/first-stratum/parse/excluded-negative-literal.ash",
        stage: Stage::Lexical,
        reason: ExpectedReason::Lexical {
            lexical: &[LexReason::NegativeLiteral],
            parser: &[],
        },
    },
    InvalidCase {
        id: "excluded-unicode-identifier",
        path: "tests/fixtures/first-stratum/parse/excluded-unicode-identifier.ash",
        stage: Stage::Lexical,
        reason: ExpectedReason::Lexical {
            lexical: &[LexReason::UnicodeIdentifier],
            parser: &[],
        },
    },
    InvalidCase {
        id: "excluded-byte-order-mark",
        path: "tests/fixtures/first-stratum/parse/excluded-bom.ash",
        stage: Stage::Lexical,
        reason: ExpectedReason::Lexical {
            lexical: &[LexReason::ByteOrderMark],
            parser: &[],
        },
    },
    InvalidCase {
        id: "R-001",
        path: "tests/fixtures/first-stratum/resolve/r001-unknown-name.ash",
        stage: Stage::Resolution,
        reason: ExpectedReason::Resolution(ResolveReason::UnknownName),
    },
    InvalidCase {
        id: "R-002",
        path: "tests/fixtures/first-stratum/resolve/r002-duplicate-global.ash",
        stage: Stage::Resolution,
        reason: ExpectedReason::Resolution(ResolveReason::DuplicateGlobal),
    },
    InvalidCase {
        id: "equation-name-mismatch",
        path: "tests/fixtures/first-stratum/resolve/equation-name-mismatch.ash",
        stage: Stage::Resolution,
        reason: ExpectedReason::Resolution(ResolveReason::EquationNameMismatch),
    },
    InvalidCase {
        id: "T-001",
        path: "tests/fixtures/first-stratum/type/t001-definition-result.ash",
        stage: Stage::Typing,
        reason: ExpectedReason::Typing(TypeReason::DefinitionResult),
    },
    InvalidCase {
        id: "T-002",
        path: "tests/fixtures/first-stratum/type/t002-operator-operand.ash",
        stage: Stage::Typing,
        reason: ExpectedReason::Typing(TypeReason::OperatorOperand),
    },
    InvalidCase {
        id: "T-003",
        path: "tests/fixtures/first-stratum/type/t003-not-applicable.ash",
        stage: Stage::Typing,
        reason: ExpectedReason::Typing(TypeReason::NotApplicable),
    },
    InvalidCase {
        id: "T-004",
        path: "tests/fixtures/first-stratum/type/t004-argument.ash",
        stage: Stage::Typing,
        reason: ExpectedReason::Typing(TypeReason::Argument),
    },
    InvalidCase {
        id: "equation-interface-not-function",
        path: "tests/fixtures/first-stratum/type/equation-interface-not-function.ash",
        stage: Stage::Typing,
        reason: ExpectedReason::Typing(TypeReason::EquationInterfaceNotFunction),
    },
    InvalidCase {
        id: "binding-initializer",
        path: "tests/fixtures/first-stratum/type/binding-initializer.ash",
        stage: Stage::Typing,
        reason: ExpectedReason::Typing(TypeReason::BindingInitializer),
    },
    InvalidCase {
        id: "function-needs-context",
        path: "tests/fixtures/first-stratum/type/function-needs-context.ash",
        stage: Stage::Typing,
        reason: ExpectedReason::Typing(TypeReason::FunctionNeedsContext),
    },
    InvalidCase {
        id: "function-result-needs-context",
        path: "tests/fixtures/first-stratum/type/function-result-needs-context.ash",
        stage: Stage::Typing,
        reason: ExpectedReason::Typing(TypeReason::FunctionNeedsContext),
    },
    InvalidCase {
        id: "function-non-function-context",
        path: "tests/fixtures/first-stratum/type/function-non-function-context.ash",
        stage: Stage::Typing,
        reason: ExpectedReason::Typing(TypeReason::FunctionNeedsContext),
    },
    InvalidCase {
        id: "recursion-unsafe-initializer",
        path: "tests/fixtures/recursion/type/unsafe-initializer.ash",
        stage: Stage::Typing,
        reason: ExpectedReason::Typing(TypeReason::UnsafeRecursiveRoot),
    },
];

fn ash(path: &Path) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_ash"))
        .arg(path)
        .output()
        .expect("the Ash executable should start")
}

fn run(path: impl Into<PathBuf>) -> Result<ash::driver::Observation, FileFailure> {
    run_path(RunConfiguration {
        entry: path.into(),
        roots: ModuleRoots::empty(),
    })
}

#[test]
fn every_valid_corpus_presentation_has_its_exact_library_and_cli_observation() {
    for case in VALID_CASES {
        let observation =
            run(case.path).unwrap_or_else(|error| panic!("{} was rejected by {error}", case.id));

        assert_eq!(
            observation.value().to_string(),
            case.expected_value,
            "{}",
            case.id
        );
        assert_eq!(
            observation.type_display(),
            case.expected_type,
            "{}",
            case.id
        );

        let output = ash(Path::new(case.path));
        assert_eq!(output.status.code(), Some(0), "{}: {output:?}", case.id);
        assert_eq!(
            output.stdout,
            case.expected_stdout.as_bytes(),
            "{}",
            case.id
        );
        assert!(output.stderr.is_empty(), "{}: {output:?}", case.id);
    }
}

#[test]
fn every_invalid_corpus_case_stops_at_its_owning_stage_and_cli_boundary() {
    for case in INVALID_CASES {
        let failure = match run(case.path) {
            Ok(_) => panic!("{} unexpectedly reached evaluation", case.id),
            Err(failure) => failure,
        };
        assert_source_reason(case, &failure);
        assert!(failure.is_source_rejection(), "{}: {failure:?}", case.id);

        let output = ash(Path::new(case.path));
        assert_eq!(output.status.code(), Some(1), "{}: {output:?}", case.id);
        assert!(output.stdout.is_empty(), "{}: {output:?}", case.id);
        assert!(!output.stderr.is_empty(), "{}: {output:?}", case.id);
    }
}

#[test]
fn explicit_kind_migration_matrix_records_every_predecessor_assertion_shift() {
    for case in MIGRATION_CASES {
        let actual = match run(case.path) {
            Ok(_) => "accepted".to_owned(),
            Err(failure) => failure.reason_code(),
        };
        assert_eq!(actual, case.implemented_outcome, "{}", case.id);
        assert_ne!(
            case.implemented_outcome, case.predecessor_outcome,
            "{}",
            case.id
        );
    }
}

#[test]
fn method_parameter_migration_and_exclusion_corpus_is_complete() {
    struct ExclusionCase {
        route: &'static str,
        source: &'static str,
        reason: &'static str,
    }

    let exclusions = [
        ExclusionCase {
            route: "source-forall",
            source: "main : forall A. A -> A\nmain value = value\n",
            reason: "parse.expected-form",
        },
        ExclusionCase {
            route: "expression-type-application",
            source: concat!(
                "identity<A> : A -> A\n",
                "identity value = value\n\n",
                "main : Unit -> Int\n",
                "main () = identity<Int> 42\n",
            ),
            reason: "parse.expected-form",
        },
        ExclusionCase {
            route: "polymorphic-parameter-annotation",
            source: "fn consume(value : forall A. A -> A) -> Int {\n0\n}\n",
            reason: "parse.expected-form",
        },
        ExclusionCase {
            route: "polymorphic-result-annotation",
            source: "fn produce(value : Unit) -> forall A. A -> A {\nfn(item) { item }\n}\n",
            reason: "parse.expected-form",
        },
        ExclusionCase {
            route: "polymorphic-tuple-field",
            source: "bad : (Int, forall A. A -> A) -> Int\nbad pair = 0\n",
            reason: "parse.expected-form",
        },
        ExclusionCase {
            route: "polymorphic-constructor-field",
            source: "type Box = Box(forall A. A -> A)\n",
            reason: "parse.expected-form",
        },
        ExclusionCase {
            route: "method-scheme-storage",
            source: concat!(
                "interface Project<I> {\nproject<A> : I -> (I, A)\n}\n\n",
                "store : Int -> Unit where Project<Int>\n",
                "store value = {\nlet stored = project\n()\n}\n",
            ),
            reason: "constraint.ambiguous",
        },
        ExclusionCase {
            route: "method-scheme-return",
            source: concat!(
                "interface Project<I> {\nproject<A> : I -> (I, A)\n}\n\n",
                "fn return_project(value : Int) -> forall A. Int -> (Int, A) ",
                "where Project<Int> {\nproject\n}\n",
            ),
            reason: "parse.expected-form",
        },
        ExclusionCase {
            route: "method-scheme-ordinary-parameter",
            source: concat!(
                "interface Project<I> {\nproject<A> : I -> (I, A)\n}\n\n",
                "fn consume<A>(poly : Int -> (Int, A)) -> Unit {\n()\n}\n",
                "pass : Int -> Unit where Project<Int>\n",
                "pass value = consume(project)\n",
            ),
            reason: "type.ambiguous",
        },
        ExclusionCase {
            route: "implicit-method-binder",
            source: "interface Project<I> {\nproject : I -> (I, A)\n}\n",
            reason: "interface.method-parameter",
        },
        ExclusionCase {
            route: "method-requirement",
            source: concat!(
                "interface Project<I> {\n",
                "project<A> : I -> (I, A) where Project<A>\n",
                "}\n",
            ),
            reason: "parse.expected-form",
        },
        ExclusionCase {
            route: "polymorphic-recursive-method-self-use",
            source: concat!(
                "interface Repeat<I> {\nrepeat<A> : (I, A) -> A\n}\n\n",
                "impl Repeat<Int> {\n",
                "repeat (owner, value) = repeat((owner, (value, value)))\n",
                "}\n",
            ),
            reason: "type.polymorphic-recursion",
        },
    ];
    assert_eq!(exclusions.len(), 12);
    for case in exclusions {
        let source = TempSource::write(case.source);
        let failure = match run(source.0.clone()) {
            Ok(_) => panic!("{} unexpectedly reached evaluation", case.route),
            Err(failure) => failure,
        };
        assert_eq!(failure.reason_code(), case.reason, "{}", case.route);

        let output = ash(&source.0);
        assert_eq!(output.status.code(), Some(1), "{}: {output:?}", case.route);
        assert!(output.stdout.is_empty(), "{}: {output:?}", case.route);
        assert!(
            output
                .stderr
                .starts_with(format!("{}\n", case.reason).as_bytes()),
            "{}: {output:?}",
            case.route,
        );
    }

    let predecessor = TempSource::write(concat!(
        "interface Project<I> {\nproject : (I, A) -> A\n}\n\n",
        "impl Project<Int> {\nproject (owner, value) = value\n}\n\n",
        "main : Unit -> Int\nmain () = project((0, 42))\n",
    ));
    let predecessor_failure =
        run(predecessor.0.clone()).expect_err("the absent-list predecessor must stay rejected");
    assert_eq!(
        predecessor_failure.reason_code(),
        "interface.method-parameter"
    );
    let predecessor_cli = ash(&predecessor.0);
    assert_eq!(predecessor_cli.status.code(), Some(1));
    assert!(predecessor_cli.stdout.is_empty());
    assert!(
        predecessor_cli
            .stderr
            .starts_with(b"interface.method-parameter\n")
    );

    let explicit = TempSource::write(concat!(
        "interface Project<I> {\nproject<A> : (I, A) -> A\n}\n\n",
        "impl Project<Int> {\nproject (owner, value) = value\n}\n\n",
        "main : Unit -> Int\nmain () = project((0, 42))\n",
    ));
    let observation = run(explicit.0.clone())
        .expect("adding the complete explicit method list should make the program valid");
    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
    let explicit_cli = ash(&explicit.0);
    assert_eq!(explicit_cli.status.code(), Some(0));
    assert_eq!(explicit_cli.stdout, b"42 : Int\n");
    assert!(explicit_cli.stderr.is_empty());
}

fn assert_source_reason(case: &InvalidCase, failure: &FileFailure) {
    match (case.stage, case.reason, failure) {
        (
            Stage::Lexical,
            ExpectedReason::Lexical { lexical, parser },
            FileFailure::Graph(LoadGraphError::Syntax(actual)),
        ) => {
            assert_eq!(actual.resource, None, "{}", case.id);
            assert_eq!(
                actual
                    .lexical
                    .iter()
                    .map(|item| item.reason)
                    .collect::<Vec<_>>(),
                lexical,
                "{}",
                case.id
            );
            assert_eq!(
                actual
                    .parser
                    .iter()
                    .map(|item| item.reason)
                    .collect::<Vec<_>>(),
                parser,
                "{}",
                case.id
            );
        }
        (
            Stage::Parser,
            ExpectedReason::Parser { parser, lexical },
            FileFailure::Graph(LoadGraphError::Syntax(actual)),
        ) => {
            assert_eq!(actual.resource, None, "{}", case.id);
            assert_eq!(
                actual
                    .lexical
                    .iter()
                    .map(|item| item.reason)
                    .collect::<Vec<_>>(),
                lexical,
                "{}",
                case.id
            );
            assert_eq!(
                actual
                    .parser
                    .iter()
                    .map(|item| item.reason)
                    .collect::<Vec<_>>(),
                parser,
                "{}",
                case.id
            );
        }
        (
            Stage::Resolution,
            ExpectedReason::Resolution(expected),
            FileFailure::Pipeline(PipelineFailure::Resolution(actual)),
        ) => assert_eq!(actual.reason, expected, "{}", case.id),
        (
            Stage::Typing,
            ExpectedReason::Typing(expected),
            FileFailure::Pipeline(PipelineFailure::Typing(TypeError::Source(actual))),
        ) => assert_eq!(actual.reason, expected, "{}", case.id),
        _ => panic!(
            "{} expected {:?} at {:?}, found {failure:?}",
            case.id, case.reason, case.stage
        ),
    }
}

#[test]
fn bare_carriage_return_is_a_structured_lexical_rejection() {
    let source = TempSource::write("\rmain : Unit -> Int\nmain () = 1\n");
    let failure = run(source.0.clone()).expect_err("bare CR must not reach evaluation");
    let FileFailure::Graph(LoadGraphError::Syntax(actual)) = failure else {
        panic!("bare CR should fail in the syntax pipeline");
    };
    assert_eq!(
        actual
            .lexical
            .iter()
            .map(|item| item.reason)
            .collect::<Vec<_>>(),
        vec![LexReason::BareCarriageReturn]
    );
    assert!(actual.parser.is_empty());
}

#[test]
fn an_independent_parser_failure_survives_an_earlier_lexical_failure() {
    let source = TempSource::write("$\nmain : Unit -> Bool\nmain () = true == false == true\n");
    let failure = run(source.0.clone()).expect_err("invalid source must not reach evaluation");
    let FileFailure::Graph(LoadGraphError::Syntax(actual)) = failure else {
        panic!("the mixed source should fail in the syntax pipeline");
    };

    assert_eq!(
        actual
            .lexical
            .iter()
            .map(|item| item.reason)
            .collect::<Vec<_>>(),
        vec![LexReason::UnknownCharacter]
    );
    assert_eq!(
        actual
            .parser
            .iter()
            .map(|item| item.reason)
            .collect::<Vec<_>>(),
        vec![ParseReason::RepeatedEquality]
    );
}

#[test]
fn a_complete_module_retains_an_independent_lexical_failure() {
    let text = "$\nfn identity(value : Int) -> Int {\n    value\n}\n";
    let source = TempSource::write(text);
    let failure = run(source.0.clone()).expect_err("invalid source must not reach evaluation");
    let FileFailure::Graph(LoadGraphError::Syntax(actual)) = failure else {
        panic!("the mixed source should fail in the syntax pipeline");
    };

    assert_eq!(
        actual
            .lexical
            .iter()
            .map(|item| item.reason)
            .collect::<Vec<_>>(),
        vec![LexReason::UnknownCharacter]
    );
    assert!(actual.parser.is_empty());
}

#[test]
fn a_lexically_rejected_line_after_complete_declarations_has_only_its_lexical_reason() {
    for (line, expected) in [
        ("-1\n", LexReason::NegativeLiteral),
        ("café\n", LexReason::UnicodeIdentifier),
        ("01\n", LexReason::InvalidIntegerLiteral),
    ] {
        let text = format!("identity : Int -> Int\nidentity value = value\n\n{line}");
        let source = TempSource::write(&text);
        let failure = run(source.0.clone()).expect_err("invalid source must not reach evaluation");
        let FileFailure::Graph(LoadGraphError::Syntax(actual)) = failure else {
            panic!("the excluded line should fail in the syntax pipeline");
        };

        assert_eq!(
            actual
                .lexical
                .iter()
                .map(|item| item.reason)
                .collect::<Vec<_>>(),
            vec![expected]
        );
        assert!(actual.parser.is_empty(), "line: {line:?}");
    }
}

#[test]
fn a_lexically_rejected_tail_does_not_create_a_parser_diagnostic() {
    for (tail, expected) in [
        ("// unavailable comment\n", LexReason::Comment),
        ("\u{feff}\n", LexReason::ByteOrderMark),
        ("\r", LexReason::BareCarriageReturn),
        ("$\n", LexReason::UnknownCharacter),
    ] {
        let text = format!("fn identity(value : Int) -> Int {{\n    value\n}}\n\n{tail}");
        let source = TempSource::write(&text);
        let failure = run(source.0.clone()).expect_err("invalid source must not reach evaluation");
        let FileFailure::Graph(LoadGraphError::Syntax(actual)) = failure else {
            panic!("the excluded tail should fail in the syntax pipeline");
        };

        assert_eq!(
            actual
                .lexical
                .iter()
                .map(|item| item.reason)
                .collect::<Vec<_>>(),
            vec![expected]
        );
        assert!(actual.parser.is_empty(), "tail: {tail:?}");
    }
}

#[test]
fn a_lexically_rejected_definition_tail_does_not_create_a_parser_diagnostic() {
    for (tail, expected) in [
        ("-1", LexReason::NegativeLiteral),
        ("café", LexReason::UnicodeIdentifier),
        ("01", LexReason::InvalidIntegerLiteral),
    ] {
        let text = format!("identity : Int -> Int\nidentity value = value {tail}\n");
        let source = TempSource::write(&text);
        let failure = run(source.0.clone()).expect_err("invalid source must not reach evaluation");
        let FileFailure::Graph(LoadGraphError::Syntax(actual)) = failure else {
            panic!("the excluded definition tail should fail in the syntax pipeline");
        };

        assert_eq!(
            actual
                .lexical
                .iter()
                .map(|item| item.reason)
                .collect::<Vec<_>>(),
            vec![expected]
        );
        assert!(actual.parser.is_empty(), "tail: {tail:?}");
    }
}
