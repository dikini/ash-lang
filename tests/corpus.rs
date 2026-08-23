use std::{fs, path::Path, process::Command};

use ash::{
    driver::{PipelineFailure, run_source},
    elaborate::{TypeError, TypeReason},
    lexer::LexReason,
    parser::ParseReason,
    resolve::ResolveReason,
    source::SourceFile,
};

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
];

const INVALID_CASES: &[InvalidCase] = &[
    InvalidCase {
        id: "P-001",
        path: "tests/fixtures/first-stratum/parse/p001-missing-result.ash",
        stage: Stage::Parser,
        reason: ExpectedReason::Parser {
            parser: &[ParseReason::ExpectedResult],
            lexical: &[],
        },
    },
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
            parser: &[ParseReason::PolymorphicHeader],
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

fn source(case: &InvalidCase) -> SourceFile {
    let text = fs::read_to_string(case.path)
        .unwrap_or_else(|error| panic!("{} could not read {}: {error}", case.id, case.path));
    SourceFile::new(case.path, text)
        .unwrap_or_else(|error| panic!("{} could not admit its fixture: {error}", case.id))
}

#[test]
fn every_valid_corpus_presentation_has_its_exact_library_and_cli_observation() {
    for case in VALID_CASES {
        let text = fs::read_to_string(case.path)
            .unwrap_or_else(|error| panic!("{} could not read {}: {error}", case.id, case.path));
        let source = SourceFile::new(case.path, text)
            .unwrap_or_else(|error| panic!("{} could not admit its fixture: {error}", case.id));
        let observation = run_source(source)
            .unwrap_or_else(|error| panic!("{} was rejected by {error}", case.id));

        assert_eq!(
            observation.value.to_string(),
            case.expected_value,
            "{}",
            case.id
        );
        assert_eq!(
            observation.ty.to_string(),
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
        let failure = match run_source(source(case)) {
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

fn assert_source_reason(case: &InvalidCase, failure: &PipelineFailure) {
    match (case.stage, case.reason, failure) {
        (
            Stage::Lexical,
            ExpectedReason::Lexical { lexical, parser },
            PipelineFailure::Syntax(actual),
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
            PipelineFailure::Syntax(actual),
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
            PipelineFailure::Resolution(actual),
        ) => assert_eq!(actual.reason, expected, "{}", case.id),
        (
            Stage::Typing,
            ExpectedReason::Typing(expected),
            PipelineFailure::Typing(TypeError::Source(actual)),
        ) => assert_eq!(actual.reason, expected, "{}", case.id),
        _ => panic!(
            "{} expected {:?} at {:?}, found {failure:?}",
            case.id, case.reason, case.stage
        ),
    }
}

#[test]
fn bare_carriage_return_is_a_structured_lexical_rejection() {
    let source = SourceFile::new("bare-cr.ash", "1\r2")
        .expect("the excluded source should fit the source model");
    let failure = run_source(source).expect_err("bare CR must not reach evaluation");
    let PipelineFailure::Syntax(actual) = failure else {
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
    let source = SourceFile::new("mixed-syntax.ash", "@\n(1\n")
        .expect("the mixed invalid source should fit the source model");
    let failure = run_source(source).expect_err("invalid source must not reach evaluation");
    let PipelineFailure::Syntax(actual) = failure else {
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
        vec![ParseReason::UnclosedGroup]
    );
}

#[test]
fn a_missing_result_after_a_complete_global_survives_an_earlier_lexical_failure() {
    let text = "@\nfn identity(value : Int) -> Int {\n    value\n}\n";
    let source = SourceFile::new("mixed-missing-result.ash", text)
        .expect("the mixed invalid source should fit the source model");
    let failure = run_source(source).expect_err("invalid source must not reach evaluation");
    let PipelineFailure::Syntax(actual) = failure else {
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
        vec![ParseReason::ExpectedResult]
    );
}

#[test]
fn an_excluded_result_after_a_complete_global_has_only_its_lexical_reason() {
    for (result, expected) in [
        ("-1\n", LexReason::NegativeLiteral),
        ("café\n", LexReason::UnicodeIdentifier),
        ("01\n", LexReason::InvalidIntegerLiteral),
    ] {
        let text = format!("identity : Int -> Int\nidentity value = value\n\n{result}");
        let source = SourceFile::new("excluded-result.ash", text)
            .expect("the excluded source should fit the source model");
        let failure = run_source(source).expect_err("invalid source must not reach evaluation");
        let PipelineFailure::Syntax(actual) = failure else {
            panic!("the excluded result should fail in the syntax pipeline");
        };

        assert_eq!(
            actual
                .lexical
                .iter()
                .map(|item| item.reason)
                .collect::<Vec<_>>(),
            vec![expected]
        );
        assert!(actual.parser.is_empty(), "result: {result:?}");
    }
}

#[test]
fn a_non_expression_lexical_tail_does_not_hide_a_missing_result() {
    for (tail, expected) in [
        ("// no result\n", LexReason::Comment),
        ("\u{feff}\n", LexReason::ByteOrderMark),
        ("\r", LexReason::BareCarriageReturn),
        ("@\n", LexReason::UnknownCharacter),
    ] {
        let text = format!("fn identity(value : Int) -> Int {{\n    value\n}}\n\n{tail}");
        let source = SourceFile::new("missing-result-after-trivia.ash", text)
            .expect("the excluded source should fit the source model");
        let failure = run_source(source).expect_err("invalid source must not reach evaluation");
        let PipelineFailure::Syntax(actual) = failure else {
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
        assert_eq!(
            actual
                .parser
                .iter()
                .map(|item| item.reason)
                .collect::<Vec<_>>(),
            vec![ParseReason::ExpectedResult],
            "tail: {tail:?}"
        );
    }
}

#[test]
fn an_expression_shaped_failure_on_the_definition_line_does_not_hide_a_missing_result() {
    for (tail, expected) in [
        ("-1", LexReason::NegativeLiteral),
        ("café", LexReason::UnicodeIdentifier),
        ("01", LexReason::InvalidIntegerLiteral),
    ] {
        let text = format!("identity : Int -> Int\nidentity value = value {tail}\n");
        let source = SourceFile::new("missing-result-after-definition.ash", text)
            .expect("the excluded source should fit the source model");
        let failure = run_source(source).expect_err("invalid source must not reach evaluation");
        let PipelineFailure::Syntax(actual) = failure else {
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
        assert_eq!(
            actual
                .parser
                .iter()
                .map(|item| item.reason)
                .collect::<Vec<_>>(),
            vec![ParseReason::ExpectedResult],
            "tail: {tail:?}"
        );
    }
}
