use ash::{
    core::validate,
    driver::{PipelineFailure, run_source},
    elaborate::{Elaborator, TypeError, TypeReason},
    eval::evaluate,
    lexer::lex,
    parser::{parse, project},
    resolve::resolve,
    source::SourceFile,
    types::Type,
};

fn run(text: &str) -> ash::driver::Observation {
    run_source(SourceFile::new("recursion.ash", text).expect("fixture should fit"))
        .expect("fixture should run")
}

fn typing_error(text: &str) -> Box<ash::diagnostic::Diagnostic<TypeReason>> {
    let error = run_source(SourceFile::new("recursion.ash", text).expect("fixture should fit"))
        .expect_err("fixture should fail typing");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("expected a source typing error, found {error:?}")
    };
    diagnostic
}

#[test]
fn global_presentations_share_recursive_scope_and_evaluate() {
    let observation = run(
        "first : Unit -> Int\nfirst ignored = second ()\n\nfn second(ignored : Unit) -> Int {\nlet retain : Unit -> Int = fn(value) {\nfirst value\n}\n42\n}\n\nfirst ()\n",
    );

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty, Type::Int);
}

#[test]
fn local_recursive_group_evaluates_through_the_same_core_form() {
    let observation = run(
        "{\nlet rec first : Unit -> Int = fn(ignored) {\nsecond ()\n}\nand second : Unit -> Int = fn(ignored) {\nlet retain : Unit -> Int = fn(value) {\nfirst value\n}\n42\n}\nfirst ()\n}\n",
    );

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty, Type::Int);
}

#[test]
fn recursive_closure_uses_its_definition_environment_not_its_caller() {
    let observation = run(
        "{\nlet captured = 42\nlet rec read : Unit -> Int = fn(ignored) {\ncaptured\n}\nlet caller : Unit -> Int = fn(ignored) {\nlet captured = 0\nread ()\n}\ncaller ()\n}\n",
    );

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty, Type::Int);
}

#[test]
fn recursive_initialization_requires_a_direct_anonymous_function() {
    for text in [
        "{\nlet rec value : Int = 1\nvalue\n}\n",
        "{\nlet rec value : Unit -> Int = {\nlet candidate : Unit -> Int = fn(ignored) {\n1\n}\ncandidate\n}\nvalue ()\n}\n",
    ] {
        let diagnostic = typing_error(text);
        assert_eq!(diagnostic.reason, TypeReason::UnsafeRecursiveInitializer);
        assert_eq!(
            diagnostic.reason.to_string(),
            "recursion.unsafe-initializer"
        );
        assert_eq!(diagnostic.related.len(), 2);
        assert_eq!(
            diagnostic.expected.as_deref(),
            Some("a direct `fn` initializer")
        );
        assert!(
            diagnostic
                .help
                .as_deref()
                .is_some_and(|help| help.contains("directly with `fn`"))
        );
    }
}

#[test]
fn recursive_members_are_checked_against_their_declared_monotypes() {
    let result_error =
        typing_error("{\nlet rec wrong : Unit -> Int = fn(ignored) {\ntrue\n}\nwrong ()\n}\n");
    assert_eq!(result_error.reason, TypeReason::BindingInitializer);
    assert_eq!(result_error.expected.as_deref(), Some("Int"));
    assert_eq!(result_error.found.as_deref(), Some("Bool"));

    let argument_error = typing_error(
        "{\nlet rec first : Unit -> Int = fn(ignored) {\nsecond 1\n}\nand second : Unit -> Int = fn(ignored) {\n42\n}\nfirst ()\n}\n",
    );
    assert_eq!(argument_error.reason, TypeReason::Argument);
    assert_eq!(argument_error.expected.as_deref(), Some("Unit"));
    assert_eq!(argument_error.found.as_deref(), Some("Int"));
}

#[test]
fn deep_recursive_group_and_call_chain_use_explicit_work_stacks() {
    const MEMBERS: usize = 10_000;
    let worker = std::thread::Builder::new()
        .name("deep-recursive-group".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            use std::fmt::Write as _;

            let mut text = String::from("{\n");
            for index in 0..MEMBERS {
                let introducer = if index == 0 { "let rec" } else { "and" };
                if index + 1 == MEMBERS {
                    writeln!(text, "{introducer} f{index} : Unit -> Int = fn(ignored) {{")
                        .expect("String writing cannot fail");
                    text.push_str("let retain : Unit -> Int = fn(value) {\nf0 value\n}\n1\n}\n");
                } else {
                    writeln!(
                        text,
                        "{introducer} f{index} : Unit -> Int = fn(ignored) {{\n1 + f{} ()\n}}",
                        index + 1
                    )
                    .expect("String writing cannot fail");
                }
            }
            text.push_str("f0 ()\n}\n");

            let source = SourceFile::new("deep-recursion.ash", text).expect("fixture should fit");
            let tree = parse(lex(&source).expect("fixture should lex"));
            assert!(tree.parse_diagnostics().is_empty());
            let surface = project(&source, &tree).expect("fixture should project");
            let resolved = resolve(&surface).expect("fixture should resolve");
            let mut elaborator =
                Elaborator::for_program(&resolved).expect("binder namespace should fit");
            let typed = elaborator
                .synthesize_program(&resolved)
                .expect("fixture should elaborate");
            let unchecked = elaborator.finish(typed.node).expect("root should finish");
            let validated = validate(unchecked, &[&source]).expect("Core should validate");
            let evaluation = evaluate(&validated).expect("recursive chain should evaluate");

            assert_eq!(evaluation.value.to_string(), MEMBERS.to_string());
            assert!(evaluation.trace.len() > MEMBERS * 5);
        })
        .expect("depth-test thread should start");

    worker
        .join()
        .expect("recursive pipeline and destruction should stay within the host stack budget");
}
