mod support;

use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::validate_modules,
    driver::PipelineFailure,
    elaborate::{Elaborator, TypeError, TypeReason, check_module, link_modules},
    eval::{Evaluation, evaluate},
    evidence_validation::validate_interface_evidence,
    module::{ModuleRoots, load_module_graph},
    resolve::resolve_module,
    types::Type,
};
use support::run_module;

static CORE_TEMP_IDS: AtomicU64 = AtomicU64::new(0);

fn run(text: &str) -> ash::driver::Observation {
    run_module("recursion.ash", text).expect("fixture should run")
}

fn typing_error(text: &str) -> Box<ash::diagnostic::Diagnostic<TypeReason>> {
    let error = run_module("recursion.ash", text).expect_err("fixture should fail typing");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("expected a source typing error, found {error:?}")
    };
    diagnostic
}

fn evaluate_module(text: &str) -> Evaluation {
    let directory = loop {
        let id = CORE_TEMP_IDS.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("ash-recursive-core-{}-{id}", std::process::id()));
        match fs::create_dir(&path) {
            Ok(()) => break path,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("recursive fixture directory should be creatable: {error}"),
        }
    };
    let entry_path = directory.join("recursion.ash");
    fs::write(&entry_path, text).expect("recursive fixture should be writable");
    let graph = load_module_graph(&entry_path, &ModuleRoots::empty())
        .expect("recursive fixture should load");
    let resolved = resolve_module(&graph.modules()[0], &[]).expect("fixture should resolve");
    let checked = check_module(resolved).expect("fixture should check");
    let linked = link_modules(vec![checked], graph.entry()).expect("fixture should link");
    let linked = validate_interface_evidence(linked).expect("linked evidence should validate");
    let mut elaborator =
        Elaborator::for_module_program(&linked).expect("binder namespace should fit");
    let typed = elaborator
        .synthesize_module_program(&linked)
        .expect("fixture should elaborate");
    let unchecked = elaborator.finish(typed.node).expect("root should finish");
    let source = graph.modules()[0].source();
    let validated = validate_modules(unchecked, &[source], &[(graph.entry(), source.id())])
        .expect("Core should validate");
    let evaluation = evaluate(&validated).expect("recursive chain should evaluate");
    let _ = fs::remove_dir_all(directory);
    evaluation
}

#[test]
fn global_presentations_share_recursive_scope_and_evaluate() {
    let observation = run(
        "first : Unit -> Int\nfirst ignored = second ()\n\nfn second(ignored : Unit) -> Int {\nlet retain : Unit -> Int = fn(value) {\nfirst value\n}\n42\n}\n\nmain : Unit -> Int\nmain () = first ()\n",
    );

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty, Type::Int);
}

#[test]
fn implementation_method_recurses_through_current_evidence() {
    let observation = run(
        "type Counter =\nStop\n| More(Counter)\n\ninterface Countdown<A> {\ncountdown : A -> Int\n}\n\nimpl Countdown<Counter> {\ncountdown Stop = 42\ncountdown (More(rest)) = countdown rest\n}\n\nmain : Unit -> Int\nmain () = countdown(More(More(Stop)))\n",
    );

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty, Type::Int);
}

#[test]
fn implementation_methods_share_mutual_recursive_scope() {
    let observation = run(
        "type Counter =\nStop\n| More(Counter)\n\ninterface Countdown<A> {\nfirst : A -> Int\nsecond : (A, Unit) -> Int\n}\n\nimpl Countdown<Counter> {\nfirst Stop = 42\nfirst (More(rest)) = second(rest, ())\nsecond (value, ()) = first value\n}\n\nmain : Unit -> Int\nmain () = first(More(More(Stop)))\n",
    );

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty, Type::Int);
}

#[test]
fn earlier_global_and_later_implementation_method_share_recursive_scope() {
    let observation = run(
        "type Counter =\nStop\n| More(Counter)\n\ninterface Countdown<A> {\ncountdown : A -> Int\n}\n\nadvance : Counter -> Int\nadvance Stop = 42\nadvance (More(rest)) = countdown rest\n\nimpl Countdown<Counter> {\ncountdown value = advance value\n}\n\nmain : Unit -> Int\nmain () = advance(More(More(Stop)))\n",
    );

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty, Type::Int);
}

#[test]
fn earlier_implementation_method_and_later_global_share_recursive_scope() {
    let observation = run(
        "type Counter =\nStop\n| More(Counter)\n\ninterface Countdown<A> {\ncountdown : A -> Int\n}\n\nimpl Countdown<Counter> {\ncountdown Stop = 42\ncountdown (More(rest)) = advance rest\n}\n\nadvance : Counter -> Int\nadvance value = countdown value\n\nmain : Unit -> Int\nmain () = countdown(More(More(Stop)))\n",
    );

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty, Type::Int);
}

#[test]
fn local_recursive_group_evaluates_through_the_same_core_form() {
    let observation = run(
        "main : Unit -> Int\nmain () = {\nlet rec first : Unit -> Int = fn(ignored) {\nsecond ()\n}\nand second : Unit -> Int = fn(ignored) {\nlet retain : Unit -> Int = fn(value) {\nfirst value\n}\n42\n}\nfirst ()\n}\n",
    );

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty, Type::Int);
}

#[test]
fn recursive_closure_uses_its_definition_environment_not_its_caller() {
    let observation = run(
        "main : Unit -> Int\nmain () = {\nlet captured = 42\nlet rec read : Unit -> Int = fn(ignored) {\ncaptured\n}\nlet caller : Unit -> Int = fn(ignored) {\nlet captured = 0\nread ()\n}\ncaller ()\n}\n",
    );

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty, Type::Int);
}

#[test]
fn recursive_initialization_requires_a_direct_anonymous_function() {
    let data = typing_error("main : Unit -> Int\nmain () = {\nlet rec value : Int = 1\nvalue\n}\n");
    assert_eq!(data.reason, TypeReason::UnsafeRecursiveRoot);
    assert_eq!(data.reason.to_string(), "recursion.unsafe-root");

    let function = typing_error(
        "main : Unit -> Int\nmain () = {\nlet rec value : Unit -> Int = {\nlet candidate : Unit -> Int = fn(ignored) {\n1\n}\ncandidate\n}\nvalue ()\n}\n",
    );
    assert_eq!(function.reason, TypeReason::UnsafeRecursiveInitializer);
    assert_eq!(function.reason.to_string(), "recursion.unsafe-initializer");
    assert_eq!(function.related.len(), 2);
    assert_eq!(
        function.expected.as_deref(),
        Some("a direct `fn` initializer")
    );
}

#[test]
fn recursive_members_are_checked_against_their_declared_monotypes() {
    let result_error = typing_error(
        "main : Unit -> Int\nmain () = {\nlet rec wrong : Unit -> Int = fn(ignored) {\ntrue\n}\nwrong ()\n}\n",
    );
    assert_eq!(result_error.reason, TypeReason::BindingInitializer);
    assert_eq!(result_error.expected.as_deref(), Some("Int"));
    assert_eq!(result_error.found.as_deref(), Some("Bool"));

    let argument_error = typing_error(
        "main : Unit -> Int\nmain () = {\nlet rec first : Unit -> Int = fn(ignored) {\nsecond 1\n}\nand second : Unit -> Int = fn(ignored) {\n42\n}\nfirst ()\n}\n",
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

            let mut text = String::from("main : Unit -> Int\nmain () = {\n");
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

            let evaluation = evaluate_module(&text);

            assert_eq!(evaluation.value.to_string(), MEMBERS.to_string());
            assert!(evaluation.trace.len() > MEMBERS * 5);
        })
        .expect("depth-test thread should start");

    worker
        .join()
        .expect("recursive pipeline and destruction should stay within the host stack budget");
}
