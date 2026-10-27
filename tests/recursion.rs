mod support;

use ash::{
    driver::PipelineFailure,
    elaborate::{TypeError, TypeReason},
    types::Type,
};
use support::run_module;

fn run(text: &str) -> ash::driver::Observation {
    run_module("recursion.ash", text).expect("fixture should run")
}

fn typing_error(text: &str) -> Box<ash::elaborate::TypeDiagnostic> {
    let error = run_module("recursion.ash", text).expect_err("fixture should fail typing");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = error else {
        panic!("expected a source typing error, found {error:?}")
    };
    diagnostic
}

#[test]
fn global_presentations_share_recursive_scope_and_evaluate() {
    let observation = run(
        "first : Unit -> Int\nfirst ignored = second ()\n\nfn second(ignored : Unit) -> Int {\nlet retain : Unit -> Int = fn(value) {\nfirst value\n}\n42\n}\n\nmain : Unit -> Int\nmain () = first ()\n",
    );

    assert_eq!(observation.value().to_string(), "42");
    assert_eq!(observation.ty(), &Type::Int);
}

#[test]
fn inline_function_open_row_uses_the_same_default_as_arrow_annotations() {
    let observation = run(
        "fn invoke<E : EffectRow>(action : Unit -> Unit ! {| E}) -> Unit ! {| E} {\naction ()\n}\naction : Unit -> Unit\naction () = ()\nmain : Unit -> Unit\nmain () = invoke action\n",
    );
    assert_eq!(observation.value().to_string(), "()");
}

#[test]
fn implementation_method_recurses_through_current_evidence() {
    let observation = run(
        "type Counter =\nStop\n| More(Counter)\n\ninterface Countdown<A> {\ncountdown : A -> Int\n}\n\nimpl Countdown<Counter> {\ncountdown Stop = 42\ncountdown (More(rest)) = countdown rest\n}\n\nmain : Unit -> Int\nmain () = countdown(More(More(Stop)))\n",
    );

    assert_eq!(observation.value().to_string(), "42");
    assert_eq!(observation.ty(), &Type::Int);
}

#[test]
fn implementation_methods_share_mutual_recursive_scope() {
    let observation = run(
        "type Counter =\nStop\n| More(Counter)\n\ninterface Countdown<A> {\nfirst : A -> Int\nsecond : (A, Unit) -> Int\n}\n\nimpl Countdown<Counter> {\nfirst Stop = 42\nfirst (More(rest)) = second(rest, ())\nsecond (value, ()) = first value\n}\n\nmain : Unit -> Int\nmain () = first(More(More(Stop)))\n",
    );

    assert_eq!(observation.value().to_string(), "42");
    assert_eq!(observation.ty(), &Type::Int);
}

#[test]
fn earlier_global_and_later_implementation_method_share_recursive_scope() {
    let observation = run(
        "type Counter =\nStop\n| More(Counter)\n\ninterface Countdown<A> {\ncountdown : A -> Int\n}\n\nadvance : Counter -> Int\nadvance Stop = 42\nadvance (More(rest)) = countdown rest\n\nimpl Countdown<Counter> {\ncountdown value = advance value\n}\n\nmain : Unit -> Int\nmain () = advance(More(More(Stop)))\n",
    );

    assert_eq!(observation.value().to_string(), "42");
    assert_eq!(observation.ty(), &Type::Int);
}

#[test]
fn earlier_implementation_method_and_later_global_share_recursive_scope() {
    let observation = run(
        "type Counter =\nStop\n| More(Counter)\n\ninterface Countdown<A> {\ncountdown : A -> Int\n}\n\nimpl Countdown<Counter> {\ncountdown Stop = 42\ncountdown (More(rest)) = advance rest\n}\n\nadvance : Counter -> Int\nadvance value = countdown value\n\nmain : Unit -> Int\nmain () = countdown(More(More(Stop)))\n",
    );

    assert_eq!(observation.value().to_string(), "42");
    assert_eq!(observation.ty(), &Type::Int);
}

#[test]
fn local_recursive_group_evaluates_through_the_same_core_form() {
    let observation = run(
        "main : Unit -> Int\nmain () = {\nlet rec first : Unit -> Int = fn(ignored) {\nsecond ()\n}\nand second : Unit -> Int = fn(ignored) {\nlet retain : Unit -> Int = fn(value) {\nfirst value\n}\n42\n}\nfirst ()\n}\n",
    );

    assert_eq!(observation.value().to_string(), "42");
    assert_eq!(observation.ty(), &Type::Int);
}

#[test]
fn recursive_closure_uses_its_definition_environment_not_its_caller() {
    let observation = run(
        "main : Unit -> Int\nmain () = {\nlet captured = 42\nlet rec read : Unit -> Int = fn(ignored) {\ncaptured\n}\nlet caller : Unit -> Int = fn(ignored) {\nlet captured = 0\nread ()\n}\ncaller ()\n}\n",
    );

    assert_eq!(observation.value().to_string(), "42");
    assert_eq!(observation.ty(), &Type::Int);
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
