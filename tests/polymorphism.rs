use ash::{driver::run_source, source::SourceFile};

fn run(text: &str) -> ash::driver::Observation {
    run_source(SourceFile::new("polymorphism.ash", text).expect("fixture should fit"))
        .expect("fixture should run")
}

fn reason(text: &str) -> String {
    run_source(SourceFile::new("polymorphism-rejection.ash", text).expect("fixture should fit"))
        .expect_err("fixture should be rejected")
        .reason_code()
}

#[test]
fn implicitly_quantified_global_instantiates_at_unrelated_types() {
    let observation = run("id : A -> A\nid value = value\n\n(id(42), id(true))\n");

    assert_eq!(observation.value_display(), "(42, true)");
    assert_eq!(observation.type_display(), "(Int, Bool)");
}

#[test]
fn parameterized_constructors_are_ordinary_polymorphic_values() {
    let observation = run(
        "type Option<A> =\nNone\n| Some(A)\n\napply : (A -> B, A) -> B\napply (function, value) = function value\n\napply(Some, 42)\n",
    );

    assert_eq!(observation.value_display(), "Some(42)");
    assert_eq!(observation.type_display(), "Option<Int>");
}

#[test]
fn anonymous_function_local_bindings_generalize() {
    let observation = run("{\nlet id = fn(value) { value }\n(id(42), id(false))\n}\n");

    assert_eq!(observation.value_display(), "(42, false)");
    assert_eq!(observation.type_display(), "(Int, Bool)");
}

#[test]
fn constructor_patterns_instantiate_the_expected_nominal_arguments() {
    let observation = run(
        "type Option<A> =\nNone\n| Some(A)\n\nunwrap_or : (A, Option<A>) -> A\nunwrap_or (fallback, None) = fallback\nunwrap_or (_, Some(value)) = value\n\nunwrap_or(0, Some(42))\n",
    );

    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn parameterized_guarded_recursive_data_keeps_runtime_types_erased() {
    let observation = run(
        "type Stream<A> =\nCons(A, Stream<A>)\n\n{\nlet rec\nones : Stream<Int> = Cons(1, ones)\nin\nones\n}\n",
    );

    assert_eq!(observation.value_display(), "Cons(1, <cycle>)");
    assert_eq!(observation.type_display(), "Stream<Int>");
}

#[test]
fn duplicate_type_parameters_are_rejected_at_resolution() {
    assert_eq!(
        reason("type Pair<A, A> =\nPair(A, A)\n\nPair(1, 2)\n"),
        "resolve.duplicate-type-parameter"
    );
}

#[test]
fn unknown_type_variables_are_rejected_at_resolution() {
    assert_eq!(
        reason("type Wrapped<A> =\nWrapped(B)\n\nWrapped(1)\n"),
        "resolve.unknown-type"
    );
}

#[test]
fn nominal_type_applications_must_be_saturated() {
    assert_eq!(
        reason("type Option<A> =\nNone\n| Some(A)\n\nbad : Option -> Int\nbad _ = 0\n\nbad None\n"),
        "resolve.type-argument-count"
    );
}

#[test]
fn type_parameters_of_kind_type_cannot_be_applied() {
    assert_eq!(
        reason("type Bad<A> =\nBad(A<Int>)\n\nBad(1)\n"),
        "resolve.type-kind"
    );
}

#[test]
fn application_shaped_local_bindings_remain_monomorphic() {
    assert_eq!(
        reason(
            "make : Unit -> (A -> A)\nmake _ = fn(value) { value }\n\n{\nlet id = make(())\n(id(42), id(false))\n}\n"
        ),
        "type.mismatch"
    );
}

#[test]
fn inferred_polymorphic_recursion_is_rejected() {
    assert_eq!(
        reason(
            "{\nlet rec\nloop : A -> Unit = fn(value) { loop((value, value)) }\nin\nloop(1)\n}\n"
        ),
        "type.polymorphic-recursion"
    );
}

#[test]
fn infinite_inferred_types_are_rejected_by_the_occurs_check() {
    assert_eq!(
        reason("{\nlet omega = fn(value) { value(value) }\nomega\n}\n"),
        "type.infinite"
    );
}
