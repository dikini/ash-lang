use ash::{
    core::{
        PureComputation, PureExprKind,
        transform::{fold_literal_primitives, identity_traversal},
        validate,
    },
    driver::run_source,
    elaborate::Elaborator,
    eval::evaluate,
    lexer::lex,
    parser::{parse, project},
    resolve::resolve,
    source::SourceFile,
};

fn run(text: &str) -> ash::driver::Observation {
    run_source(SourceFile::new("polymorphism.ash", text).expect("fixture should fit"))
        .expect("fixture should run")
}

fn reason(text: &str) -> String {
    run_source(SourceFile::new("polymorphism-rejection.ash", text).expect("fixture should fit"))
        .expect_err("fixture should be rejected")
        .reason_code()
}

fn elaborated(text: &str) -> ash::core::ValidatedProgram {
    let source = SourceFile::new("polymorphic-core.ash", text).expect("fixture should fit");
    let tree = parse(lex(&source).expect("source should lex"));
    let surface = project(&source, &tree).expect("source should project");
    let resolved = resolve(&surface).expect("source should resolve");
    let mut elaborator = Elaborator::for_program(&resolved).expect("Core namespace should fit");
    let typed = elaborator
        .synthesize_program(&resolved)
        .expect("source should elaborate");
    validate(
        elaborator.finish(typed.node).expect("Core should finish"),
        &[&source],
    )
    .expect("Core should validate")
}

#[test]
fn source_instantiation_is_explicit_in_validated_core() {
    let program = elaborated("id : A -> A\nid value = value\n\nid(42)\n");
    let mut work = vec![program.root()];
    let mut abstractions = 0;
    let mut applications = 0;
    while let Some(id) = work.pop() {
        let node = program.node(id).expect("validated node");
        match &node.kind {
            PureExprKind::Computation(PureComputation::TypeAbstraction(operation)) => {
                abstractions += 1;
                work.push(operation.body());
            }
            PureExprKind::Computation(PureComputation::TypeApplication(operation)) => {
                applications += 1;
                work.push(operation.function());
            }
            kind => {
                for index in 0..kind.child_count() {
                    work.push(kind.child_at(index).expect("validated child"));
                }
            }
        }
    }
    assert!(abstractions >= 1);
    assert!(applications >= 1);
}

#[test]
fn explicit_type_operations_survive_both_core_transforms_and_erasure() {
    let source = SourceFile::new(
        "polymorphic-transform.ash",
        "id : A -> A\nid value = value\n\nid(40 + 2)\n",
    )
    .expect("fixture should fit");
    let before = {
        let tree = parse(lex(&source).expect("source should lex"));
        let surface = project(&source, &tree).expect("source should project");
        let resolved = resolve(&surface).expect("source should resolve");
        let mut elaborator = Elaborator::for_program(&resolved).expect("Core namespace should fit");
        let typed = elaborator
            .synthesize_program(&resolved)
            .expect("source should elaborate");
        validate(
            elaborator.finish(typed.node).expect("Core should finish"),
            &[&source],
        )
        .expect("Core should validate")
    };
    for transformed in [
        identity_traversal(&before).expect("identity traversal"),
        fold_literal_primitives(&before).expect("literal folding"),
    ] {
        let transformed = validate(transformed, &[&source]).expect("transformed Core validates");
        assert_eq!(
            evaluate(&transformed)
                .expect("transformed Core evaluates")
                .value
                .to_string(),
            "42"
        );
    }
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
    let observation = run("{\nlet id = fn(value) {\nvalue\n}\n(id(42), id(false))\n}\n");

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
fn coverage_substitutes_parameterized_constructor_payloads() {
    let observation = run(
        "type Option<A> =\nNone\n| Some(A)\n\nclassify : Option<Bool> -> Int\nclassify None = 0\nclassify (Some true) = 1\nclassify (Some false) = 2\n\nclassify(Some(false))\n",
    );
    assert_eq!(observation.value_display(), "2");
}

#[test]
fn parameterized_guarded_recursive_data_keeps_runtime_types_erased() {
    let observation = run(
        "type Stream<A> =\nCons(A, Stream<A>)\n\n{\nlet rec ones : Stream<Int> = Cons(1, ones)\nones\n}\n",
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
            "make : Unit -> (A -> A)\nmake _ = fn(value) {\nvalue\n}\n\n{\nlet id = make(())\n(id(42), id(false))\n}\n"
        ),
        "type.argument"
    );
}

#[test]
fn inferred_polymorphic_recursion_is_rejected() {
    assert_eq!(
        reason("loop : A -> Unit\nloop value = loop((value, value))\n\nloop(1)\n"),
        "type.polymorphic-recursion"
    );
}

#[test]
fn infinite_inferred_types_are_rejected_by_the_occurs_check() {
    assert_eq!(
        reason("{\nlet omega = fn(value) {\nvalue(value)\n}\nomega\n}\n"),
        "type.infinite"
    );
}

#[test]
fn unresolved_local_function_inference_is_a_source_ambiguity() {
    assert_eq!(
        reason("{\nlet constant = fn(ignored) {\n42\n}\nconstant\n}\n"),
        "type.ambiguous"
    );
}
