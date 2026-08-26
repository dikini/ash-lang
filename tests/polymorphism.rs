use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

mod support;

use ash::{
    core::{
        PureComputation, PureExprKind, ValidatedProgram,
        transform::{fold_literal_primitives, identity_traversal},
        validate_modules,
    },
    driver::PipelineFailure,
    elaborate::{Elaborator, check_module, link_modules},
    eval::evaluate,
    evidence_validation::validate_interface_evidence,
    module::{ModuleId, ModuleRoots, load_module_graph},
    resolve::resolve_module,
    source::SourceFile,
};
use support::run_module;

static CORE_TEMP_IDS: AtomicU64 = AtomicU64::new(0);

fn run(text: &str) -> ash::driver::Observation {
    run_module("polymorphism.ash", text).expect("fixture should run")
}

#[test]
fn observation_parts_have_a_public_iterative_type_disposal_path() {
    let observation = run("main : Unit -> Int\nmain () = 42\n");
    let parts = observation.into_parts();

    assert_eq!(parts.value_display(), "42");
    assert_eq!(parts.type_display(), "Int");
    let (value, ty) = parts.into_pair();
    assert_eq!(value.to_string(), "42");
    assert_eq!(ty.to_string(), "Int");
    ash::types::discard_type_iteratively(ty);
}

fn reason(text: &str) -> String {
    let failure: PipelineFailure =
        run_module("polymorphism-rejection.ash", text).expect_err("fixture should be rejected");
    failure.reason_code()
}

fn elaborated(text: &str) -> (ValidatedProgram, SourceFile, ModuleId) {
    let directory = loop {
        let id = CORE_TEMP_IDS.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("ash-polymorphic-core-{}-{id}", std::process::id()));
        match fs::create_dir(&path) {
            Ok(()) => break path,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("Core fixture directory should be creatable: {error}"),
        }
    };
    let entry_path: PathBuf = directory.join("polymorphic-core.ash");
    fs::write(&entry_path, text).expect("Core fixture should be writable");
    let graph = load_module_graph(&entry_path, &ModuleRoots::empty())
        .expect("Core fixture graph should load");
    let resolved = resolve_module(&graph.modules()[0], &[]).expect("source should resolve");
    let checked = check_module(resolved).expect("source should check");
    let linked = link_modules(vec![checked], graph.entry()).expect("source should link");
    let linked = validate_interface_evidence(linked).expect("linked evidence should validate");
    let mut elaborator =
        Elaborator::for_module_program(&linked).expect("Core namespace should fit");
    let typed = elaborator
        .synthesize_module_program(&linked)
        .expect("source should elaborate");
    let unchecked = elaborator.finish(typed.node).expect("Core should finish");
    let source = graph.modules()[0].source().clone();
    let module = graph.entry();
    let validated = validate_modules(unchecked, &[&source], &[(module, source.id())])
        .expect("Core should validate");
    let _ = fs::remove_dir_all(directory);
    (validated, source, module)
}

#[test]
fn source_instantiation_is_explicit_in_validated_core() {
    let (program, _, _) =
        elaborated("id : A -> A\nid value = value\n\nmain : Unit -> Int\nmain () = id(42)\n");
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
    let (before, source, module) =
        elaborated("id : A -> A\nid value = value\n\nmain : Unit -> Int\nmain () = id(40 + 2)\n");
    for transformed in [
        identity_traversal(&before).expect("identity traversal"),
        fold_literal_primitives(&before).expect("literal folding"),
    ] {
        let transformed = validate_modules(transformed, &[&source], &[(module, source.id())])
            .expect("transformed Core validates");
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
fn core_transforms_preserve_the_canonical_result_application_tree() {
    let (before, source, module) = elaborated(concat!(
        "type Wrapped<A> =\nWrapped(A)\n\n",
        "main : Unit -> Wrapped<Int>\n",
        "main () = Wrapped(40 + 2)\n",
    ));
    let before_type = before
        .node(before.root())
        .expect("the validated root should exist")
        .ty
        .clone();
    assert!(matches!(before_type, ash::types::Type::Application(_, _)));

    for transformed in [
        identity_traversal(&before).expect("identity traversal"),
        fold_literal_primitives(&before).expect("literal folding"),
    ] {
        let transformed = validate_modules(transformed, &[&source], &[(module, source.id())])
            .expect("transformed Core validates");
        assert!(ash::types::same_type(
            &transformed
                .node(transformed.root())
                .expect("the transformed root should exist")
                .ty,
            &before_type,
        ));
        assert_eq!(
            evaluate(&transformed)
                .expect("transformed Core evaluates")
                .value
                .to_string(),
            "Wrapped(42)",
        );
    }
}

#[test]
fn implicitly_quantified_global_instantiates_at_unrelated_types() {
    let observation = run(
        "id : A -> A\nid value = value\n\nmain : Unit -> (Int, Bool)\nmain () = (id(42), id(true))\n",
    );

    assert_eq!(observation.value_display(), "(42, true)");
    assert_eq!(observation.type_display(), "(Int, Bool)");
}

#[test]
fn polymorphic_global_instantiates_freshly_inside_another_global() {
    let observation = run(
        "id : A -> A\nid value = value\n\nrelay : B -> B\nrelay value = id value\n\nmain : Unit -> Bool\nmain () = relay(true)\n",
    );

    assert_eq!(observation.value_display(), "true");
    assert_eq!(observation.type_display(), "Bool");
}

#[test]
fn parameterized_constructors_are_ordinary_polymorphic_values() {
    let observation = run(
        "type Option<A> =\nNone\n| Some(A)\n\napply : (A -> B, A) -> B\napply (function, value) = function value\n\nmain : Unit -> Option<Int>\nmain () = apply(Some, 42)\n",
    );

    assert_eq!(observation.value_display(), "Some(42)");
    assert_eq!(observation.type_display(), "Option<Int>");
}

#[test]
fn wide_nominal_application_remains_width_through_elaboration_and_core() {
    const WIDTH: usize = 256;

    std::thread::Builder::new()
        .name("wide-canonical-application-pipeline".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let parameters = (0..WIDTH)
                .map(|index| format!("A{index}"))
                .collect::<Vec<_>>()
                .join(", ");
            let arguments = std::iter::repeat_n("Int", WIDTH)
                .collect::<Vec<_>>()
                .join(", ");
            let source = format!(
                "type Wide<{parameters}> =\nWide\n\nmain : Unit -> Wide<{arguments}>\nmain () = Wide\n"
            );

            let observation = run(&source);
            let mut current = observation.ty();
            let mut application_cells = 0;
            while let ash::types::Type::Application(function, argument) = current {
                assert_eq!(argument.as_ref(), &ash::types::Type::Int);
                application_cells += 1;
                current = function;
            }
            assert_eq!(application_cells, WIDTH);
            assert!(matches!(current, ash::types::Type::Nominal(_)));
            assert_eq!(observation.value_display(), "Wide");
            drop(observation);
        })
        .expect("the wide pipeline thread should start")
        .join()
        .expect("the wide source, Core program, and observation should dispose on a small stack");
}

#[test]
fn solved_result_inference_is_zonked_before_public_observation() {
    let observation = run(
        "type Option<A> =\nNone\n| Some(A)\n\nmain : Unit -> Option<Int>\nmain () = {\nlet value = None\nlet _ : Option<Int> = value\nvalue\n}\n",
    );

    assert_eq!(observation.value_display(), "None");
    assert_eq!(observation.type_display(), "Option<Int>");
}

#[test]
fn anonymous_function_local_bindings_generalize() {
    let observation = run(
        "main : Unit -> (Int, Bool)\nmain () = {\nlet id = fn(value) {\nvalue\n}\n(id(42), id(false))\n}\n",
    );

    assert_eq!(observation.value_display(), "(42, false)");
    assert_eq!(observation.type_display(), "(Int, Bool)");
}

#[test]
fn primitive_operands_refine_inferred_function_parameters() {
    let observation = run(
        "main : Unit -> Int\nmain () = {\nlet increment = fn(value) {\nvalue + 1\n}\nincrement(41)\n}\n",
    );

    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn nested_anonymous_functions_refine_inferred_codomains() {
    let observation = run(
        "main : Unit -> Int\nmain () = {\nlet first = fn(left) {\nfn(right) {\nleft\n}\n}\nfirst(42)(false)\n}\n",
    );

    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn parameter_refinement_updates_a_shared_inferred_codomain() {
    let observation = run(
        "apply : (A -> A) -> A -> A\napply function = fn(value) {\nfunction value\n}\n\nmain : Unit -> Unit\nmain () = apply(fn(()) {\n()\n})(())\n",
    );

    assert_eq!(observation.value_display(), "()");
    assert_eq!(observation.type_display(), "Unit");
}

#[test]
fn unit_and_tuple_patterns_refine_inferred_function_domains() {
    let observation = run(
        "main : Unit -> (Int, Int)\nmain () = {\nlet from_unit = fn(()) {\n42\n}\nlet tuple_first = fn((left, right)) {\nleft\n}\n(from_unit(()), tuple_first((7, false)))\n}\n",
    );

    assert_eq!(observation.value_display(), "(42, 7)");
    assert_eq!(observation.type_display(), "(Int, Int)");
}

#[test]
fn singleton_constructor_patterns_refine_inferred_function_domains() {
    let observation = run(
        "type Identity<A> =\nIdentity(A)\n\nmain : Unit -> Int\nmain () = {\nlet unwrap = fn(Identity(value)) {\nvalue\n}\nunwrap(Identity(42))\n}\n",
    );

    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn boolean_patterns_refine_before_function_coverage_rejection() {
    assert_eq!(
        reason("main : Unit -> Unit\nmain () = {\nlet only_true = fn(true) {\n1\n}\n()\n}\n"),
        "pattern.refutable-function-domain"
    );
}

#[test]
fn match_patterns_refine_inferred_scrutinee_types_before_coverage() {
    let observation = run(
        "main : Unit -> Bool\nmain () = {\nlet negate = fn(value) {\nmatch value {\ntrue => false\nfalse => true\n}\n}\nnegate(true)\n}\n",
    );

    assert_eq!(observation.value_display(), "false");
    assert_eq!(observation.type_display(), "Bool");
}

#[test]
fn local_patterns_refine_inferred_binding_types_before_coverage() {
    let observation = run(
        "main : Unit -> Int\nmain () = {\nlet consume = fn(value) {\nlet () = value\n42\n}\nconsume(())\n}\n",
    );

    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn constructor_patterns_instantiate_the_expected_nominal_arguments() {
    let observation = run(
        "type Option<A> =\nNone\n| Some(A)\n\nunwrap_or : (A, Option<A>) -> A\nunwrap_or (fallback, None) = fallback\nunwrap_or (_, Some(value)) = value\n\nmain : Unit -> Int\nmain () = unwrap_or(0, Some(42))\n",
    );

    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn coverage_substitutes_parameterized_constructor_payloads() {
    let observation = run(
        "type Option<A> =\nNone\n| Some(A)\n\nclassify : Option<Bool> -> Int\nclassify None = 0\nclassify (Some true) = 1\nclassify (Some false) = 2\n\nmain : Unit -> Int\nmain () = classify(Some(false))\n",
    );
    assert_eq!(observation.value_display(), "2");
}

#[test]
fn parameterized_guarded_recursive_data_keeps_runtime_types_erased() {
    let observation = run(
        "type Stream<A> =\nCons(A, Stream<A>)\n\nmain : Unit -> Stream<Int>\nmain () = {\nlet rec ones : Stream<Int> = Cons(1, ones)\nones\n}\n",
    );

    assert_eq!(observation.value_display(), "Cons(1, <cycle>)");
    assert_eq!(observation.type_display(), "Stream<Int>");
}

#[test]
fn duplicate_type_parameters_are_rejected_at_resolution() {
    assert_eq!(
        reason(
            "type Pair<A, A> =\nPair(A, A)\n\nmain : Unit -> Pair<Int, Int>\nmain () = Pair(1, 2)\n"
        ),
        "resolve.duplicate-type-parameter"
    );
}

#[test]
fn unknown_type_variables_are_rejected_at_resolution() {
    assert_eq!(
        reason(
            "type Wrapped<A> =\nWrapped(B)\n\nmain : Unit -> Wrapped<Int>\nmain () = Wrapped(1)\n"
        ),
        "resolve.unknown-type"
    );
}

#[test]
fn nominal_constructors_at_value_boundaries_must_end_at_type() {
    assert_eq!(
        reason(
            "type Option<A> =\nNone\n| Some(A)\n\nbad : Option -> Int\nbad _ = 0\n\nmain : Unit -> Int\nmain () = bad None\n"
        ),
        "kind.expected-type"
    );
}

#[test]
fn type_parameters_of_kind_type_are_not_applicable() {
    assert_eq!(
        reason("type Bad<A> =\nBad(A<Int>)\n\nmain : Unit -> Bad<Int>\nmain () = Bad(1)\n"),
        "kind.not-applicable"
    );
}

#[test]
fn application_shaped_local_bindings_remain_monomorphic() {
    assert_eq!(
        reason(
            "make : Unit -> (A -> A)\nmake _ = fn(value) {\nvalue\n}\n\nmain : Unit -> (Int, Bool)\nmain () = {\nlet id = make(())\n(id(42), id(false))\n}\n"
        ),
        "type.argument"
    );
}

#[test]
fn function_generalization_excludes_inference_shared_with_the_environment() {
    assert_eq!(
        reason(
            "make : Unit -> (A -> A)\nmake _ = fn(value) {\nvalue\n}\n\nmain : Unit -> (Int, Bool)\nmain () = {\nlet shared = make(())\nlet get = fn(ignored) {\nshared\n}\n(get(())(42), get(())(false))\n}\n"
        ),
        "type.argument"
    );
}

#[test]
fn inferred_polymorphic_recursion_is_rejected() {
    assert_eq!(
        reason(
            "loop : A -> Unit\nloop value = loop((value, value))\n\nmain : Unit -> Unit\nmain () = loop(1)\n"
        ),
        "type.polymorphic-recursion"
    );
}

#[test]
fn recursive_global_self_uses_apply_the_same_rigid_parameters() {
    let observation =
        run("repeat : A -> A\nrepeat value = repeat value\n\nmain : Unit -> Int\nmain () = 0\n");
    assert_eq!(observation.value_display(), "0");
}

#[test]
fn infinite_inferred_types_are_rejected_by_the_occurs_check() {
    assert_eq!(
        reason(
            "main : Unit -> Unit\nmain () = {\nlet omega = fn(value) {\nvalue(value)\n}\n()\n}\n"
        ),
        "type.infinite"
    );
}

#[test]
fn unresolved_local_function_inference_is_a_source_ambiguity() {
    assert_eq!(
        reason(
            "main : Unit -> Unit\nmain () = {\nlet constant = fn(ignored) {\n42\n}\nlet _ = constant\n()\n}\n"
        ),
        "type.ambiguous"
    );
}

#[test]
fn discarded_anonymous_function_inference_is_a_source_ambiguity() {
    assert_eq!(
        reason("main : Unit -> Unit\nmain () = {\nlet _ = fn(value) {\nvalue\n}\n()\n}\n"),
        "type.ambiguous"
    );
}

#[test]
fn unused_parameterized_constructor_inference_is_a_source_ambiguity() {
    assert_eq!(
        reason(
            "type Option<A> =\nNone\n| Some(A)\n\nmain : Unit -> Unit\nmain () = {\nlet unused = None\n()\n}\n"
        ),
        "type.ambiguous"
    );
}

#[test]
fn deep_parameter_substitution_completes_on_a_small_stack() {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn_scoped(scope, || {
                let mut argument = "Unit".to_owned();
                for _ in 0..(ash::parser::STRUCTURAL_DEPTH_LIMIT - 4) {
                    argument = format!("Unit -> {argument}");
                }
                let text = format!(
                    "type Holder<A> =\nHold(Unit -> A)\n\nread : Holder<{argument}> -> Int\nread (Hold function) = 0\n\nmain : Unit -> Int\nmain () = 0\n"
                );
                assert_eq!(run(&text).value_display(), "0");
            })
            .expect("small-stack thread should start")
            .join()
            .expect("substitution must not consume the host stack");
    });
}
