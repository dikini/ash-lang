mod support;

use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{CoreBuilder, PureComputation, PureExprKind, validate, validate_modules},
    driver::PipelineFailure,
    elaborate::{ElaborationFailure, Elaborator, TypeContext, TypeError, TypeReason},
    eval::{TraceEvent, Value, evaluate},
    integer::Integer,
    module::{ModuleRoots, load_module_graph},
    resolve::resolve_module,
    resolved::{
        Binder, ResolvedBinding, ResolvedBlock, ResolvedDefinitionKind, ResolvedExpr,
        ResolvedExprKind, ResolvedLocalDeclaration, ResolvedModule, ResolvedModuleProgram,
        ResolvedPatternKind,
    },
    source::{ByteRange, GeneratedReason, Origin, SourceFile},
    types::Type,
};
use support::run_module;

const V003: &str =
    "main : Unit -> Int\nmain () = {\n    let value = 1\n    let value = value + 1\n    value\n}\n";
static MODULE_TEMP_IDS: AtomicU64 = AtomicU64::new(0);

fn binding(block: &ResolvedBlock, index: usize) -> &ResolvedBinding {
    let ResolvedLocalDeclaration::Binding(binding) = &block.declarations[index] else {
        panic!("expected ordinary binding")
    };
    binding
}

fn binding_binder(binding: &ResolvedBinding) -> &Binder {
    let ResolvedPatternKind::Binder(binder) = &binding.pattern.kind else {
        panic!("expected binder pattern")
    };
    binder
}

fn binding_mut(block: &mut ResolvedBlock, index: usize) -> &mut ResolvedBinding {
    let ResolvedLocalDeclaration::Binding(binding) = &mut block.declarations[index] else {
        panic!("expected ordinary binding")
    };
    binding
}

fn resolved(name: &str, text: &str) -> (SourceFile, ResolvedModule) {
    let directory = loop {
        let id = MODULE_TEMP_IDS.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("ash-binding-module-{}-{id}", std::process::id()));
        match fs::create_dir(&path) {
            Ok(()) => break path,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("binding fixture directory should be creatable: {error}"),
        }
    };
    let path: PathBuf = directory.join(name);
    fs::write(&path, text).expect("binding fixture should be writable");
    let graph =
        load_module_graph(&path, &ModuleRoots::empty()).expect("binding module should load");
    let source = graph.modules()[0].source().clone();
    let resolved = resolve_module(&graph.modules()[0], &[]).expect("binding module should resolve");
    let _ = fs::remove_dir_all(directory);
    (source, resolved)
}

fn main_body(module: &ResolvedModule) -> &ResolvedExpr {
    let definition = module
        .definitions()
        .iter()
        .find(|definition| match &definition.kind {
            ResolvedDefinitionKind::Equational(global) => global.interface.name.spelling == "main",
            ResolvedDefinitionKind::InlineOperational(global) => {
                global.header.name.spelling == "main"
            }
        })
        .expect("fixture should declare main");
    let ResolvedDefinitionKind::Equational(main) = &definition.kind else {
        panic!("binding fixture main should be equational");
    };
    &main.equations[0].body
}

fn expression_elaborator(module: &ResolvedModule, expression: &ResolvedExpr) -> Elaborator {
    let probe = ResolvedModuleProgram {
        registry: std::sync::Arc::clone(module.registry()),
        groups: Vec::new().into_boxed_slice(),
        entry: module.module(),
        result: expression.clone(),
    };
    Elaborator::for_module_program(&probe).expect("binder reservation should fit")
}

fn elaborate(
    source: &SourceFile,
    module: &ResolvedModule,
    expression: &ResolvedExpr,
) -> (ash::core::ValidatedProgram, Type) {
    let mut elaborator = expression_elaborator(module, expression);
    let typed = elaborator
        .synthesize(expression, &TypeContext::new())
        .expect("binding program should synthesize");
    let ty = typed.ty;
    let unchecked = elaborator.finish(typed.node).expect("root should finish");
    let validated = validate_modules(unchecked, &[source], &[(module.module(), source.id())])
        .expect("binding Core should validate");
    (validated, ty)
}

#[test]
fn v003_resolves_shadowing_to_distinct_binders_and_runs_to_two() {
    let (_source, module) = resolved("v003-local-shadowing.ash", V003);
    let ResolvedExprKind::Block(block) = &main_body(&module).kind else {
        panic!("expected the V-003 block");
    };
    let first = binding_binder(binding(block, 0)).id;
    let second = binding_binder(binding(block, 1)).id;
    let ResolvedExprKind::Add(initializer) = &binding(block, 1).initializer.kind else {
        panic!("expected the shadowing initializer");
    };
    let ResolvedExprKind::Occurrence(initializer_use) = &initializer.left.kind else {
        panic!("expected the initializer occurrence");
    };
    let ResolvedExprKind::Occurrence(result_use) = &block.result.kind else {
        panic!("expected the result occurrence");
    };

    assert_ne!(first, second);
    assert_eq!(initializer_use.binder, first);
    assert_eq!(result_use.binder, second);

    let observation =
        run_module("v003-local-shadowing.ash", V003).expect("V-003 should run end to end");
    let Value::Integer(value) = observation.value else {
        panic!("expected an integer value");
    };
    assert_eq!(value, Integer::parse_decimal("2").expect("valid integer"));
    assert_eq!(observation.ty, Type::Int);
}

#[test]
fn annotated_primitive_binding_checks_then_enters_the_remainder_scope() {
    let source = SourceFile::new(
        "annotated.ash",
        "main : Unit -> Int\nmain () = {\n    let answer : Int = 20 + 1\n    answer * 2\n}\n",
    )
    .expect("test source should fit");

    let observation =
        run_module("annotated.ash", source.text()).expect("annotated binding should run");
    let Value::Integer(value) = observation.value else {
        panic!("expected an integer value");
    };
    assert_eq!(value, Integer::parse_decimal("42").expect("valid integer"));
    assert_eq!(observation.ty, Type::Int);
}

#[test]
fn annotated_initializer_mismatch_is_a_source_type_rejection() {
    let source = SourceFile::new(
        "mismatch.ash",
        "main : Unit -> Bool\nmain () = {\n    let value : Bool = 1\n    value\n}\n",
    )
    .expect("test source should fit");

    let error =
        run_module("mismatch.ash", source.text()).expect_err("the initializer should not check");
    let PipelineFailure::Typing(TypeError::Source(diagnostic)) = &error else {
        panic!("expected a categorized binding-initializer diagnostic");
    };
    assert_eq!(diagnostic.reason, TypeReason::BindingInitializer);
    assert_eq!(diagnostic.expected.as_deref(), Some("Bool"));
    assert_eq!(diagnostic.found.as_deref(), Some("Int"));
    assert!(error.is_source_rejection());
}

#[test]
fn block_elaboration_folds_bindings_right_to_left_with_causal_origins() {
    let (source, module) = resolved("origins.ash", V003);
    let expression = main_body(&module);
    let ResolvedExprKind::Block(block) = &expression.kind else {
        panic!("expected a block");
    };
    let (validated, ty) = elaborate(&source, &module, expression);
    assert_eq!(ty, Type::Int);

    let outer = validated.node(validated.root()).expect("outer binding");
    let PureExprKind::Computation(PureComputation::Bind(first_core)) = &outer.kind else {
        panic!("expected the first binding outside the second");
    };
    assert_eq!(
        first_core.binder().id(),
        binding_binder(binding(block, 0)).id
    );
    assert_eq!(first_core.binder().ty(), &Type::Int);
    assert_eq!(outer.ty, Type::Int);
    assert_eq!(
        outer.origin.generated_reason(),
        Some(GeneratedReason::BindingLowering)
    );
    assert_eq!(outer.origin.primary_span(), binding(block, 0).span);
    assert_eq!(
        outer.origin.related_spans(),
        &[binding(block, 0).initializer.span]
    );
    assert_eq!(
        first_core.binder().origin().generated_reason(),
        Some(GeneratedReason::BindingLowering)
    );
    assert_eq!(
        first_core.binder().origin().primary_span(),
        binding_binder(binding(block, 0)).origin.primary_span()
    );

    let inner = validated.node(first_core.body()).expect("inner binding");
    let PureExprKind::Computation(PureComputation::Bind(second_core)) = &inner.kind else {
        panic!("expected the second binding inside the first");
    };
    assert_eq!(
        second_core.binder().id(),
        binding_binder(binding(block, 1)).id
    );
    assert_eq!(inner.origin.primary_span(), binding(block, 1).span);
    assert_eq!(
        inner.origin.related_spans(),
        &[binding(block, 1).initializer.span]
    );
}

#[test]
fn machine_trace_enters_each_initializer_before_its_binding_body() {
    let (source, module) = resolved("trace.ash", V003);
    let (validated, _) = elaborate(&source, &module, main_body(&module));

    let outer = validated.node(validated.root()).expect("outer binding");
    let PureExprKind::Computation(PureComputation::Bind(first)) = &outer.kind else {
        panic!("expected outer binding");
    };
    let inner = validated.node(first.body()).expect("inner binding");
    let PureExprKind::Computation(PureComputation::Bind(second)) = &inner.kind else {
        panic!("expected inner binding");
    };
    let addition = validated
        .node(second.initializer())
        .expect("addition initializer");
    let PureExprKind::Computation(PureComputation::Primitive(operation)) = &addition.kind else {
        panic!("expected primitive initializer");
    };
    let expected = vec![
        validated.root(),
        first.initializer(),
        first.body(),
        second.initializer(),
        operation.left(),
        operation.right(),
        second.body(),
    ];

    let evaluation = evaluate(&validated).expect("binding machine should evaluate");
    let entered = evaluation
        .trace
        .iter()
        .map(|event| match event {
            TraceEvent::Enter(node) => *node,
        })
        .collect::<Vec<_>>();
    assert_eq!(entered, expected);
}

#[test]
fn failed_initializer_scope_check_poisons_the_elaborator() {
    let (_source, module) = resolved("invalid-scope.ash", V003);
    let mut expression = main_body(&module).clone();
    let ResolvedExprKind::Block(block) = &mut expression.kind else {
        panic!("expected a block");
    };
    let prior_expression = binding(block, 0).initializer.clone();
    let second_binder = binding_binder(binding(block, 1)).id;
    let ResolvedExprKind::Add(initializer) = &mut binding_mut(block, 1).initializer.kind else {
        panic!("expected an addition initializer");
    };
    let ResolvedExprKind::Occurrence(use_site) = &mut initializer.left.kind else {
        panic!("expected an occurrence");
    };
    use_site.binder = second_binder;

    let mut elaborator = expression_elaborator(&module, &expression);
    let prior = elaborator
        .synthesize(&prior_expression, &TypeContext::new())
        .expect("the independent primitive should synthesize");
    assert!(matches!(
        elaborator.synthesize(&expression, &TypeContext::new()),
        Err(TypeError::Internal(ElaborationFailure::InvalidState))
    ));
    assert!(matches!(
        elaborator.finish(prior.node),
        Err(ElaborationFailure::InvalidState)
    ));
}

#[test]
fn annotated_function_is_checked_from_the_binding_annotation() {
    let (source, module) = resolved(
        "pending-function.ash",
        "main : Unit -> Int\nmain () = {\n    let identity : Int -> Int = fn(value) {\n        value\n    }\n    1\n}\n",
    );
    let expression = main_body(&module);
    let mut elaborator = expression_elaborator(&module, expression);
    let typed = elaborator
        .synthesize(expression, &TypeContext::new())
        .expect("the annotated function should check");
    assert_eq!(typed.ty, Type::Int);
    let validated = validate(
        elaborator.finish(typed.node).expect("root should finish"),
        &[&source],
    )
    .expect("expected-typed function Core should validate");
    let evaluation = evaluate(&validated).expect("unused function binding should evaluate");
    assert!(matches!(evaluation.value, Value::Integer(value) if value.to_string() == "1"));
}

#[test]
fn nested_block_initializer_restores_the_outer_context_and_core_binding_stack() {
    let (source, module) = resolved(
        "nested.ash",
        "main : Unit -> Int\nmain () = {\n    let outer = 20\n    let inner = {\n        let shadow = outer + 1\n        shadow\n    }\n    outer + inner\n}\n",
    );
    let expression = main_body(&module);
    let ResolvedExprKind::Block(outer_block) = &expression.kind else {
        panic!("expected outer block");
    };
    let ResolvedExprKind::Block(inner_block) = &binding(outer_block, 1).initializer.kind else {
        panic!("expected nested initializer block");
    };
    let ResolvedExprKind::Add(inner_initializer) = &binding(inner_block, 0).initializer.kind else {
        panic!("expected inner initializer addition");
    };
    let ResolvedExprKind::Occurrence(outer_use) = &inner_initializer.left.kind else {
        panic!("expected outer use inside nested block");
    };
    assert_eq!(outer_use.binder, binding_binder(binding(outer_block, 0)).id);

    let (validated, ty) = elaborate(&source, &module, expression);
    let outer_core = validated.node(validated.root()).expect("outer binding");
    let PureExprKind::Computation(PureComputation::Bind(outer_binding)) = &outer_core.kind else {
        panic!("expected outer Core binding");
    };
    let inner_core = validated.node(outer_binding.body()).expect("inner binding");
    let PureExprKind::Computation(PureComputation::Bind(inner_binding)) = &inner_core.kind else {
        panic!("expected second outer-block binding");
    };
    let nested_core = validated
        .node(inner_binding.initializer())
        .expect("nested initializer binding");
    let PureExprKind::Computation(PureComputation::Bind(nested_binding)) = &nested_core.kind else {
        panic!("expected nested-block Core binding");
    };
    assert_eq!(
        nested_binding.binder().id(),
        binding_binder(binding(inner_block, 0)).id
    );

    let evaluation = evaluate(&validated).expect("nested bindings should evaluate");
    let Value::Integer(value) = evaluation.value else {
        panic!("expected an integer value");
    };
    assert_eq!(value, Integer::parse_decimal("41").expect("valid integer"));
    assert_eq!(ty, Type::Int);
}

#[test]
fn nested_block_binder_is_removed_before_the_enclosing_result() {
    let (_source, module) = resolved(
        "nested-scope.ash",
        "main : Unit -> Int\nmain () = {\n    let value = {\n        let hidden = 1\n        hidden\n    }\n    value\n}\n",
    );
    let mut expression = main_body(&module).clone();
    let ResolvedExprKind::Block(outer) = &mut expression.kind else {
        panic!("expected outer block");
    };
    let ResolvedExprKind::Block(inner) = &binding(outer, 0).initializer.kind else {
        panic!("expected nested block");
    };
    let hidden = binding_binder(binding(inner, 0)).id;
    let ResolvedExprKind::Occurrence(result_use) = &mut outer.result.kind else {
        panic!("expected outer result occurrence");
    };
    result_use.binder = hidden;

    let mut elaborator = expression_elaborator(&module, &expression);
    assert!(matches!(
        elaborator.synthesize(&expression, &TypeContext::new()),
        Err(TypeError::Internal(ElaborationFailure::InvalidState))
    ));
}

#[test]
fn long_flat_binding_machine_shares_extensions_and_drops_on_a_small_stack() {
    const BINDINGS: usize = 20_000;
    let worker = std::thread::Builder::new()
        .name("long-flat-bindings".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let source = SourceFile::new("long-bindings.ash", "main : Unit -> Int\nmain () = 1\n")
                .expect("source should fit");
            let origin = Origin::Source(
                source
                    .span(ByteRange::new(0, 1).expect("ordered range"))
                    .expect("span should fit"),
            );
            let one = Integer::parse_decimal("1").expect("valid integer");
            let mut builder = CoreBuilder::new();
            let mut bindings = Vec::with_capacity(BINDINGS);
            for _ in 0..BINDINGS {
                let binder = builder
                    .binder(Type::Int, origin.clone())
                    .expect("binder should fit");
                let initializer = builder
                    .integer(one.clone(), Type::Int, origin.clone())
                    .expect("initializer should fit");
                bindings.push((binder, initializer));
            }
            let last = bindings.last().expect("at least one binder").0.id();
            let mut body = builder
                .variable(last, Type::Int, origin.clone())
                .expect("body should fit");
            for (binder, initializer) in bindings.into_iter().rev() {
                body = builder
                    .binding(binder, initializer, body, Type::Int, origin.clone())
                    .expect("binding should fit");
            }
            let validated = validate(
                builder.finish(body).expect("root should finish"),
                &[&source],
            )
            .expect("long binding Core should validate");
            let evaluation = evaluate(&validated).expect("long binding Core should evaluate");
            let Value::Integer(ref value) = evaluation.value else {
                panic!("expected an integer value");
            };
            assert_eq!(value, &one);
            assert_eq!(evaluation.trace.len(), BINDINGS * 2 + 1);
            drop(evaluation);
            drop(validated);
        })
        .expect("test thread should start");

    worker.join().expect("long binding worker should finish");
}
