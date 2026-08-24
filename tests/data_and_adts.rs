use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

mod support;

use ash::{
    core::{
        NodeId, PureComputation, PureExprKind, ValidatedProgram,
        transform::{fold_literal_primitives, identity_traversal},
        validate, validate_modules,
    },
    driver::{Observation, PipelineFailure},
    elaborate::{ElaborationFailure, Elaborator, TypeError, check_module, link_modules},
    eval::{TraceEvent, evaluate},
    module::{ModuleId, ModuleRoots, load_module_graph},
    parser::{ResourceFailure, SYNTAX_WORK_LIMIT},
    render,
    resolve::resolve_module,
    resolved::{
        ResolvedApplicationExpr, ResolvedExpr, ResolvedExprKind, ResolvedOccurrence,
        ResolvedTermName,
    },
    source::SourceFile,
    types::Type,
};
use support::run_module;

static CORE_TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct StructuralProgram {
    program: ValidatedProgram,
    source: SourceFile,
    module: ModuleId,
    ty: Type,
}

fn elaborated_module(text: &str) -> StructuralProgram {
    let directory = loop {
        let id = CORE_TEMP_IDS.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "ash-data-and-adts-core-{}-{id}",
            std::process::id()
        ));
        match fs::create_dir(&path) {
            Ok(()) => break path,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("Core fixture directory should be creatable: {error}"),
        }
    };
    let entry_path: PathBuf = directory.join("data-and-adts-core.ash");
    fs::write(&entry_path, text).expect("Core fixture should be writable");
    let graph = load_module_graph(&entry_path, &ModuleRoots::empty())
        .expect("Core fixture graph should load");
    let loaded = graph
        .modules()
        .iter()
        .find(|module| module.id() == graph.entry())
        .expect("entry module should remain loaded");
    assert!(loaded.dependencies().is_empty());
    let resolved = resolve_module(loaded, &[]).expect("Core fixture should resolve");
    let checked = check_module(resolved).expect("Core fixture should check");
    let main = checked
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "main")
        .expect("Core fixture should declare main");
    let span = main.origin.primary_span();
    let result = ResolvedExpr {
        kind: ResolvedExprKind::Apply(ResolvedApplicationExpr {
            function: Box::new(ResolvedExpr {
                kind: ResolvedExprKind::Occurrence(ResolvedOccurrence {
                    term: ResolvedTermName::Global(main.binder),
                    spelling: "main".to_owned(),
                    origin: main.origin.clone(),
                    evidence: Box::new([]),
                }),
                span,
            }),
            argument: Box::new(ResolvedExpr {
                kind: ResolvedExprKind::Unit,
                span,
            }),
        }),
        span,
    };
    let linked = link_modules(vec![checked], graph.entry(), result)
        .expect("checked Core fixture should link");
    let mut elaborator =
        Elaborator::for_module_program(&linked).expect("Core namespace should fit");
    let typed = elaborator
        .synthesize_module_program(&linked)
        .expect("Core fixture should elaborate");
    let ty = typed.ty;
    let unchecked = elaborator.finish(typed.node).expect("Core should finish");
    let source = loaded.source().clone();
    let module = graph.entry();
    let program = validate_modules(unchecked, &[&source], &[(module, source.id())])
        .expect("Core fixture should validate");
    fs::remove_dir_all(directory).expect("Core fixture directory should be removable");
    StructuralProgram {
        program,
        source,
        module,
        ty,
    }
}

fn find_core_node(
    program: &ValidatedProgram,
    mut predicate: impl FnMut(&PureExprKind) -> bool,
) -> Option<NodeId> {
    let mut pending = vec![program.root()];
    while let Some(id) = pending.pop() {
        let node = program.node(id)?;
        if predicate(&node.kind) {
            return Some(id);
        }
        for index in (0..node.kind.child_count()).rev() {
            pending.push(node.kind.child_at(index)?);
        }
    }
    None
}

#[test]
fn shared_pipeline_elaborates_and_validates_finite_data_core() {
    let StructuralProgram {
        program,
        source,
        module,
        ty,
    } = elaborated_module(
        "type Wrapped =\nWrap(Int)\n\nmain : Unit -> Int\nmain () = match Wrap(40 + 2) {\nWrap(value) => value\n}\n",
    );

    assert_eq!(ty, Type::Int);
    assert!(
        find_core_node(&program, |kind| matches!(
            kind,
            PureExprKind::Computation(PureComputation::Match(_))
        ))
        .is_some()
    );
    assert_eq!(
        evaluate(&program)
            .expect("retained machine")
            .value
            .to_string(),
        "42"
    );
    let transformed = identity_traversal(&program).expect("identity transform");
    let transformed = validate_modules(transformed, &[&source], &[(module, source.id())])
        .expect("transformed validation");
    assert_eq!(
        evaluate(&transformed)
            .expect("transformed retained machine")
            .value
            .to_string(),
        "42"
    );
    let folded = fold_literal_primitives(&program).expect("literal transform");
    let folded =
        validate_modules(folded, &[&source], &[(module, source.id())]).expect("folded validation");
    assert_eq!(
        evaluate(&folded)
            .expect("folded retained machine")
            .value
            .to_string(),
        "42"
    );
}

#[test]
fn constructor_tuple_payloads_enter_elements_strictly_left_to_right() {
    let StructuralProgram { program, .. } = elaborated_module(
        "type Pair =\nPair(Int, Int)\n\nmain : Unit -> Pair\nmain () = Pair(20, 22)\n",
    );
    let application_id = find_core_node(&program, |kind| match kind {
        PureExprKind::Computation(PureComputation::Apply(application)) => program
            .node(application.argument())
            .is_some_and(|argument| {
                matches!(
                    argument.kind,
                    PureExprKind::Computation(PureComputation::Tuple(_))
                )
            }),
        _ => false,
    })
    .expect("constructor application");
    let application = match &program
        .node(application_id)
        .expect("constructor application")
        .kind
    {
        PureExprKind::Computation(PureComputation::Apply(application)) => application,
        _ => unreachable!("the selected node is an application"),
    };
    let argument = program
        .node(application.argument())
        .expect("tuple argument");
    let PureExprKind::Computation(PureComputation::Tuple(tuple)) = &argument.kind else {
        panic!("expected tuple payload")
    };
    let evaluation = evaluate(&program).expect("constructor application should evaluate");
    let entered = evaluation
        .trace
        .iter()
        .map(|event| match event {
            TraceEvent::Enter(node) => *node,
        })
        .collect::<Vec<_>>();
    let relevant = entered
        .into_iter()
        .filter(|node| {
            *node == application_id
                || *node == application.function()
                || *node == application.argument()
                || tuple.elements().contains(node)
        })
        .collect::<Vec<_>>();

    assert_eq!(
        relevant,
        vec![
            application_id,
            application.function(),
            application.argument(),
            tuple.elements()[0],
            tuple.elements()[1],
        ]
    );
}

#[test]
fn shared_pipeline_validates_equations_tuple_domains_and_local_patterns() {
    for (text, expected) in [
        (
            "type Tree =\nLeaf(Int)\n| Node(Tree, Tree)\n\ndepth : Tree -> Int\ndepth (Leaf value) = 1\ndepth (Node(left, right)) = depth left + depth right\n\nmain : Unit -> Int\nmain () = depth (Node(Leaf(1), Leaf(2)))\n",
            "2",
        ),
        (
            "fn add(left : Int, right : Int) -> Int {\nleft + right\n}\n\nmain : Unit -> Int\nmain () = add(20, 22)\n",
            "42",
        ),
        (
            "main : Unit -> Int\nmain () = {\nlet (left, right) = (20, 22)\nleft + right\n}\n",
            "42",
        ),
    ] {
        let StructuralProgram { program, ty, .. } = elaborated_module(text);
        assert_eq!(ty, Type::Int);
        assert_eq!(
            evaluate(&program)
                .expect("retained machine")
                .value
                .to_string(),
            expected
        );
    }
}

fn run(text: &str) -> Observation {
    run_module("data-and-adts.ash", text).expect("fixture should run")
}

fn rejection(text: &str) -> String {
    let error =
        run_module("data-and-adts-rejection.ash", text).expect_err("fixture should be rejected");
    format!("{} {error:?}", error.reason_code())
}

#[test]
fn finite_nominal_tree_patterns_execute() {
    let observation = run(
        "type IntTree =\nLeaf(Int)\n| Node(IntTree, IntTree)\n\ndepth : IntTree -> Int\ndepth (Leaf value) = 1\ndepth (Node(left, right)) = depth left + depth right\n\nmain : Unit -> Int\nmain () = depth (Node(Leaf(1), Leaf(2)))\n",
    );

    assert_eq!(observation.value.to_string(), "2");
    assert_eq!(observation.ty.to_string(), "Int");
}

#[test]
fn operational_tuple_domains_are_distinct_from_curried_functions() {
    let observation = run(
        "fn add(left : Int, right : Int) -> Int {\nleft + right\n}\n\nmain : Unit -> Int\nmain () = add(20, 22)\n",
    );

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty.to_string(), "Int");
}

#[test]
fn payload_constructors_are_higher_order_unary_values() {
    let observation = run(
        "type Wrapped =\nWrap(Int)\n\nfn build(make : Int -> Wrapped) -> Wrapped {\nmake 42\n}\n\nmain : Unit -> Int\nmain () = match build Wrap {\nWrap(value) => value\n}\n",
    );

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty.to_string(), "Int");
}

#[test]
fn contextually_typed_matches_check_every_anonymous_function_arm() {
    let observation = run(
        "fn choose(flag : Bool) -> Int -> Int {\nmatch flag {\ntrue => fn(value) {\nvalue + 1\n}\nfalse => fn(value) {\nvalue * 2\n}\n}\n}\n\nmain : Unit -> Int\nmain () = choose true 41\n",
    );

    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn local_tuple_patterns_are_irrefutable() {
    let observation =
        run("main : Unit -> Int\nmain () = {\nlet (left, right) = (20, 22)\nleft + right\n}\n");

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty.to_string(), "Int");
}

#[test]
fn explicit_match_and_equations_have_equivalent_recursive_coverage() {
    let observation = run(
        "type Tree =\nTip(Int)\n| Fork(Tree, Tree)\n\nsize : Tree -> Int\nsize (Tip value) = 1\nsize (Fork(left, right)) = size left + size right\n\nfn size_match(tree : Tree) -> Int {\nmatch tree {\nTip(value) => 1\nFork(left, right) => size_match left + size_match right\n}\n}\n\nmain : Unit -> Int\nmain () = size (Fork(Tip(0), Tip(0))) + size_match (Fork(Tip(0), Tip(0)))\n",
    );

    assert_eq!(observation.value.to_string(), "4");
    assert_eq!(observation.ty.to_string(), "Int");
}

#[test]
fn constructor_guarded_recursive_data_renders_cycles_structurally() {
    let observation = run(
        "type Stream =\nNext(Int, Stream)\n\nmain : Unit -> Stream\nmain () = {\nlet rec ones : Stream = Next(1, ones)\nones\n}\n",
    );

    assert_eq!(observation.value.to_string(), "Next(1, <cycle>)");
    assert_eq!(observation.type_display(), "Stream");
}

#[test]
fn declaration_and_constructor_names_have_stable_rejections() {
    let cases = [
        (
            "type Item =\nFirst\n\ntype Item =\nSecond\n\nmain : Unit -> Item\nmain () = First\n",
            "resolve.duplicate-type",
        ),
        (
            "type Left =\nSame\n\ntype Right =\nSame\n\nmain : Unit -> Left\nmain () = Same\n",
            "resolve.duplicate-constructor",
        ),
        (
            "type Broken =\nBroken(Missing)\n\nmain : Unit -> Broken\nmain () = Broken\n",
            "resolve.unknown-type",
        ),
        (
            "main : Unit -> Unit\nmain () = Missing\n",
            "resolve.unknown-constructor",
        ),
    ];

    for (text, reason) in cases {
        assert!(rejection(text).contains(reason), "missing {reason}");
    }
}

#[test]
fn pattern_typing_has_stable_rejections() {
    let cases = [
        (
            "type Pair =\nPair(Int, Int)\n\nmain : Unit -> Int\nmain () = match Pair(1, 2) {\nPair(value, value) => value\n}\n",
            "pattern.duplicate-binder",
        ),
        (
            "type Left =\nLeft\n\ntype Right =\nRight(Int)\n\nfn inspect(value : Left) -> Int {\nmatch value {\nRight(payload) => payload\n}\n}\n\nmain : Unit -> Int\nmain () = inspect Left\n",
            "pattern.constructor-owner",
        ),
        (
            "type Maybe =\nNone\n| Some(Int)\n\nmain : Unit -> Int\nmain () = {\nlet Some(value) = Some(1)\nvalue\n}\n",
            "pattern.refutable-binding",
        ),
        (
            "type Maybe =\nNone\n| Some(Int)\n\nmain : Unit -> Int\nmain () = match Some(1) {\nSome(value) => value\n}\n",
            "coverage.non-exhaustive",
        ),
        (
            "type Maybe =\nNone\n| Some(Int)\n\nmain : Unit -> Int\nmain () = match Some(1) {\n_ => 0\nSome(value) => value\n}\n",
            "coverage.redundant-case",
        ),
    ];

    for (text, reason) in cases {
        assert!(rejection(text).contains(reason), "missing {reason}");
    }
}

#[test]
fn equation_groups_reject_inconsistent_pattern_arity() {
    let error = rejection(
        "type Flag =\nOff\n| On\n\nchoose : Flag -> Int -> Int\nchoose Off value = value\nchoose On = fn(value) {\nvalue\n}\n\nmain : Unit -> Int\nmain () = choose On 42\n",
    );

    assert!(error.contains("equation.arity"));
}

#[test]
fn pattern_equations_use_the_retained_pipeline_without_data_markers() {
    let curried = run(
        "choose : Bool -> Int -> Int\nchoose true left = left\nchoose false right = right + 1\n\nmain : Unit -> Int\nmain () = choose false 41\n",
    );
    assert_eq!(curried.value_display(), "42");

    let unit =
        run("answer : Unit -> Int\nanswer () = 42\n\nmain : Unit -> Int\nmain () = answer ()\n");
    assert_eq!(unit.value_display(), "42");

    let redundant = rejection(
        "keep : Int -> Int\nkeep value = value\nkeep other = other\n\nmain : Unit -> Int\nmain () = keep 42\n",
    );
    assert!(redundant.contains("coverage.redundant-case"));

    let duplicate = rejection(
        "same : Int -> Int -> Int\nsame value value = value\n\nmain : Unit -> Int\nmain () = same 1 2\n",
    );
    assert!(duplicate.contains("pattern.duplicate-binder"));

    let equality_bodies = run(
        "truth : Bool -> Bool\ntruth true = 1 == 1\ntruth false = 0 == 1\n\nmain : Unit -> Bool\nmain () = truth true\n",
    );
    assert_eq!(equality_bodies.value_display(), "true");
}

#[test]
fn recursive_data_requires_a_constructor_root_and_guarded_occurrences() {
    let nullary = run(
        "type Flag =\nOff\n| On\n\nmain : Unit -> Flag\nmain () = {\nlet rec flag : Flag = Off\nflag\n}\n",
    );
    assert_eq!(nullary.value_display(), "Off");

    let unsafe_root = rejection(
        "type Stream =\nNext(Int, Stream)\n\nmain : Unit -> Stream\nmain () = {\nlet rec stream : Stream = {\nNext(1, stream)\n}\nstream\n}\n",
    );
    assert!(unsafe_root.contains("recursion.unsafe-root"));

    let unguarded = rejection(
        "type Stream =\nNext(Int, Stream)\n\nfn identity(value : Stream) -> Stream {\nvalue\n}\n\nmain : Unit -> Stream\nmain () = {\nlet rec stream : Stream = Next(1, identity stream)\nstream\n}\n",
    );
    assert!(unguarded.contains("recursion.unguarded-use"));
}

#[test]
fn excluded_pattern_families_remain_rejected() {
    for text in [
        "main : Unit -> Int\nmain () = match true {\n1 => 0\n_ => 1\n}\n",
        "main : Unit -> Int\nmain () = match true {\ntrue | false => 0\n}\n",
    ] {
        assert!(rejection(text).contains("parse."));
    }
}

#[test]
fn retained_data_syntax_failures_keep_the_exact_current_token_span() {
    let text = "main : Unit -> Int\nmain () = match true {\ntrue 0\nfalse => 1\n}\n";
    let failure =
        run_module("data-span.ash", text).expect_err("the missing arrow must be rejected");
    let PipelineFailure::Syntax(failure) = failure else {
        panic!("the retained grammar should own this rejection")
    };
    let diagnostic = failure.parser.first().expect("parser rejection");
    assert_eq!(diagnostic.reason.to_string(), "parse.expected-form");
    let span = diagnostic.primary.span();
    let start = u32::try_from(text.find('0').expect("fixture contains zero"))
        .expect("fixture offset should fit");
    assert_eq!(span.range().start(), start);
    assert_eq!(span.range().end(), start + 1);
}

#[test]
fn an_empty_match_is_rejected_by_the_retained_syntax_stage() {
    let failure = run_module(
        "empty-match.ash",
        "main : Unit -> Int\nmain () = match true {\n}\n",
    )
    .expect_err("a match requires an arm");
    let PipelineFailure::Syntax(failure) = failure else {
        panic!("the retained grammar must reject an empty match")
    };
    let diagnostic = failure.parser.first().expect("parser rejection");
    assert_eq!(diagnostic.reason.to_string(), "parse.expected-form");
    assert_eq!(diagnostic.expected.as_deref(), Some("a pattern"));
}

#[test]
fn admitted_nested_patterns_complete_the_full_pipeline_on_a_small_stack() {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(512 * 1024)
            .spawn_scoped(scope, || {
                let depth = ash::parser::STRUCTURAL_DEPTH_LIMIT / 8 - 4;
                let mut pattern = "_".to_owned();
                for _ in 0..depth {
                    pattern = format!("Step({pattern})");
                }
                let text = format!(
                    "type Chain =\nEnd\n| Step(Chain)\n\nmain : Unit -> Int\nmain () = match End {{\n{pattern} => 1\n_ => 0\n}}\n"
                );
                let observation = run_module("pattern-full-boundary.ash", &text)
                    .expect("admitted pattern must complete");
                assert_eq!(observation.value_display(), "0");

                let match_depth = ash::parser::STRUCTURAL_DEPTH_LIMIT / 32;
                let mut text = "main : Unit -> Int\nmain () = ".to_owned();
                text.push_str(&"match true {\n_ => ".repeat(match_depth));
                text.push('0');
                text.push('\n');
                text.push_str(&"}\n".repeat(match_depth));
                let observation = run_module("match-full-boundary.ash", &text)
                    .expect("admitted matches must complete");
                assert_eq!(observation.value_display(), "0");

                let mut deep_equation_pattern = "_".to_owned();
                for _ in 0..(ash::parser::STRUCTURAL_DEPTH_LIMIT / 8) {
                    deep_equation_pattern = format!("Step({deep_equation_pattern})");
                }
                let text = format!(
                    "type Chain =\nStep(Chain)\n\npick : Chain -> Int -> Int\npick {deep_equation_pattern} value = value\n\nmain : Unit -> Int\nmain () = 0\n"
                );
                let observation = run_module("equation-pattern-boundary.ash", &text)
                    .expect("tuple-lowered equation must complete");
                assert_eq!(observation.value_display(), "0");

                let text = format!(
                    "type Chain =\nStep(Chain)\n\nfn pick({deep_equation_pattern} : Chain, value : Int) -> Int {{\nvalue\n}}\n\nmain : Unit -> Int\nmain () = 0\n"
                );
                let observation = run_module("operational-pattern-boundary.ash", &text)
                    .expect("tuple-lowered operational header must complete");
                assert_eq!(observation.value_display(), "0");
            })
            .expect("small-stack thread should start")
            .join()
            .expect("full pattern pipeline must fit the small stack");
    });
}

#[test]
fn admitted_type_depth_survives_synthesized_tuple_and_function_wrappers() {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn_scoped(scope, || {
                let mut deep_type = "Unit".to_owned();
                for _ in 0..ash::parser::STRUCTURAL_DEPTH_LIMIT {
                    deep_type = format!("Unit -> {deep_type}");
                }
                let operational = format!(
                    "fn pick(value : {deep_type}, other : Int) -> Int {{\n0\n}}\n\nmain : Unit -> Int\nmain () = 0\n"
                );
                let observation = run_module("operational-type-boundary.ash", &operational)
                    .expect("tuple/function lowering must fit");
                assert_eq!(observation.value_display(), "0");

                let declaration = format!(
                    "type Boxed =\nMake({deep_type}, Int)\n\nmain : Unit -> Int\nmain () = 0\n"
                );
                let observation = run_module("constructor-type-boundary.ash", &declaration)
                    .expect("constructor payload lowering must fit");
                assert_eq!(observation.value_display(), "0");
            })
            .expect("small-stack thread should start")
            .join()
            .expect("lowered type wrappers must fit the small stack");
    });
}

#[test]
fn a_wide_constructor_set_has_practical_exhaustive_coverage() {
    const WIDTH: usize = 512;
    let mut text = "type Wide =\nC0\n".to_owned();
    for index in 1..WIDTH {
        text.push_str(&format!("| C{index}\n"));
    }
    text.push_str(&format!(
        "\nmain : Unit -> Int\nmain () = match C{} {{\n",
        WIDTH - 1
    ));
    for index in 0..WIDTH {
        text.push_str(&format!("C{index} => {index}\n"));
    }
    text.push_str("}\n");
    let observation =
        run_module("wide-constructors.ash", &text).expect("wide exhaustive match should complete");
    assert_eq!(observation.value_display(), (WIDTH - 1).to_string());
}

#[test]
fn an_over_budget_case_group_reports_an_internal_resource_failure() {
    const WIDTH: usize = 800;
    let mut text = "type TooWide =\nC0\n".to_owned();
    for index in 1..WIDTH {
        text.push_str(&format!("| C{index}\n"));
    }
    text.push_str("\nmain : Unit -> Int\nmain () = match C0 {\n");
    for index in 0..WIDTH {
        text.push_str(&format!("C{index} => {index}\n"));
    }
    text.push_str("}\n");
    let error =
        run_module("coverage-resource.ash", &text).expect_err("coverage work must be bounded");
    let PipelineFailure::Typing(TypeError::Internal(failure)) = error else {
        panic!("coverage exhaustion must remain an internal resource failure")
    };
    assert_eq!(failure, ElaborationFailure::CoverageResourceExhausted);
}

#[test]
fn a_wide_tuple_case_group_charges_type_and_specialization_cells() {
    const WIDTH: usize = 100_000;
    let mut text = String::with_capacity(WIDTH * 5 + 32);
    text.push_str("main : Unit -> Int\nmain () = match (");
    for index in 0..WIDTH {
        if index > 0 {
            text.push_str(", ");
        }
        text.push('0');
    }
    text.push_str(") {\n(");
    for index in 0..WIDTH {
        if index > 0 {
            text.push_str(", ");
        }
        text.push('_');
    }
    text.push_str(") => 0\n}\n");

    let error = run_module("wide-tuple-coverage.ash", &text)
        .expect_err("tuple coverage materialization must be bounded");
    let PipelineFailure::Typing(TypeError::Internal(failure)) = error else {
        panic!("coverage exhaustion must remain an internal resource failure")
    };
    assert_eq!(failure, ElaborationFailure::CoverageResourceExhausted);
}

#[test]
fn wider_tuple_syntax_reports_a_structured_internal_resource_failure() {
    const WIDTH: usize = 110_000;
    let mut text = String::with_capacity(WIDTH * 5 + 32);
    text.push_str("main : Unit -> Int\nmain () = match (");
    for index in 0..WIDTH {
        if index > 0 {
            text.push_str(", ");
        }
        text.push('0');
    }
    text.push_str(") {\n(");
    for index in 0..WIDTH {
        if index > 0 {
            text.push_str(", ");
        }
        text.push('_');
    }
    text.push_str(") => 0\n}\n");
    let error = run_module("syntax-work-pipeline.ash", &text)
        .expect_err("syntax work must be bounded before projection");

    let PipelineFailure::Syntax(failure) = &error else {
        panic!("syntax work exhaustion must remain owned by the syntax stage")
    };
    assert_eq!(
        failure.resource,
        Some(ResourceFailure::SyntaxWork {
            limit: SYNTAX_WORK_LIMIT
        })
    );
    assert_eq!(error.reason_code(), "internal.resource.syntax-work");
    assert!(!error.is_source_rejection());
    assert_eq!(
        render::pipeline_failure(&error),
        format!("internal.resource.syntax-work\nlimit {SYNTAX_WORK_LIMIT}")
    );
}

#[test]
fn match_trace_enters_the_scrutinee_once_and_only_the_selected_body() {
    use ash::{
        core::{CoreBuilder, CoreMatchArm, CorePattern, CorePatternKind},
        integer::Integer,
        source::{ByteRange, Origin},
        types::Type,
    };

    let file = SourceFile::new("match-trace.ash", "match trace").expect("trace fixture should fit");
    let origin = Origin::Source(
        file.span(ByteRange::new(0, 11).expect("ordered range"))
            .expect("fixture span"),
    );
    let mut builder = CoreBuilder::new();
    let scrutinee = builder
        .boolean(true, Type::Bool, origin.clone())
        .expect("scrutinee");
    let selected = builder
        .integer(
            Integer::parse_decimal("1").expect("integer"),
            Type::Int,
            origin.clone(),
        )
        .expect("selected body");
    let unselected = builder
        .integer(
            Integer::parse_decimal("2").expect("integer"),
            Type::Int,
            origin.clone(),
        )
        .expect("unselected body");
    let arm = |value, body| {
        CoreMatchArm::new(
            CorePattern::new(Type::Bool, origin.clone(), CorePatternKind::Boolean(value)),
            body,
            origin.clone(),
        )
    };
    let root = builder
        .match_expression(
            scrutinee,
            vec![arm(true, selected), arm(false, unselected)],
            Type::Int,
            origin,
        )
        .expect("match");
    let program = validate(builder.finish(root).expect("root"), &[&file]).expect("valid Core");
    let evaluation = evaluate(&program).expect("match evaluation");
    assert_eq!(evaluation.value.to_string(), "1");
    assert_eq!(
        evaluation.trace,
        vec![
            TraceEvent::Enter(root),
            TraceEvent::Enter(scrutinee),
            TraceEvent::Enter(selected),
        ]
    );
}

#[test]
fn nominal_declarations_are_file_wide_recursive_and_distinct() {
    let forward = run(
        "type Left =\nLeft(Right)\n\ntype Right =\nRight(Int)\n\nmain : Unit -> Left\nmain () = Left(Right(42))\n",
    );
    assert_eq!(forward.value_display(), "Left(Right(42))");
    assert_eq!(forward.type_display(), "Left");

    let mismatch = rejection(
        "type First =\nFirst(Int)\n\ntype Second =\nSecond(Int)\n\nfn take(value : First) -> Int {\nmatch value {\nFirst(payload) => payload\n}\n}\n\nmain : Unit -> Int\nmain () = take Second(1)\n",
    );
    assert!(mismatch.contains("type.argument"));
}

#[test]
fn coverage_handles_bool_unit_tuples_and_recursive_nominals() {
    let observation = run(
        "type Nat =\nZero\n| Succ(Nat)\n\nfn classify(value : (Bool, Unit, Nat)) -> Int {\nmatch value {\n(true, (), _) => 1\n(false, (), Zero) => 2\n(false, (), Succ(_)) => 3\n}\n}\n\nmain : Unit -> Int\nmain () = classify(false, (), Succ(Zero))\n",
    );
    assert_eq!(observation.value_display(), "3");

    let missing = rejection(
        "main : Unit -> Int\nmain () = match (true, false) {\n(true, _) => 1\n(false, true) => 2\n}\n",
    );
    assert!(missing.contains("coverage.non-exhaustive"));
    assert!(missing.contains("(false, false)"));
}

#[test]
fn rendering_repeats_shared_values_and_marks_only_active_cycles() {
    let shared = run(
        "type Tree =\nLeaf(Int)\n| Pair(Tree, Tree)\n\nmain : Unit -> Tree\nmain () = {\nlet leaf = Leaf(1)\nPair(leaf, leaf)\n}\n",
    );
    assert_eq!(shared.value_display(), "Pair(Leaf(1), Leaf(1))");

    let mutual = run(
        "type Left =\nLeft(Right)\n\ntype Right =\nRight(Left)\n\nmain : Unit -> Left\nmain () = {\nlet rec left : Left = Left(right)\nand right : Right = Right(left)\nleft\n}\n",
    );
    assert_eq!(mutual.value_display(), "Left(Right(<cycle>))");
}

#[test]
fn mixed_recursive_groups_support_functions_and_guarded_data() {
    let observation = run(
        "type Stream =\nNext(Int, Stream)\n\nmain : Unit -> Int\nmain () = {\nlet rec ones : Stream = Next(1, ones)\nand head : Stream -> Int = fn(stream) {\nmatch stream {\nNext(value, tail) => value\n}\n}\nhead ones\n}\n",
    );
    assert_eq!(observation.value_display(), "1");
}

#[test]
fn tuple_domain_anonymous_functions_receive_one_expected_tuple() {
    let observation = run(
        "fn apply(operation : (Int, Int) -> Int) -> Int {\noperation(20, 22)\n}\n\nmain : Unit -> Int\nmain () = apply (fn(left, right) {\nleft + right\n})\n",
    );
    assert_eq!(observation.value_display(), "42");
}

#[test]
fn single_clause_function_domain_patterns_must_be_irrefutable() {
    let operational = rejection(
        "type Maybe =\nNone\n| Some(Int)\n\nfn unsafe(Some(value) : Maybe) -> Int {\nvalue\n}\n\nmain : Unit -> Int\nmain () = unsafe None\n",
    );
    assert!(operational.contains("pattern.refutable-function-domain"));

    let anonymous = rejection(
        "type Maybe =\nNone\n| Some(Int)\n\nmain : Unit -> Int\nmain () = {\nlet unsafe : Maybe -> Int = fn(Some(value)) {\nvalue\n}\nunsafe None\n}\n",
    );
    assert!(anonymous.contains("pattern.refutable-function-domain"));
}

#[test]
fn ten_thousand_member_cycle_evaluates_renders_and_drops_on_a_small_stack() {
    std::thread::Builder::new()
        .name("deep-data-cycle".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            const MEMBERS: usize = 10_000;
            let mut source = String::from(
                "type Chain =\nLink(Chain)\n\nmain : Unit -> Chain\nmain () = {\nlet rec value0 : Chain = Link(value1)\n",
            );
            for index in 1..MEMBERS {
                let next = if index + 1 == MEMBERS { 0 } else { index + 1 };
                source.push_str(&format!("and value{index} : Chain = Link(value{next})\n"));
            }
            source.push_str("value0\n}\n");

            let observation = run(&source);
            assert_eq!(observation.type_display(), "Chain");
            let rendered = observation.value_display();
            assert!(rendered.starts_with("Link(Link(Link("));
            assert!(rendered.ends_with(')'));
            assert_eq!(rendered.matches("Link(").count(), MEMBERS);
            assert_eq!(rendered.matches("<cycle>").count(), 1);
        })
        .expect("the deep-data thread should start")
        .join()
        .expect("the retained pipeline should fit the small host stack");
}
