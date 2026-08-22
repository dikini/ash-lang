use ash::{
    driver::{Observation, PipelineFailure, run_source},
    extended::ExtendedStage,
    source::SourceFile,
};

fn run(text: &str) -> Observation {
    run_source(SourceFile::new("data-and-adts.ash", text).expect("fixture should fit"))
        .expect("fixture should run")
}

fn rejection(text: &str) -> String {
    let error = run_source(
        SourceFile::new("data-and-adts-rejection.ash", text).expect("fixture should fit"),
    )
    .expect_err("fixture should be rejected");
    format!("{error:?}")
}

#[test]
fn finite_nominal_tree_patterns_execute() {
    let observation = run(
        "type IntTree =\nLeaf(Int)\n| Node(IntTree, IntTree)\n\ndepth : IntTree -> Int\ndepth (Leaf value) = 1\ndepth (Node(left, right)) = depth left + depth right\n\ndepth (Node(Leaf(1), Leaf(2)))\n",
    );

    assert_eq!(observation.value.to_string(), "2");
    assert_eq!(observation.ty.to_string(), "Int");
}

#[test]
fn operational_tuple_domains_are_distinct_from_curried_functions() {
    let observation =
        run("fn add(left : Int, right : Int) -> Int {\nleft + right\n}\n\nadd(20, 22)\n");

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty.to_string(), "Int");
}

#[test]
fn payload_constructors_are_higher_order_unary_values() {
    let observation = run(
        "type Wrapped =\nWrap(Int)\n\nfn build(make : Int -> Wrapped) -> Wrapped {\nmake 42\n}\n\nmatch build Wrap {\nWrap(value) => value\n}\n",
    );

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty.to_string(), "Int");
}

#[test]
fn local_tuple_patterns_are_irrefutable() {
    let observation = run("{\nlet (left, right) = (20, 22)\nleft + right\n}\n");

    assert_eq!(observation.value.to_string(), "42");
    assert_eq!(observation.ty.to_string(), "Int");
}

#[test]
fn explicit_match_and_equations_have_equivalent_recursive_coverage() {
    let observation = run(
        "type Tree =\nTip(Int)\n| Fork(Tree, Tree)\n\nsize : Tree -> Int\nsize (Tip value) = 1\nsize (Fork(left, right)) = size left + size right\n\nfn size_match(tree : Tree) -> Int {\nmatch tree {\nTip(value) => 1\nFork(left, right) => size_match left + size_match right\n}\n}\n\nsize (Fork(Tip(0), Tip(0))) + size_match (Fork(Tip(0), Tip(0)))\n",
    );

    assert_eq!(observation.value.to_string(), "4");
    assert_eq!(observation.ty.to_string(), "Int");
}

#[test]
fn constructor_guarded_recursive_data_renders_cycles_structurally() {
    let observation = run(
        "type Stream =\nNext(Int, Stream)\n\n{\nlet rec ones : Stream = Next(1, ones)\nones\n}\n",
    );

    assert_eq!(observation.value.to_string(), "Next(1, <cycle>)");
    assert_eq!(observation.type_display(), "Stream");
}

#[test]
fn declaration_and_constructor_names_have_stable_rejections() {
    let cases = [
        (
            "type Item =\nFirst\n\ntype Item =\nSecond\n\nFirst\n",
            "resolve.duplicate-type",
        ),
        (
            "type Left =\nSame\n\ntype Right =\nSame\n\nSame\n",
            "resolve.duplicate-constructor",
        ),
        (
            "type Broken =\nBroken(Missing)\n\nBroken\n",
            "resolve.unknown-type",
        ),
        ("Missing\n", "resolve.unknown-constructor"),
    ];

    for (text, reason) in cases {
        assert!(rejection(text).contains(reason), "missing {reason}");
    }
}

#[test]
fn pattern_typing_has_stable_rejections() {
    let cases = [
        (
            "type Pair =\nPair(Int, Int)\n\nmatch Pair(1, 2) {\nPair(value, value) => value\n}\n",
            "pattern.duplicate-binder",
        ),
        (
            "type Left =\nLeft\n\ntype Right =\nRight(Int)\n\nfn inspect(value : Left) -> Int {\nmatch value {\nRight(payload) => payload\n}\n}\n\ninspect Left\n",
            "pattern.constructor-owner",
        ),
        (
            "type Maybe =\nNone\n| Some(Int)\n\n{\nlet Some(value) = Some(1)\nvalue\n}\n",
            "pattern.refutable-binding",
        ),
        (
            "type Maybe =\nNone\n| Some(Int)\n\nmatch Some(1) {\nSome(value) => value\n}\n",
            "coverage.non-exhaustive",
        ),
        (
            "type Maybe =\nNone\n| Some(Int)\n\nmatch Some(1) {\n_ => 0\nSome(value) => value\n}\n",
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
        "type Flag =\nOff\n| On\n\nchoose : Flag -> Int -> Int\nchoose Off value = value\nchoose On = fn(value) {\nvalue\n}\n\nchoose On 42\n",
    );

    assert!(error.contains("equation.arity"));
}

#[test]
fn recursive_data_requires_a_constructor_root_and_guarded_occurrences() {
    let unsafe_root = rejection(
        "type Stream =\nNext(Int, Stream)\n\n{\nlet rec stream : Stream = {\nNext(1, stream)\n}\nstream\n}\n",
    );
    assert!(unsafe_root.contains("recursion.unsafe-root"));

    let unguarded = rejection(
        "type Stream =\nNext(Int, Stream)\n\nfn identity(value : Stream) -> Stream {\nvalue\n}\n\n{\nlet rec stream : Stream = Next(1, identity stream)\nstream\n}\n",
    );
    assert!(unguarded.contains("recursion.unguarded-use"));
}

#[test]
fn excluded_pattern_families_remain_rejected() {
    for text in [
        "match true {\n1 => 0\n_ => 1\n}\n",
        "match true {\ntrue | false => 0\n}\n",
    ] {
        assert!(rejection(text).contains("parse."));
    }
}

#[test]
fn extended_syntax_failures_keep_the_exact_current_token_span() {
    let text = "match true {\ntrue 0\nfalse => 1\n}\n";
    let source = SourceFile::new("extended-span.ash", text).expect("fixture should fit");
    let failure = run_source(source).expect_err("the missing arrow must be rejected");
    let PipelineFailure::Extended(failure) = failure else {
        panic!("the extended grammar should own this rejection")
    };
    assert_eq!(failure.stage, ExtendedStage::Syntax);
    assert_eq!(failure.reason, "parse.expected-form");
    let span = failure
        .primary
        .expect("syntax rejection needs a primary span");
    let start = u32::try_from(text.find('0').expect("fixture contains zero"))
        .expect("fixture offset should fit");
    assert_eq!(span.range().start(), start);
    assert_eq!(span.range().end(), start + 1);
}

#[test]
fn nominal_declarations_are_file_wide_recursive_and_distinct() {
    let forward = run("type Left =\nLeft(Right)\n\ntype Right =\nRight(Int)\n\nLeft(Right(42))\n");
    assert_eq!(forward.value_display(), "Left(Right(42))");
    assert_eq!(forward.type_display(), "Left");

    let mismatch = rejection(
        "type First =\nFirst(Int)\n\ntype Second =\nSecond(Int)\n\nfn take(value : First) -> Int {\nmatch value {\nFirst(payload) => payload\n}\n}\n\ntake Second(1)\n",
    );
    assert!(mismatch.contains("type.mismatch"));
}

#[test]
fn coverage_handles_bool_unit_tuples_and_recursive_nominals() {
    let observation = run(
        "type Nat =\nZero\n| Succ(Nat)\n\nfn classify(value : (Bool, Unit, Nat)) -> Int {\nmatch value {\n(true, (), _) => 1\n(false, (), Zero) => 2\n(false, (), Succ(_)) => 3\n}\n}\n\nclassify(false, (), Succ(Zero))\n",
    );
    assert_eq!(observation.value_display(), "3");

    let missing = rejection("match (true, false) {\n(true, _) => 1\n(false, true) => 2\n}\n");
    assert!(missing.contains("coverage.non-exhaustive"));
    assert!(missing.contains("(false, false)"));
}

#[test]
fn rendering_repeats_shared_values_and_marks_only_active_cycles() {
    let shared = run(
        "type Tree =\nLeaf(Int)\n| Pair(Tree, Tree)\n\n{\nlet leaf = Leaf(1)\nPair(leaf, leaf)\n}\n",
    );
    assert_eq!(shared.value_display(), "Pair(Leaf(1), Leaf(1))");

    let mutual = run(
        "type Left =\nLeft(Right)\n\ntype Right =\nRight(Left)\n\n{\nlet rec left : Left = Left(right)\nand right : Right = Right(left)\nleft\n}\n",
    );
    assert_eq!(mutual.value_display(), "Left(Right(<cycle>))");
}

#[test]
fn mixed_recursive_groups_support_functions_and_guarded_data() {
    let observation = run(
        "type Stream =\nNext(Int, Stream)\n\n{\nlet rec ones : Stream = Next(1, ones)\nand head : Stream -> Int = fn(stream) {\nmatch stream {\nNext(value, tail) => value\n}\n}\nhead ones\n}\n",
    );
    assert_eq!(observation.value_display(), "1");
}

#[test]
fn tuple_domain_anonymous_functions_receive_one_expected_tuple() {
    let observation = run(
        "fn apply(operation : (Int, Int) -> Int) -> Int {\noperation(20, 22)\n}\n\napply (fn(left, right) {\nleft + right\n})\n",
    );
    assert_eq!(observation.value_display(), "42");
}

#[test]
fn ten_thousand_member_cycle_evaluates_renders_and_drops_on_a_small_stack() {
    std::thread::Builder::new()
        .name("deep-data-cycle".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            const MEMBERS: usize = 10_000;
            let mut source = String::from(
                "type Chain =\nLink(Chain)\n\n{\nlet rec value0 : Chain = Link(value1)\n",
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
        .expect("the data pipeline should fit the small host stack");
}
