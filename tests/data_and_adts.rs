use ash::{
    driver::{Observation, run_source},
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
    let observation = run(
        "fn add(left : Int, right : Int) -> Int {\nleft + right\n}\n\nadd(20, 22)\n",
    );

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
    assert_eq!(observation.ty.to_string(), "Stream");
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
