use ash::{
    driver::{RunConfiguration, run_path},
    module::ModuleRoots,
};
use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT_SOURCE: AtomicU64 = AtomicU64::new(0);

fn run_result(source: &str) -> Result<ash::driver::Observation, ash::driver::FileFailure> {
    let path = std::env::temp_dir().join(format!(
        "ash-region-runtime-{}-{}.ash",
        std::process::id(),
        NEXT_SOURCE.fetch_add(1, Ordering::Relaxed)
    ));
    fs::write(&path, source).unwrap();
    let result = run_path(RunConfiguration {
        entry: path.clone(),
        roots: ModuleRoots::empty(),
    });
    fs::remove_file(path).unwrap();
    result
}

fn run(source: &str) -> String {
    run_result(source)
        .unwrap_or_else(|failure| panic!("{failure:?}"))
        .value_display()
        .to_owned()
}

#[test]
fn declared_host_region_constructs_and_consumes_a_tuple_before_close() {
    assert_eq!(
        run(
            "main : Unit -> Int\nmain () = region<R> r {\nlet pair = (20, 22)\nmatch pair {\n(left, right) => match (left + right) == 42 {\ntrue => 42\nfalse => 0\n}\n}\n}\n"
        ),
        "42"
    );
}

#[test]
fn explicit_selection_constructs_under_an_enclosing_live_region() {
    assert_eq!(
        run(
            "main : Unit -> Int\nmain () = region<R> outer {\nregion<S> inner {\nusing outer {\nlet pair = (20, 22)\nmatch pair {\n(left, right) => match (left + right) == 42 {\ntrue => 42\nfalse => 0\n}\n}\n}\n}\n}\n"
        ),
        "42"
    );
}

#[test]
fn ordinary_construction_without_selection_uses_generated_root() {
    assert_eq!(
        run("main : Unit -> Int\nmain () = match (20, 22) {\n(left, right) => left + right\n}\n"),
        "42"
    );
}

#[test]
fn ordinary_closure_records_cannot_escape_their_creation_region() {
    for body in ["42", "captured"] {
        let source = format!(
            "main : Unit -> (Unit -> Int)\nmain () = region<R> owner {{\nlet captured = 42\nlet function : Unit -> Int = fn(ignored) {{\n{body}\n}}\nfunction\n}}\n"
        );
        let failure = run_result(&source).unwrap_err();
        let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
            panic!("expected source lifetime rejection, got {failure:?}");
        };
        let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(error)) =
            diagnostic.failure()
        else {
            panic!("expected source resource escape, got {diagnostic:?}");
        };
        assert_eq!(error.reason, ash::elaborate::TypeReason::ResourceEscape);
    }
}

#[test]
fn ordinary_closure_explicitly_created_in_outer_region_survives_inner_close() {
    assert_eq!(
        run(concat!(
            "main : Unit -> Int\nmain () = region<R> outer {\n",
            "let function : Unit -> Int = region<S> inner {\nusing outer {\n",
            "let captured = 42\nlet saved : Unit -> Int = fn(ignored) {\ncaptured\n}\nsaved\n}\n}\nfunction ()\n}\n",
        )),
        "42"
    );
}

#[test]
fn generated_root_does_not_hide_unrelated_outstanding_effects() {
    let failure = run_result("effect Console {\nwrite : Unit -> Unit\n}\nmain : Unit -> Unit ! {Console}\nmain () = perform Console.write ()\n").unwrap_err();
    let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
        panic!("expected source rejection");
    };
    assert!(format!("{diagnostic:?}").contains("MainEffects"));
}

#[test]
fn binding_facade_imports_share_the_generated_service_identity() {
    assert_eq!(
        run(concat!(
            "import @builtin.regions as Region\n",
            "import @builtin.foreign as Foreign\n",
            "inspect : Region.Request -> Int\ninspect request = Region.usable_bytes request\n",
            "adapt<R> : (Region.Request, Foreign.Address, Int, Int) -> Region.Storage<R>\nadapt value = Region.from_backing value\n",
            "main : Unit -> Int\nmain () = 42\n",
        )),
        "42"
    );
}

#[test]
fn binding_facade_does_not_export_the_generated_default_effect() {
    let failure = run_result("import @builtin.regions as Region\nmain : Unit -> Unit ! {Region.DefaultAlloc}\nmain () = ()\n").unwrap_err();
    assert!(format!("{failure:?}").contains("Resolve"), "{failure:?}");
}

#[test]
fn binding_facade_does_not_export_private_view_types() {
    for hidden in ["RegionView", "StorageView"] {
        let source = format!(
            "import @builtin.regions as Region\nprobe : Region.{hidden} -> Unit\nprobe value = ()\nmain : Unit -> Unit\nmain () = ()\n"
        );
        let failure = run_result(&source).unwrap_err();
        assert!(format!("{failure:?}").contains("Resolve"), "{failure:?}");
    }
}

#[test]
fn generated_service_has_no_user_import_spelling() {
    let failure = run_result(
        "import @builtin.region_service as Service\nmain : Unit -> Unit\nmain () = ()\n",
    )
    .unwrap_err();
    assert!(
        format!("{failure:?}").contains("UnknownBuiltin"),
        "{failure:?}"
    );
}

#[test]
fn region_access_cannot_be_used_after_its_owner_closes() {
    assert!(run_result("main : Unit -> Int\nmain () = {\nlet leaked = region<R> r { r }\nusing leaked { 42 }\n}\n").is_err());
}

#[test]
fn outer_selected_tuple_remains_readable_after_inner_close() {
    assert_eq!(
        run(concat!(
            "main : Unit -> Int\nmain () = region<R> outer {\n",
            "let kept = region<S> inner {\nlet local = (1, 2)\n",
            "let total = match local {\n(a, b) => match (a + b) == 42 {\ntrue => 42\nfalse => 0\n}\n}\n",
            "using outer {\n(20, 22)\n}\n}\n",
            "match kept {\n(a, b) => match (a + b) == 42 {\ntrue => 42\nfalse => 0\n}\n}\n}\n",
        )),
        "42"
    );
}

#[test]
fn generated_root_backing_survives_tuple_observation() {
    assert_eq!(
        run("main : Unit -> (Int, Int)\nmain () = (20, 22)\n"),
        "(20, 22)"
    );
}

#[test]
fn nominal_records_cannot_escape_their_declared_region() {
    for expression in ["Empty", "Full 42"] {
        let source = format!(
            "type Item =\nEmpty\n| Full(Int)\nmain : Unit -> Item\nmain () = region<R> owner {{\n{expression}\n}}\n"
        );
        let failure = run_result(&source).unwrap_err();
        let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
            panic!("expected the source lifetime diagnostic, got {failure:?}");
        };
        let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(error)) =
            diagnostic.failure()
        else {
            panic!("expected source resource escape, got {diagnostic:?}");
        };
        assert_eq!(error.reason, ash::elaborate::TypeReason::ResourceEscape);
    }
}

#[test]
fn constructor_alias_uses_the_callers_selected_region() {
    assert_eq!(
        run(concat!(
            "type Item = Full(Int)\nmain : Unit -> Int\nmain () = region<R> outer {\n",
            "let construct = Full\nlet kept = region<S> inner {\nusing outer {\nconstruct 42\n}\n}\n",
            "match kept {\nFull(value) => value\n}\n}\n",
        )),
        "42"
    );
}

#[test]
fn higher_order_constructor_uses_the_callers_selected_region() {
    assert_eq!(
        run(concat!(
            "type Item = Full(Int)\napply : (Int -> Item, Int) -> Item\n",
            "apply (construct, value) = construct value\nmain : Unit -> Int\n",
            "main () = region<R> outer {\nlet kept = region<S> inner {\nusing outer {\napply (Full, 42)\n}\n}\n",
            "match kept {\nFull(value) => value\n}\n}\n",
        )),
        "42"
    );
}

#[test]
fn nominal_tags_are_distinct_from_tuple_constructor_functions() {
    assert_eq!(
        run("type Item = Full(Int)\nmain : Unit -> (Int -> Item, Int)\nmain () = (Full, 42)\n"),
        "(<function>, 42)"
    );
    assert_eq!(
        run(
            "type Tree =\nLeaf(Int)\n| Wrap(Tree)\nmain : Unit -> Tree\nmain () = Wrap (Leaf 42)\n"
        ),
        "Wrap(Leaf(42))"
    );
    assert_eq!(
        run(
            "type Tree =\nLeaf(Int)\n| Wrap(Tree)\nmain : Unit -> Int\nmain () = region<R> r {\nmatch Wrap (Leaf 42) {\nWrap(Leaf(value)) => value\n_ => 0\n}\n}\n"
        ),
        "42"
    );
}

#[test]
fn generic_nullary_and_payload_constructors_keep_their_instantiated_types() {
    assert_eq!(
        run(concat!(
            "type Option<A> =\nNone\n| Some(A)\nmain : Unit -> Int\nmain () = region<R> r {\n",
            "let empty : Option<Int> = None\nlet make = Some\nmatch (empty, make 42) {\n",
            "(None, Some(value)) => value\n_ => 0\n}\n}\n",
        )),
        "42"
    );
}

#[test]
fn a_whole_tuple_cannot_escape_its_declared_region() {
    let failure = run_result("main : Unit -> (Int, Int)\nmain () = region<R> r {\n(20, 22)\n}\n")
        .unwrap_err();
    let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
        panic!("expected the source lifetime diagnostic");
    };
    let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(error)) =
        diagnostic.failure()
    else {
        panic!("expected source resource escape, got {diagnostic:?}");
    };
    assert_eq!(error.reason, ash::elaborate::TypeReason::ResourceEscape);
}

#[test]
fn tuple_fields_resume_in_order_and_are_evaluated_once() {
    assert_eq!(
        run(concat!(
            "import @builtin.generic_cell as Cell\n",
            "effect Yield {\nnext : Int -> Int\n}\n",
            "main : Unit -> Int\nmain () = resource Cell.Cell<R,Int> count = 0 {\n",
            "let pair = handle (\nperform Yield.next 20,\nperform Yield.next 22\n) with Yield {\n",
            "next value => {\nlet previous = Cell.read count\n",
            "let ignored = Cell.write (count, previous + 1)\nresume (value + previous)\n}\n}\n",
            "match pair {\n(left, right) => left + right + Cell.read count\n}\n}\n",
        )),
        "45"
    );
}

#[test]
fn discarding_a_field_continuation_abandons_unrequested_tuple_storage() {
    assert_eq!(
        run(concat!(
            "effect Stop {\nstop : Unit -> Int\n}\n",
            "main : Unit -> Int\nmain () = region<R> owner {\n",
            "handle (match (20, perform Stop.stop ()) {\n(left, right) => left + right\n}) with Stop {\n",
            "stop ignored => {\nlet done = discard\n99\n}\n}\n}\n",
        )),
        "99"
    );
}

#[test]
fn an_outer_cell_cannot_backpatch_a_release_with_its_regions_view() {
    let failure = run_result(concat!(
        "import @builtin.generic_cell as Cell\n",
        "zero : Unit -> Int\nzero () = 0\nmain : Unit -> Unit\n",
        "main () = region<S> outer {\nresource Cell.Cell<C, Unit -> Int> holder = zero {\n",
        "region<R> owner {\nlet capture : Unit -> Int = fn(ignored) {\nusing owner {\n42\n}\n}\n",
        "using outer {\nCell.write (holder, capture)\n}\n}\n}\n}\n",
    ))
    .unwrap_err();
    let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
        panic!("source lifetime rejection")
    };
    let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(error)) =
        diagnostic.failure()
    else {
        panic!("source lifetime rejection: {diagnostic:?}")
    };
    assert_eq!(error.reason, ash::elaborate::TypeReason::ResourceEscape);
}

#[test]
fn owned_byte_payloads_cannot_escape_their_declared_region() {
    for (ty, expression) in [
        ("String", "\"region bytes\""),
        ("Bytes", "Text.to_utf8 \"region bytes\""),
    ] {
        let source = format!(
            "import @builtin.string as Text\nmain : Unit -> {ty}\nmain () = region<R> owner {{\n{expression}\n}}\n"
        );
        let failure = run_result(&source).unwrap_err();
        let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
            panic!("expected source lifetime rejection, got {failure:?}");
        };
        let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(error)) =
            diagnostic.failure()
        else {
            panic!("expected source resource escape, got {diagnostic:?}");
        };
        assert_eq!(error.reason, ash::elaborate::TypeReason::ResourceEscape);
    }
}

#[test]
fn selected_string_and_byte_copies_survive_an_inner_close() {
    assert_eq!(
        run(concat!(
            "import @builtin.string as Text\nimport @builtin.bytes as B\n",
            "make : Unit -> String\nmake () = \"region bytes\"\n",
            "main : Unit -> Int\nmain () = region<R> outer {\n",
            "let kept = region<S> inner {\nusing outer {\nmake ()\n}\n}\n",
            "B.length (Text.to_utf8 kept)\n}\n"
        )),
        "12"
    );
}

#[test]
fn integer_immediate_literal_can_escape_its_region() {
    assert_eq!(
        run("main : Unit -> Int\nmain () = region<R> r {\n42\n}\n"),
        "42"
    );
}

#[test]
fn integer_large_literal_retains_its_region() {
    let failure = run_result(
        "main : Unit -> Int\nmain () = region<R> r {\n340282366920938463463374607431768211456\n}\n",
    )
    .unwrap_err();
    let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
        panic!("expected source lifetime rejection")
    };
    let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(error)) =
        diagnostic.failure()
    else {
        panic!("expected source lifetime rejection: {diagnostic:?}")
    };
    assert_eq!(error.reason, ash::elaborate::TypeReason::ResourceEscape);
}

#[test]
fn integer_local_arithmetic_is_conservatively_resident() {
    let failure =
        run_result("main : Unit -> Int\nmain () = region<R> r {\n20 + 22\n}\n").unwrap_err();
    let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
        panic!("expected source lifetime rejection")
    };
    let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(error)) =
        diagnostic.failure()
    else {
        panic!("expected source lifetime rejection: {diagnostic:?}")
    };
    assert_eq!(error.reason, ash::elaborate::TypeReason::ResourceEscape);
}

#[test]
fn integer_arithmetic_can_select_the_surviving_outer_region() {
    assert_eq!(
        run(
            "main : Unit -> Int\nmain () = region<R> outer {\nlet result = region<S> inner {\nusing outer {\n20 + 22\n}\n}\nmatch result == 42 {\ntrue => 42\nfalse => 0\n}\n}\n"
        ),
        "42"
    );
}

#[test]
fn integer_host_backing_preserves_large_literal_and_overflow_results() {
    let expected = "340282366920938463463374607431768211456";
    assert_eq!(
        run("main : Unit -> Int\nmain () = 340282366920938463463374607431768211456\n"),
        expected
    );
    assert_eq!(
        run("main : Unit -> Int\nmain () = 9223372036854775808 * 9223372036854775808 * 4\n"),
        expected
    );
    assert_eq!(
        run("main : Unit -> Int\nmain () = 340282366920938463463374607431768211456 + 1\n"),
        "340282366920938463463374607431768211457"
    );
}

#[test]
fn integer_known_call_and_projection_preserve_immediate_independence() {
    assert_eq!(
        run(
            "identity : Int -> Int\nidentity value = value\nmain : Unit -> Int\nmain () = region<R> r {\nmatch (42, 0) {\n(value, ignored) => identity value\n}\n}\n"
        ),
        "42"
    );
}

#[test]
fn integer_legacy_cell_read_preserves_stored_immediate_facts() {
    assert_eq!(
        run(
            "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource cell<C> cell = 41 {\nCell.read cell\n}\n"
        ),
        "41"
    );
}

#[test]
fn integer_legacy_cell_read_preserves_older_digit_backing() {
    assert_eq!(
        run(
            "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = {\nlet original = 340282366920938463463374607431768211456\nresource cell<C> cell = original {\nCell.read cell\n}\n}\n"
        ),
        "340282366920938463463374607431768211456"
    );
}

#[test]
fn integer_legacy_cell_rejects_younger_digit_backpatch() {
    let failure = run_result("import @builtin.cell as Cell\nmain : Unit -> Unit\nmain () = resource cell<C> cell = 0 {\nregion<R> local {\nCell.write (cell, 340282366920938463463374607431768211456)\n}\n}\n").unwrap_err();
    let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
        panic!("expected source lifetime rejection")
    };
    let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(error)) =
        diagnostic.failure()
    else {
        panic!("expected source lifetime rejection: {diagnostic:?}")
    };
    assert_eq!(error.reason, ash::elaborate::TypeReason::ResourceEscape);
}

#[test]
fn integer_binary_operands_resume_once_in_source_order() {
    assert_eq!(
        run(
            "import @builtin.cell as Cell\neffect Tick {\nnext : Int -> Int\n}\nmain : Unit -> Int\nmain () = resource cell<C> steps = 0 {\nlet value = handle (perform Tick.next 1) * (perform Tick.next 2) with Tick {\nnext tag => {\nlet _ = Cell.write (steps, (Cell.read steps) * 10 + tag)\nresume 18446744073709551616\n}\n}\nmatch value == 340282366920938463463374607431768211456 {\ntrue => match (Cell.read steps) == 12 {\ntrue => 42\nfalse => 0\n}\nfalse => 0\n}\n}\n"
        ),
        "42"
    );
}

#[test]
fn integer_handled_request_result_preserves_digit_residency() {
    let failure = run_result("effect Read {\nget : Unit -> Int\n}\nmain : Unit -> Int\nmain () = region<R> r {\nhandle perform Read.get () with Read {\nget ignored => resume 340282366920938463463374607431768211456\n}\n}\n").unwrap_err();
    let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
        panic!("expected source lifetime rejection")
    };
    let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(error)) =
        diagnostic.failure()
    else {
        panic!("expected source lifetime rejection: {diagnostic:?}")
    };
    assert_eq!(error.reason, ash::elaborate::TypeReason::ResourceEscape);
}

#[test]
fn integer_imported_summaries_preserve_actual_residency() {
    let directory = std::env::temp_dir().join(format!(
        "ash-int-summary-{}-{}",
        std::process::id(),
        NEXT_SOURCE.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    fs::write(directory.join("values.ash"), "pub identity : Int -> Int\nidentity value = value\npub large : Unit -> Int\nlarge () = 340282366920938463463374607431768211456\n").unwrap();
    for (body, accepted) in [("Values.identity 42", true), ("Values.large ()", false)] {
        let entry = directory.join("entry.ash");
        fs::write(&entry,format!("import values as Values\nmain : Unit -> Int\nmain () = region<R> r {{\n{body}\n}}\n")).unwrap();
        let result = run_path(RunConfiguration {
            entry,
            roots: ModuleRoots::empty(),
        });
        if accepted {
            assert_eq!(result.unwrap().value_display(), "42");
        } else {
            let ash::driver::FileFailure::Pipeline(diagnostic) = result.unwrap_err() else {
                panic!("expected source lifetime rejection")
            };
            let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(error)) =
                diagnostic.failure()
            else {
                panic!("expected source lifetime rejection: {diagnostic:?}")
            };
            assert_eq!(error.reason, ash::elaborate::TypeReason::ResourceEscape);
        }
    }
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn polymorphic_closure_views_keep_independent_type_instantiations() {
    assert_eq!(
        run(concat!(
            "main : Unit -> Int\nmain () = {\n",
            "let identity = fn(value) {\nvalue\n}\n",
            "let integer = identity 42\nlet boolean = identity true\n",
            "match boolean {\ntrue => integer\nfalse => 0\n}\n}\n",
        )),
        "42"
    );
}

#[test]
fn polymorphic_closure_aliases_forward_without_changing_sibling_views() {
    assert_eq!(
        run(concat!(
            "main : Unit -> Int\nmain () = {\n",
            "let identity = fn(value) {\nvalue\n}\nlet forwarded = identity\n",
            "let answer = forwarded 42\n",
            "match identity true {\ntrue => answer\nfalse => 0\n}\n}\n",
        )),
        "42"
    );
}

#[test]
fn polymorphic_closure_creation_keeps_its_region_residency() {
    let failure = run_result(concat!(
        "main : Unit -> Int\nmain () = {\nlet escaped = region<R> owner {\n",
        "let identity = fn(value) {\nvalue\n}\nidentity\n}\nescaped 42\n}\n",
    ))
    .unwrap_err();
    let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
        panic!("expected source lifetime rejection, got {failure:?}");
    };
    let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(error)) =
        diagnostic.failure()
    else {
        panic!("expected source resource escape, got {diagnostic:?}");
    };
    assert_eq!(
        error.reason,
        ash::elaborate::TypeReason::ResourceEscape,
        "{diagnostic:?}"
    );
}

#[test]
fn closure_body_fresh_construction_uses_the_callers_selected_region() {
    let failure = run_result(concat!(
        "main : Unit -> Int\nmain () = region<A> outer {\n",
        "let make : Unit -> (Int, Int) = fn(ignored) {\n(20, 22)\n}\n",
        "let pair = region<B> inner {\nmake ()\n}\n",
        "match pair {\n(left, right) => 42\n}\n}\n",
    ))
    .unwrap_err();
    let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
        panic!("expected source lifetime rejection, got {failure:?}");
    };
    let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(error)) =
        diagnostic.failure()
    else {
        panic!("expected source resource escape, got {diagnostic:?}");
    };
    assert_eq!(error.reason, ash::elaborate::TypeReason::ResourceEscape);
}

#[test]
fn closure_body_explicit_selection_keeps_its_captured_region_identity() {
    assert_eq!(
        run(concat!(
            "main : Unit -> Int\nmain () = region<A> outer {\n",
            "let make : Unit -> (Int, Int) = fn(ignored) {\nusing outer {\n(20, 22)\n}\n}\n",
            "let pair = region<B> inner {\nmake ()\n}\n",
            "match pair {\n(left, right) => match (left + right) == 42 {\ntrue => 42\nfalse => 0\n}\n}\n}\n",
        )),
        "42"
    );
}

const SCORE_CAPTURE_DECLARATIONS: &str = concat!(
    "type Option<A> =\nNone\n| Some(A)\n",
    "interface Score<A> {\nscore<X> : (A, X) -> Int\n}\n",
    "impl Score<Int> {\nscore (value, ignored) = value\n}\n",
    "impl Score<Option<A>> where Score<A> {\nscore (None, ignored) = 4\n",
    "score (Some(value), ignored) = {\nlet empty : Option<A> = None\n",
    "score((empty, ignored)) * 10 + score((value, ignored))\n}\n}\n",
);

const SCORE_CAPTURE_OWNER_MAIN: &str = concat!(
    "main : Unit -> Bool\nmain () = region<A> outer {\n",
    "let escaped : Unit -> Int = region<R> inner {\n",
    "let selected : (Option<Int>, Bool) -> Int = score\n",
    "using outer {\nlet wrapper : Unit -> Int = fn(ignored) {\n",
    "selected((Some(2), true))\n}\nwrapper\n}\n}\n(escaped ()) == 42\n}\n",
);

#[test]
fn selected_polymorphic_method_capture_keeps_its_materialization_owner() {
    let source = format!("{SCORE_CAPTURE_DECLARATIONS}{SCORE_CAPTURE_OWNER_MAIN}");
    let failure = run_result(&source).unwrap_err();
    let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
        panic!("expected source lifetime rejection, got {failure:?}");
    };
    let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(error)) =
        diagnostic.failure()
    else {
        panic!("expected source resource escape, got {diagnostic:?}");
    };
    assert_eq!(error.reason, ash::elaborate::TypeReason::ResourceEscape);
}

#[test]
fn selected_polymorphic_method_materialized_in_outer_region_survives_inner_close() {
    let source = format!("{SCORE_CAPTURE_DECLARATIONS}{SCORE_CAPTURE_OWNER_MAIN}");
    let positive = source.replace("= score\n", "= using outer {\nscore\n}\n");
    assert_eq!(run(&positive), "true");
}

fn run_imported_score(
    source: &str,
    through_facade: bool,
) -> Result<ash::driver::Observation, ash::driver::FileFailure> {
    let directory = std::env::temp_dir().join(format!(
        "ash-region-method-{}-{}",
        std::process::id(),
        NEXT_SOURCE.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    let declarations = SCORE_CAPTURE_DECLARATIONS
        .replace("type Option", "pub type Option")
        .replace("interface Score", "pub interface Score")
        .replace("impl Score", "pub impl Score");
    fs::write(directory.join("methods.ash"), declarations).unwrap();
    let entry = directory.join("entry.ash");
    let imports = if through_facade {
        fs::write(
            directory.join("facade.ash"),
            concat!(
                "pub import methods (Option, None, Some)\n",
                "import methods (Score, score)\nimport methods (impl Score)\n",
                "pub pick : Unit -> ((Option<Int>, Bool) -> Int)\npick () = score\n",
            ),
        )
        .unwrap();
        "import facade (Option, None, Some, pick)\n"
    } else {
        "import methods (Option, None, Some, Score, score)\nimport methods (impl Score)\n"
    };
    fs::write(&entry, format!("{imports}{source}")).unwrap();
    let result = run_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    });
    fs::remove_dir_all(directory).unwrap();
    result
}

#[test]
fn imported_selected_method_capture_keeps_its_materialization_owner() {
    let failure = run_imported_score(SCORE_CAPTURE_OWNER_MAIN, false).unwrap_err();
    let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
        panic!("expected imported source lifetime rejection, got {failure:?}");
    };
    let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(error)) =
        diagnostic.failure()
    else {
        panic!("expected imported source escape, got {diagnostic:?}");
    };
    assert_eq!(error.reason, ash::elaborate::TypeReason::ResourceEscape);
}

#[test]
fn imported_selected_method_outer_placement_survives_inner_close() {
    let positive = SCORE_CAPTURE_OWNER_MAIN.replace("= score\n", "= using outer {\nscore\n}\n");
    assert_eq!(
        run_imported_score(&positive, false)
            .unwrap()
            .value_display(),
        "true"
    );
}

#[test]
fn transitive_selected_method_capture_keeps_its_materialization_owner() {
    let source = SCORE_CAPTURE_OWNER_MAIN.replace("= score\n", "= pick(())\n");
    let failure = run_imported_score(&source, true).unwrap_err();
    let ash::driver::FileFailure::Pipeline(diagnostic) = failure else {
        panic!("expected transitive source lifetime rejection, got {failure:?}");
    };
    let ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(error)) =
        diagnostic.failure()
    else {
        panic!("expected transitive source escape, got {diagnostic:?}");
    };
    assert_eq!(error.reason, ash::elaborate::TypeReason::ResourceEscape);
}

#[test]
fn transitive_selected_method_outer_placement_survives_inner_close() {
    let source = SCORE_CAPTURE_OWNER_MAIN.replace("= score\n", "= using outer {\npick(())\n}\n");
    assert_eq!(
        run_imported_score(&source, true).unwrap().value_display(),
        "true"
    );
}
