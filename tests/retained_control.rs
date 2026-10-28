mod support;

#[test]
fn unused_store_api_does_not_block_an_unrelated_program() {
    let source = concat!(
        "import @builtin.retained_control as Control\n",
        "main : Unit -> Int\nmain () = 42\n",
    );
    let observation = support::run_module("unused-store-api.ash", source)
        .expect("an unused store API has no release obligation");
    assert_eq!(observation.value_display(), "42");
}

#[test]
fn probe_is_an_ordinary_interceptable_request() {
    let source = concat!(
        "import @builtin.retained_control as Control\n",
        "probe<N> : Unit -> Bool ! {Control.Probe<N>}\n",
        "probe ignored = perform Control.Probe<N>.quiescent ()\n",
        "main : Unit -> Bool\n",
        "main () = {\n",
        "let specialized : Unit -> Bool ! {Control.Probe<Int>} = probe\n",
        "handle (specialized ()) with Control.Probe<Int> {\n",
        "quiescent ignored => resume true\n}\n",
        "}\n",
    );
    let observation = support::run_module("intercepted-probe.ash", source)
        .expect("a nearer source handler can intercept the ordinary request");
    assert_eq!(observation.value_display(), "true");
}

#[test]
fn store_probe_is_discharged_without_opening_release() {
    let source = concat!(
        "import @builtin.retained_control as Control\n",
        "main : Unit -> Int\n",
        "main () = resource Control.Store<N,(Unit -> Int)> store = () {\n",
        "let empty = perform Control.Probe<N>.quiescent ()\n",
        "match empty {\ntrue => 42\nfalse => 0\n}\n}\n",
    );
    let failure = support::run_module("store-probe.ash", source)
        .expect_err("the probe does not itself prove public release");
    assert_eq!(
        failure.reason_code(),
        "core.validation.retained-release",
        "{failure:?}"
    );
}

#[test]
fn private_root_without_retain_still_requires_admission() {
    let source = concat!(
        "import @builtin.retained_control as Control\n",
        "effect Checkpoint<N> {\ncheckpoint : Unit -> Unit\n}\n",
        "run<N> : (Control.Store<N,(Unit -> Int)>, Unit) -> Int\n",
        "run (store, ignored) = handle {\n",
        "let _ = perform Checkpoint<N>.checkpoint ()\n42\n",
        "} with Checkpoint<N> using store {\ncheckpoint ignored => resume ()\n}\n",
        "main : Unit -> Int\nmain () = 42\n",
    );
    let failure = support::run_module("root-without-retain.ash", source)
        .expect_err("a private root still requires its admission proof");
    assert_eq!(
        failure.reason_code(),
        "core.validation.retained-release",
        "{failure:?}"
    );
}

#[test]
fn public_option_and_same_spelled_user_constructors_remain_ordinary() {
    let source = concat!(
        "import @builtin.retained_control (Option, None, Some)\n",
        "type Marker = HiddenStore\n",
        "main : Unit -> Int\nmain () = {\n",
        "let marker = HiddenStore\nlet value : Option<Int> = Some(42)\n",
        "match marker {\nHiddenStore => match value {\n",
        "None => 0\nSome(result) => result\n}\n}\n}\n",
    );
    let observation = support::run_module("ordinary-option.ash", source)
        .expect("Option and a user constructor keep ordinary constructor behavior");
    assert_eq!(observation.value_display(), "42");
}

#[test]
fn generic_continue_accepts_a_row_bearing_answer() {
    let source = concat!(
        "import @builtin.retained_control as Control\n",
        "nested<N,E : EffectRow> : ",
        "(Control.Store<N,(Unit -> (Unit -> Int ! {| E}) ! {| E})>, Control.Key<N>) -> ",
        "Control.Option<(Unit -> Int ! {| E})> ! {Control.Drive<N> | E}\n",
        "nested pair = Control.advance pair\n",
        "main : Unit -> Int\nmain () = 42\n",
    );
    let observation = support::run_module("nested-store-answer.ash", source)
        .expect("the answer can carry the descriptor's open row");
    assert_eq!(observation.value_display(), "42");
}

#[test]
fn generic_continue_accepts_a_descriptor_that_already_contains_drive() {
    let source = concat!(
        "import @builtin.retained_control as Control\n",
        "forward<N> : ",
        "(Control.Store<N,(Unit -> Int ! {Control.Drive<N>})>, Control.Key<N>) -> ",
        "Control.Option<Int> ! {Control.Drive<N>}\n",
        "forward pair = Control.advance_with_drive pair\n",
        "main : Unit -> Int\nmain () = 42\n",
    );
    let observation = support::run_module("store-answer-with-drive.ash", source)
        .expect("a closed descriptor row may already contain the store drive");
    assert_eq!(observation.value_display(), "42");
}

#[test]
fn fresh_store_answer_resolves_but_unproved_close_is_rejected() {
    let source = concat!(
        "import @builtin.retained_control as Control\n",
        "type Step<N> =\nDone\n| Waiting(Control.Key<N>)\n",
        "main : Unit -> Int\n",
        "main () = resource Control.Store<N,(Unit -> Step<N>)> store = () {\n",
        "42\n}\n",
    );
    let failure = support::run_module("fresh-store-answer.ash", source)
        .expect_err("C3 has not yet established this public close");
    assert!(
        matches!(&failure, ash::driver::PipelineFailure::Validation(_)),
        "frontend should resolve and elaborate before close admission: {failure:?}"
    );
    assert_eq!(failure.reason_code(), "core.validation.retained-release");
}

#[test]
fn retained_fresh_answer_needs_its_actual_allocator_handler() {
    let source = include_str!("fixtures/retained-drain/fresh-answer.ash");
    let failure = support::run_module("owned-answer-allocator.ash", source)
        .expect_err("the owned handler passes source checks but public release remains closed");
    assert_eq!(failure.reason_code(), "core.validation.retained-release");

    let owned = "                using outer {\n                    let _ = perform Checkpoint<N>.checkpoint ()\n                    Done\n                }";
    let external =
        "                let _ = perform Checkpoint<N>.checkpoint ()\n                Done";
    assert_eq!(source.matches(owned).count(), 1);
    let failure = support::run_module(
        "external-answer-allocator.ash",
        &source.replace(owned, external),
    )
    .expect_err("the cleanup forwarder changes the external allocator handler");
    assert_eq!(failure.reason_code(), "effect.retained-interpretation");
}

#[test]
fn store_descriptor_requires_a_unit_domain_function() {
    for descriptor in ["Int", "(Int -> Int)"] {
        let source = format!(
            "import @builtin.retained_control as Control\n\
             main : Unit -> Int\n\
             main () = resource Control.Store<N,{descriptor}> store = () {{\n42\n}}\n"
        );
        let failure = support::run_module("bad-store-descriptor.ash", &source)
            .expect_err("the descriptor has no Unit-domain function");
        assert_eq!(
            failure.reason_code(),
            "type.store-descriptor",
            "{failure:?}"
        );
    }
}

#[test]
fn store_identity_is_not_visible_in_its_initializer() {
    let source = concat!(
        "import @builtin.retained_control as Control\n",
        "main : Unit -> Int\n",
        "main () = resource Control.Store<N,(Unit -> Int)> store = ({\n",
        "let leaked : Control.Key<N> = ()\n",
        "()\n}) {\n42\n}\n",
    );
    let failure = support::run_module("store-initializer-scope.ash", source)
        .expect_err("the fresh store identity is not in initializer scope");
    assert!(
        matches!(&failure, ash::driver::PipelineFailure::Resolution(_)),
        "identity must fail resolution in the preceding scope: {failure:?}"
    );
}

#[test]
fn store_handle_cannot_escape_the_fresh_identity() {
    let source = concat!(
        "import @builtin.retained_control as Control\n",
        "main : Unit -> Int\n",
        "main () = {\n",
        "let escaped = resource Control.Store<N,(Unit -> Int)> store = () {\nstore\n}\n",
        "42\n}\n",
    );
    let failure = support::run_module("store-escape.ash", source)
        .expect_err("the store handle contains its fresh identity");
    assert_eq!(failure.reason_code(), "type.resource-escape", "{failure:?}");
}

#[test]
fn generic_helper_can_forward_the_structural_continue() {
    let source = concat!(
        "import @builtin.retained_control as Control\n",
        "forward<N,A,E : EffectRow> : ",
        "(Control.Store<N,(Unit -> A ! {| E})>, Control.Key<N>) -> ",
        "Control.Option<A> ! {Control.Drive<N> | E}\n",
        "forward pair = Control.advance pair\n",
        "main : Unit -> Int\n",
        "main () = resource Control.Store<N,(Unit -> Int)> store = () {\n",
        "let relay : (Control.Store<N,(Unit -> Int)>, Control.Key<N>) -> ",
        "Control.Option<Int> ! {Control.Drive<N>} = forward\n",
        "42\n}\n",
    );
    let failure = support::run_module("store-forward.ash", source)
        .expect_err("C3 has not yet established this public close");
    assert_eq!(
        failure.reason_code(),
        "core.validation.retained-release",
        "{failure:?}"
    );
}

#[test]
fn private_checkpoint_clause_can_retain_or_resume_before_its_suffix() {
    let source = concat!(
        "import @builtin.retained_control as Control\n",
        "effect Checkpoint<N> {\ncheckpoint : Unit -> Unit\n}\n",
        "main : Unit -> Int\n",
        "main () = resource Control.Store<N,(Unit -> Int ! {Control.Drive<N>})> store = () {\n",
        "let answer = handle {\nlet _ = perform Checkpoint<N>.checkpoint ()\n7\n}",
        " with Checkpoint<N> using store {\n",
        "checkpoint ignored => match true {\n",
        "true => {\nlet key = retain\n42\n}\n",
        "false => resume ()\n}\n}\n42\n}\n",
    );
    let failure = support::run_module("private-root.ash", source)
        .expect_err("C3 has not yet established this public close");
    assert_eq!(
        failure.reason_code(),
        "core.validation.retained-release",
        "{failure:?}"
    );
}

fn private_root_fixture(reply: &str, branch: &str, clause: &str, store: &str) -> String {
    format!(
        "import @builtin.retained_control as Control\n\
         effect Checkpoint<N> {{\ncheckpoint : Unit -> {reply}\n}}\n\
         main : Unit -> Int\n\
         main () = resource Control.Store<N,(Unit -> Int ! {{Control.Drive<N>}})> store = () {{\n\
         let answer = handle {{\nlet _ = perform Checkpoint<N>.checkpoint ()\n{branch}\n}} \
         with Checkpoint<N> using {store} {{\ncheckpoint ignored => {clause}\n}}\n42\n}}\n"
    )
}

#[test]
fn private_root_checks_store_answer_and_checkpoint_reply() {
    for (reply, branch, clause, store, expected) in [
        (
            "Unit",
            "7",
            "{\nlet key = retain\n42\n}",
            "3",
            "type.store-descriptor",
        ),
        (
            "Unit",
            "()",
            "{\nlet key = retain\n42\n}",
            "store",
            "type.mismatch",
        ),
        (
            "Int",
            "7",
            "{\nlet key = retain\n42\n}",
            "store",
            "effect.retain-reply",
        ),
    ] {
        let source = private_root_fixture(reply, branch, clause, store);
        let failure = support::run_module("private-root-ports.ash", &source)
            .expect_err("the root's actual store and reply ports must agree");
        assert_eq!(failure.reason_code(), expected, "{failure:?}");
    }
}

#[test]
fn private_root_consumes_its_selected_owner_once_without_discard() {
    for (clause, expected) in [
        ("{\nlet _ = discard\n42\n}", "effect.retained-root-discard"),
        (
            "{\nlet key = retain\nlet again = retain\n42\n}",
            "effect.resume-already-consumed",
        ),
        ("42", "effect.resume-not-consumed"),
        (
            "{\nlet later : Unit -> Int ! {Control.Drive<N>} = fn(ignored) {\nlet key = retain\n42\n}\nresume ()\n}",
            "effect.resume-capture",
        ),
    ] {
        let source = private_root_fixture("Unit", "7", clause, "store");
        let failure = support::run_module("private-root-usage.ash", &source)
            .expect_err("the selected owner cannot be lost, discarded, duplicated or captured");
        assert_eq!(failure.reason_code(), expected, "{failure:?}");
    }
}

#[test]
fn private_root_retain_never_searches_past_an_inner_clause() {
    let source = concat!(
        "import @builtin.retained_control as Control\n",
        "effect Checkpoint<N> {\ncheckpoint : Unit -> Unit\n}\n",
        "effect Inner<N> {\ninner : Unit -> Unit\n}\n",
        "main : Unit -> Int\n",
        "main () = resource Control.Store<N,(Unit -> Int ! {Control.Drive<N>})> store = () {\n",
        "handle {\nlet _ = perform Checkpoint<N>.checkpoint ()\n7\n}",
        " with Checkpoint<N> using store {\ncheckpoint ignored => ",
        "handle {\nlet _ = perform Inner<N>.inner ()\n42\n}",
        " with Inner<N> {\ninner ignored => {\nlet key = retain\nresume ()\n}\n}\n}\n}\n",
    );
    let failure = support::run_module("private-root-nearest.ash", source)
        .expect_err("an inner ordinary clause is the nearest selected owner");
    assert_eq!(
        failure.reason_code(),
        "effect.retain-outside-root",
        "{failure:?}"
    );

    let outside = "main : Unit -> Int\nmain () = {\nlet key = retain\n42\n}\n";
    let failure = support::run_module("retain-outside-root.ash", outside)
        .expect_err("retain is unavailable outside a private root");
    assert_eq!(
        failure.reason_code(),
        "effect.retain-outside-root",
        "{failure:?}"
    );
}

#[test]
fn retain_is_a_reserved_source_keyword() {
    let source = "main : Unit -> Int\nmain () = {\nlet retain : Int = 42\nretain\n}\n";
    let failure = support::run_module("retain-keyword.ash", source)
        .expect_err("retain is no longer an identifier");
    assert!(matches!(failure, ash::driver::PipelineFailure::Syntax(_)));
}

#[test]
fn private_root_allows_other_operations_to_resume_non_unit_replies() {
    let source = concat!(
        "import @builtin.retained_control as Control\n",
        "effect Checkpoint<N> {\npause : Unit -> Unit\nask : Unit -> Int\n}\n",
        "main : Unit -> Int\n",
        "main () = resource Control.Store<N,(Unit -> Int ! {Control.Drive<N>})> store = () {\n",
        "handle {\nlet _ = perform Checkpoint<N>.pause ()\n",
        "perform Checkpoint<N>.ask ()\n} with Checkpoint<N> using store {\n",
        "pause ignored => {\nlet key = retain\n42\n}\nask ignored => resume 7\n}\n}\n",
    );
    let failure = support::run_module("private-root-multiple-operations.ash", source)
        .expect_err("C3 has not yet established this public close");
    assert_eq!(
        failure.reason_code(),
        "core.validation.retained-release",
        "{failure:?}"
    );
}

#[test]
fn store_drive_is_row_nameable_but_not_an_ordinary_operation() {
    for body in [
        "perform Control.Drive<N>.internal ()",
        "handle () with Control.Drive<N> {\ninternal ignored => resume ()\n}",
        "hook Control.Drive<N> {\n()\n}",
        "register Control.Drive<N> identity {\n()\n}",
    ] {
        let source = format!(
            "import @builtin.retained_control as Control\n\
             main : Unit -> Int\n\
             main () = resource Control.Store<N,(Unit -> Int)> store = () {{\n\
             let _ = {body}\n42\n}}\n"
        );
        let failure = support::run_module("sealed-drive.ash", &source)
            .expect_err("the internal drive has no ordinary source operation");
        assert_eq!(failure.reason_code(), "resolve.sealed-drive", "{failure:?}");
    }
}

#[test]
fn aliased_drive_cannot_be_performed_or_handled() {
    for body in [
        "perform Run<N>.internal ()",
        "handle () with Run<N> {\ninternal ignored => resume ()\n}",
    ] {
        let source = format!(
            "import @builtin.retained_control (Drive as Run)\n\
             attempt<N> : N -> Int\nattempt ignored = {{\nlet _ = {body}\n42\n}}\n\
             main : Unit -> Int\nmain () = 42\n"
        );
        let failure = support::run_module("sealed-drive-alias.ash", &source)
            .expect_err("aliasing does not expose the internal drive operation");
        assert_eq!(failure.reason_code(), "resolve.sealed-drive", "{failure:?}");
    }
}
