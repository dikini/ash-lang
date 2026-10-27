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
