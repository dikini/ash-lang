mod support;

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
