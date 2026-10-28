use std::path::Path;

use ash::{
    driver::{RunConfiguration, compile_path, run_path},
    module::ModuleRoots,
};

#[test]
fn coroutine_selection_keeps_the_other_branch_until_the_final_drain() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let observation = run_path(RunConfiguration {
        entry: root.join("tests/fixtures/scheduling/coroutine.ash"),
        roots: ModuleRoots::new([("ash", root.join("libraries"))])
            .expect("the shipped library root is valid"),
    })
    .expect("the coroutine program drains its retained work");

    let cost = observation
        .compilation_work()
        .independent_core
        .expect("the public driver records linked Core work");
    eprintln!(
        "coroutine: Core work={}, allowance={:?}",
        cost.used, cost.allowance
    );
    assert_eq!(observation.value_display(), "(42, 123456)");
    assert_eq!(observation.type_display(), "(Int, Int)");
}

#[test]
fn drain_follows_each_new_key_until_the_branch_completes() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let observation = run_path(RunConfiguration {
        entry: root.join("tests/fixtures/scheduling/repeated.ash"),
        roots: ModuleRoots::new([("ash", root.join("libraries"))])
            .expect("the shipped library root is valid"),
    })
    .expect("the drain follows each newly retained generation");

    assert_eq!(observation.value_display(), "1213145");
}

#[test]
fn cooperative_queue_requeues_new_keys_after_other_ready_work() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let observation = run_path(RunConfiguration {
        entry: root.join("tests/fixtures/scheduling/cooperative.ash"),
        roots: ModuleRoots::new([("ash", root.join("libraries"))])
            .expect("the shipped library root is valid"),
    })
    .expect("the queue drains both repeatedly yielding branches");

    let cost = observation
        .compilation_work()
        .independent_core
        .expect("the public driver records linked Core work");
    eprintln!(
        "cooperative: Core work={}, allowance={:?}",
        cost.used, cost.allowance
    );
    assert_eq!(observation.value_display(), "123142567");
}

#[test]
fn an_empty_ready_queue_completes_without_starting_work() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let observation = run_path(RunConfiguration {
        entry: root.join("tests/fixtures/scheduling/empty.ash"),
        roots: ModuleRoots::new([("ash", root.join("libraries"))])
            .expect("the shipped library root is valid"),
    })
    .expect("an empty ready queue has no work to run");

    assert_eq!(observation.value_display(), "42");
}

#[test]
fn losing_a_ready_key_does_not_authorize_store_release() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let Err(failure) = compile_path(RunConfiguration {
        entry: root.join("tests/fixtures/scheduling/lost-key.ash"),
        roots: ModuleRoots::new([("ash", root.join("libraries"))])
            .expect("the shipped library root is valid"),
    }) else {
        panic!("a lost ready key must not discard the stored branch");
    };

    assert_eq!(
        failure.pipeline_failure().unwrap().reason_code(),
        "core.validation.retained-release",
        "{failure:?}"
    );
}
