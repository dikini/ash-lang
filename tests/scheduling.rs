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
fn host_default_allocation_does_not_add_work_to_an_empty_store() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let observation = run_path(RunConfiguration {
        entry: root.join("tests/fixtures/scheduling/empty-host.ash"),
        roots: ModuleRoots::new([("ash", root.join("libraries"))])
            .expect("the shipped library root is valid"),
    })
    .expect("host-default allocation leaves the empty Store ready to close");

    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
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

#[test]
fn draining_the_key_before_release_completes_the_same_branch() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let observation = run_path(RunConfiguration {
        entry: root.join("tests/fixtures/scheduling/restored-key.ash"),
        roots: ModuleRoots::new([("ash", root.join("libraries"))])
            .expect("the shipped library root is valid"),
    })
    .expect("draining the retained branch permits the Store to close");

    assert_eq!(observation.value_display(), "42");
}

#[test]
fn gas_safe_points_commit_accounting_before_the_selected_yield() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let observation = run_path(RunConfiguration {
        entry: root.join("tests/fixtures/scheduling/gas.ash"),
        roots: ModuleRoots::new([("ash", root.join("libraries"))])
            .expect("the shipped library root is valid"),
    })
    .expect("the selected gas yield leaves committed accounting visible");

    assert_eq!(observation.value_display(), "(42, 123456)");
}

#[test]
fn imported_gas_guard_keeps_both_branches_until_the_final_drain() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture = root.join("tests/fixtures/scheduling/imported-guard");
    let observation = run_path(RunConfiguration {
        entry: fixture.join("gas-pq.ash"),
        roots: ModuleRoots::new([("ash", fixture)]).expect("the fixture library root is valid"),
    })
    .expect("the imported gas guard preserves both retained branches");

    assert_eq!(observation.value_display(), "(42, 123456)");
    assert_eq!(observation.type_display(), "(Int, Int)");
}

#[test]
fn imported_gas_guard_allows_one_retained_branch_to_finish() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture = root.join("tests/fixtures/scheduling/imported-guard");
    let observation = run_path(RunConfiguration {
        entry: fixture.join("gas-single.ash"),
        roots: ModuleRoots::new([("ash", fixture)]).expect("the fixture library root is valid"),
    })
    .expect("the imported gas guard preserves a single retained branch");

    assert_eq!(observation.value_display(), "(42, 123456)");
    assert_eq!(observation.type_display(), "(Int, Int)");
}

#[test]
fn checkpoints_before_and_after_resume_keep_the_inner_clause() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let observation = run_path(RunConfiguration {
        entry: root.join("tests/fixtures/scheduling/resume.ash"),
        roots: ModuleRoots::new([("ash", root.join("libraries"))])
            .expect("the shipped library root is valid"),
    })
    .expect("both sides of the inner resume survive suspension");

    assert_eq!(observation.value_display(), "123415678");
}

#[test]
fn repeatedly_suspended_cleanup_returns_the_saved_result_after_other_work() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let observation = run_path(RunConfiguration {
        entry: root.join("tests/fixtures/scheduling/suspended-cleanup.ash"),
        roots: ModuleRoots::new([("ash", root.join("libraries"))])
            .expect("the shipped library root is valid"),
    })
    .expect("the cleanup and its saved result survive suspension");

    assert_eq!(observation.value_display(), "(42, 1234156178)");
}
