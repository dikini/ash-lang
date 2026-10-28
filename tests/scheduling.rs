use std::path::Path;

use ash::{
    driver::{RunConfiguration, run_path},
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
