use super::*;

#[test]
fn checked_host_resolution_has_exact_one_short_and_fresh_work_boundaries() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-host-resolution-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let entry = directory.join("entry.ash");
    std::fs::write(&entry, "import @builtin.foreign as Foreign\nmain : Unit -> Int\nmain () = foreign host H {\n    42\n}\n").unwrap();
    let graph =
        crate::module::load_module_graph(&entry, &crate::module::ModuleRoots::empty()).unwrap();
    std::fs::remove_dir_all(directory).unwrap();
    let builtin = graph
        .modules()
        .iter()
        .find(|module| module.id().is_builtin_foreign())
        .unwrap();
    let checked =
        crate::elaborate::check_module(resolve_checked_foreign_module(builtin, &[]).unwrap())
            .unwrap();
    let loaded = graph.module(graph.entry()).unwrap();
    let dependencies = loaded
        .dependencies()
        .iter()
        .map(|edge| DependencyExports::new(edge, checked.exports()).unwrap())
        .collect::<Vec<_>>();
    let run = |limit| {
        let mut work = TypeWorkBudget::with_limit(limit);
        let result = resolve_module_for_foreign_profile(
            loaded,
            &dependencies,
            &mut work,
            &mut InterfaceConstraintBudget::default(),
            None,
            true,
        );
        (result, work.used())
    };
    let (result, required) = run(usize::MAX);
    result.unwrap();
    run(required).0.unwrap();
    let failure = run(required - 1)
        .0
        .expect_err("one-short work cannot publish a checked module");
    assert!(match failure {
        ResolveModuleError::Resolution(error) =>
            error.diagnostic().reason == ResolveReason::TypeResourceExhausted,
        ResolveModuleError::Kind(error) => error.is_resource_exhaustion(),
        _ => false,
    });
    run(required).0.unwrap();
}
