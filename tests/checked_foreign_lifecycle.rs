//! Static checked-owner lifecycle correspondence; no native execution.

#[test]
fn checked_owner_lifecycle_source_fixture_loads() {
    let entry = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/checked-owner-lifecycle/owner.ash");
    let graph = ash::module::load_module_graph(&entry, &ash::module::ModuleRoots::empty())
        .expect("the canonical checked_scope source fixture must parse and project");
    let source = graph.module(graph.entry()).unwrap();
    assert_eq!(source.surface().source_resources.len(), 1);
    assert_eq!(source.surface().foreign_libraries.len(), 1);
}

#[test]
fn checked_owner_lifecycle_source_checks_under_exact_host() {
    let entry = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/checked-owner-lifecycle/owner.ash");
    let graph = ash::module::load_module_graph(&entry, &ash::module::ModuleRoots::empty())
        .expect("the checked lifecycle fixture must load before source admission");
    let mut checked: Vec<ash::resolved::CheckedModule> = Vec::new();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                let producer = checked
                    .iter()
                    .find(|module| module.module() == edge.target())
                    .unwrap();
                ash::resolve::DependencyExports::new(edge, producer.exports()).unwrap()
            })
            .collect::<Vec<_>>();
        let resolved = ash::resolve::resolve_checked_foreign_module(loaded, &dependencies).expect(
            "exact checked owner/resource originals must resolve before lifecycle checking",
        );
        checked.push(
            ash::elaborate::check_module(resolved)
                .expect("canonical checked owner lifecycle must pass source phase checking"),
        );
    }
    assert_eq!(checked.len(), graph.modules().len());
}
