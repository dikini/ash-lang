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
