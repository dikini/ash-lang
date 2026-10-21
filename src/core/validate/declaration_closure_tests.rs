#[test]
fn checked_declaration_closure_core_independently_rejects_missing_held_metadata() {
    let source = format!(
        "{}\nmain : Unit -> Foreign.CheckedCall<Int>\nmain () = {{\n    let call = select 7\n    call ()\n}}\n",
        include_str!("../../../tests/fixtures/checked-declaration-closure/global.ash")
            .replace("type Spare = Spare(Int)\n", "")
    );
    let (program, graph) = super::foreign_host_tests::original(&source);
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let valid = crate::core::validate_effect_modules(program, &sources, &modules).unwrap();
    let mut changed = crate::core::transform::identity_effect_traversal(&valid).unwrap();
    let held = changed
        .registry
        .nominals()
        .iter()
        .find(|fact| fact.id.module() == graph.entry() && fact.spelling == "Held")
        .unwrap()
        .id;
    assert!(
        std::sync::Arc::make_mut(&mut changed.registry).erase_nominal_for_closure_core_test(held)
    );
    let error = crate::core::validate_effect_modules(changed, &sources, &modules).unwrap_err();
    assert_ne!(error.reason(), crate::core::ValidationReason::Resource);
}
