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

fn constructor_payload_original() -> (
    crate::core::UnvalidatedEffectProgram,
    crate::module::ModuleGraph,
) {
    // Ordinary nominal declarations are file-wide. Put Leaf last so removing
    // it cannot fail just because a later retained ordinal leaves a gap.
    let source = format!(
        "{}\ntype Leaf = Leaf(Int)\nmain : Unit -> Foreign.CheckedCall<Int>\nmain () = inspect (make 7)\n",
        include_str!("../../../tests/fixtures/checked-constructor-closure/producer.ash")
            .replace("type Leaf = Leaf(Int)\n", "")
    );
    super::foreign_host_tests::original(&source)
}

#[test]
fn checked_constructor_closure_core_independently_rejects_missing_final_leaf() {
    let (program, graph) = constructor_payload_original();
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
    let leaf = changed
        .registry
        .nominals()
        .iter()
        .find(|fact| fact.id.module() == graph.entry() && fact.spelling == "Leaf")
        .unwrap()
        .id;
    assert!(
        changed
            .registry
            .nominals()
            .iter()
            .filter(|fact| fact.id.module() == graph.entry() && fact.id != leaf)
            .all(|fact| fact.id.declaration() < leaf.declaration())
    );
    assert!(
        std::sync::Arc::make_mut(&mut changed.registry).erase_nominal_for_closure_core_test(leaf)
    );
    let error = crate::core::validate_effect_modules(changed, &sources, &modules).unwrap_err();
    assert_ne!(error.reason(), crate::core::ValidationReason::Resource);
}

#[test]
fn checked_constructor_closure_core_independently_rejects_coherent_payload_donor() {
    let (program, graph) = constructor_payload_original();
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
    let identity = |name: &str| {
        changed
            .registry
            .nominals()
            .iter()
            .find(|fact| fact.id.module() == graph.entry() && fact.spelling == name)
            .unwrap()
            .id
    };
    let (envelope, leaf, donor) = (identity("Envelope"), identity("Leaf"), identity("Donor"));
    assert!(
        std::sync::Arc::make_mut(&mut changed.registry)
            .replace_constructor_payload_for_closure_core_test(
                crate::types::ConstructorId::new(envelope, 0),
                leaf,
                donor
            )
    );
    let error = crate::core::validate_effect_modules(changed, &sources, &modules).unwrap_err();
    assert_ne!(error.reason(), crate::core::ValidationReason::Resource);
}
