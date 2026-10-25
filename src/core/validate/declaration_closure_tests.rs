//! Independent ordinary declaration metadata checks after source admission.

fn ordinary_original(
    text: &str,
) -> (
    crate::core::UnvalidatedEffectProgram,
    crate::module::ModuleGraph,
) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-core-declaration-closure-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let entry = directory.join("entry.ash");
    std::fs::write(&entry, text).unwrap();
    let graph =
        crate::module::load_module_graph(&entry, &crate::module::ModuleRoots::empty()).unwrap();
    std::fs::remove_dir_all(directory).unwrap();
    let mut checked: Vec<crate::resolved::CheckedModule> = Vec::new();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                crate::resolve::DependencyExports::new(
                    edge,
                    checked
                        .iter()
                        .find(|module| module.module() == edge.target())
                        .unwrap()
                        .exports(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let resolved = crate::resolve::resolve_module(loaded, &dependencies).unwrap();
        checked.push(crate::elaborate::check_module(resolved).unwrap());
    }
    let linked = crate::elaborate::link_modules(checked, graph.entry()).unwrap();
    let linked = crate::evidence_validation::validate_interface_evidence(linked).unwrap();
    let mut elaborator = crate::elaborate::EffectElaborator::for_module_program(&linked).unwrap();
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .unwrap();
    (elaborator.finish(typed.node).unwrap(), graph)
}

#[test]
fn checked_declaration_closure_core_independently_rejects_missing_held_metadata() {
    let source = r"type Held = Held(Int)
closed<T> : (T, Int) -> Int
closed (unused, value) = value
pub select : Int -> (Unit -> Int)
select value = {
    let held = Held value
    fn(ignored) {
        match held {
            Held(captured) => closed (held, captured)
        }
    }
}
main : Unit -> Int
main () = {
    let call = select 7
    call ()
}
";
    let (program, graph) = ordinary_original(source);
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
    let source = r"type Donor = Donor(Int)
type Spare = Spare(Int)
pub type Envelope = Envelope(Leaf)
pub type Witness = Witness(Donor)
closed : Int -> Int
closed value = value
pub make : Int -> Envelope
make value = Envelope (Leaf value)
pub inspect : Envelope -> Int
inspect envelope = match envelope {
    Envelope(Leaf(value)) => closed value
}
type Leaf = Leaf(Int)
main : Unit -> Int
main () = inspect (make 7)
";
    ordinary_original(source)
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
