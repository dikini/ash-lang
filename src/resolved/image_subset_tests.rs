use super::*;

fn foreign_registry() -> ResolvedRegistry {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-image-subset-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let entry = directory.join("entry.ash");
    std::fs::write(
        &entry,
        "import @builtin.foreign as Foreign\nmain : Unit -> Int\nmain () = 42\n",
    )
    .unwrap();
    let graph =
        crate::module::load_module_graph(&entry, &crate::module::ModuleRoots::empty()).unwrap();
    std::fs::remove_dir_all(directory).unwrap();
    // Image admission consumes checked, linked schemes. A raw resolved
    // registry has the global variables but has not retained their scheme rows.
    let mut checked: Vec<CheckedModule> = Vec::new();
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
        let resolved =
            crate::resolve::resolve_checked_foreign_module(loaded, &dependencies).unwrap();
        checked.push(crate::elaborate::check_module(resolved).unwrap());
    }
    let linked = crate::elaborate::link_modules(checked, graph.entry()).unwrap();
    let registry = linked.registry().as_ref().clone();
    assert_eq!(registry.type_variables.len(), 31);
    assert_eq!(registry.global_parameter_rows.len(), 11);
    assert_eq!(
        registry
            .global_parameter_rows
            .iter()
            .map(|row| row.parameters.len())
            .sum::<usize>(),
        17
    );
    registry
}

#[test]
fn checked_builtin_image_subset_preserves_exact_metadata_and_work_limit() {
    let registry = foreign_registry();
    let mut measured = TypeWorkBudget::unbounded();
    assert!(registry.monomorphic_image_subset(&mut measured).unwrap());
    let required = measured.used();
    assert!(
        registry
            .monomorphic_image_subset(&mut TypeWorkBudget::with_limit(required))
            .unwrap()
    );
    assert!(matches!(
        registry.monomorphic_image_subset(&mut TypeWorkBudget::with_limit(required - 1)),
        Err(ResolvedBuildFailure::TypeResource)
    ));
    assert!(
        registry
            .monomorphic_image_subset(&mut TypeWorkBudget::with_limit(required))
            .unwrap()
    );
}

#[test]
fn checked_builtin_image_subset_refuses_altered_roles_and_mirrors() {
    let original = foreign_registry();
    assert!(
        original
            .monomorphic_image_subset(&mut TypeWorkBudget::unbounded())
            .unwrap()
    );
    let mutations: &[fn(&mut ResolvedRegistry)] = &[
        |registry| registry.effects[0].public = false,
        |registry| registry.effects[0].parameters[0].kind = Kind::EffectRow,
        |registry| registry.effect_positions.clear(),
        |registry| registry.owner_signatures.effect_positions.clear(),
        |registry| registry.owner_signatures.effects[0].parameters = Box::new([]),
        |registry| registry.owner_definition_positions.clear(),
        |registry| {
            registry.owner_definitions[0].family =
                Some(NominalTypeId::new(registry.effects[0].id.module(), 0))
        },
        |registry| {
            registry.owner_definitions.pop();
        },
        |registry| {
            let module = registry.effects[0].id.module();
            registry
                .nominal_parameters
                .get_mut(&NominalTypeId::new(module, 14))
                .unwrap()
                .swap(0, 1);
        },
        |registry| {
            let module = registry.effects[0].id.module();
            registry
                .nominal_parameters
                .insert(NominalTypeId::new(module, 18), Box::new([]));
        },
        |registry| {
            registry
                .constructors
                .iter_mut()
                .find(|constructor| {
                    constructor.owner.declaration() == 12
                        && constructor.id == ConstructorId::new(constructor.owner, 2)
                })
                .unwrap()
                .payload = Some(Type::Int);
        },
    ];
    for (index, mutate) in mutations.iter().enumerate() {
        let mut registry = original.clone();
        mutate(&mut registry);
        assert!(
            !matches!(
                registry.monomorphic_image_subset(&mut TypeWorkBudget::unbounded()),
                Ok(true)
            ),
            "accepted altered metadata {index}"
        );
    }
}
