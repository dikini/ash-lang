use ash::{
    core::{
        transform::{fold_effect_literal_primitives, identity_effect_traversal},
        validate_effect_modules,
    },
    elaborate::{EffectElaborator, check_module, link_modules},
    eval::evaluate_effect,
    evidence_validation::validate_interface_evidence,
    module::{ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
    source::SourceFile,
};

fn transformed(source: &str, modules: &[(&str, &str)], expected: &str) {
    let directory = std::env::temp_dir().join(format!(
        "ash-hooks-core-{}-{}",
        std::process::id(),
        SourceFile::new("hook", "").unwrap().id().value()
    ));
    std::fs::create_dir(&directory).unwrap();
    for (name, text) in modules {
        std::fs::write(directory.join(name), text).unwrap();
    }
    let entry = directory.join("entry.ash");
    std::fs::write(&entry, source).unwrap();
    let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    std::fs::remove_dir_all(directory).unwrap();
    let mut checked: Vec<CheckedModule> = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                DependencyExports::new(
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
        checked.push(check_module(resolve_module(module, &dependencies).unwrap()).unwrap());
    }
    let linked =
        validate_interface_evidence(link_modules(checked, graph.entry()).unwrap()).unwrap();
    let mut elaborator = EffectElaborator::for_module_program(&linked).unwrap();
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .unwrap();
    let core = elaborator.finish(typed.node).unwrap();
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let relations = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let mut program = validate_effect_modules(core, &sources, &relations).unwrap();
    for pass in 0..3 {
        if pass > 0 {
            let core = if pass == 1 {
                identity_effect_traversal(&program)
            } else {
                fold_effect_literal_primitives(&program)
            }
            .unwrap();
            program = validate_effect_modules(core, &sources, &relations).unwrap();
        }
        assert_eq!(
            evaluate_effect(&program).unwrap().value.to_string(),
            expected
        );
    }
}

#[test]
fn identity_and_folding_preserve_unused_roots_and_enclosing_resume() {
    transformed(
        "effect Adjust {\npublish : Int -> Int\n}\nmain : Unit -> Bool\nmain () = hook Adjust {\ntrue\n}\n",
        &[],
        "true",
    );
    transformed(
        "effect Adjust {\npublish : Int -> Int\n}\neffect Ask {\nask : Unit -> Int\n}\nmain : Unit -> Int\nmain () = handle (perform Ask.ask ()) with Ask {\nask ignored => hook Adjust {\nresume (40 + 2)\n}\n}\n",
        &[],
        "42",
    );
}

#[test]
fn facade_generic_api_keeps_exact_root_and_request_instantiation() {
    for (argument, expected) in [("()", "3"), ("true", "13")] {
        transformed(
            &format!(
                "import facade (Mark, probe)\nmain : Unit -> Int\nmain () = handle (probe ((), {argument})) with Mark<Unit> {{\npublish input => resume (input + 10)\n}}\n"
            ),
            &[
                (
                    "api.ash",
                    "pub effect Mark<T> {\npublish : Int -> Int\n}\npub probe<T, U> : (T, U) -> Int ! {Mark<T>}\nprobe (first, second) = hook Mark<U> {\nperform Mark<T>.publish 3\n}\n",
                ),
                ("facade.ash", "pub import api (Mark, probe)\n"),
            ],
            expected,
        );
    }
}

#[test]
fn root_preserves_live_resource_function_payloads_through_transforms() {
    transformed(
        "import @builtin.cell as Cell\neffect Adjust {\npublish : (Unit -> Int) -> (Unit -> Int)\n}\nmain : Unit -> Int\nmain () = resource cell<R> c = 42 {\nlet get : Unit -> Int = fn(ignored) {\nhandle (Cell.read c) with Cell.Ops<R> {\nread value => resume 42\nwrite value => resume ()\n}\n}\nlet restored = hook Adjust {\nperform Adjust.publish get\n}\nrestored ()\n}\n",
        &[],
        "42",
    );
}

#[test]
fn imported_open_lacks_helper_preserves_its_least_root_row_after_transforms() {
    transformed(
        "import helper (Adjust, relay)\nconstant : Unit -> Int\nconstant () = 42\nmain : Unit -> Int\nmain () = hook Adjust {\nrelay constant\n}\n",
        &[(
            "helper.ash",
            "pub effect Adjust {\npublish : Int -> Int\n}\npub relay<R : EffectRow> : (Unit -> Int ! {| R}) -> Int ! {Adjust | R}\nrelay action = hook Adjust {\naction ()\n}\n",
        )],
        "42",
    );
}
