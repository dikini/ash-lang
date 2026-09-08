use ash::{
    core::{
        transform::{fold_effect_literal_primitives, identity_effect_traversal},
        validate_effect_modules,
    },
    elaborate::{EffectElaborator, check_module, link_modules},
    evidence_validation::validate_interface_evidence,
    module::{ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
    source::SourceFile,
};

fn validate_transforms(source: &str, modules: &[(&str, &str)]) {
    let directory = std::env::temp_dir().join(format!(
        "ash-native-core-{}-{}",
        std::process::id(),
        SourceFile::new("native", "").unwrap().id().value()
    ));
    std::fs::create_dir(&directory).unwrap();
    for (name, text) in modules {
        std::fs::write(directory.join(name), text).unwrap();
    }
    let entry = directory.join("entry.ash");
    std::fs::write(&entry, source).unwrap();
    let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    std::fs::remove_dir_all(&directory).unwrap();
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
    let relation = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let program = validate_effect_modules(core, &sources, &relation).unwrap();
    for transformed in [
        identity_effect_traversal(&program),
        fold_effect_literal_primitives(&program),
    ] {
        validate_effect_modules(transformed.unwrap(), &sources, &relation).unwrap();
    }
}

#[test]
fn native_methods_and_nested_results_validate_after_both_transforms() {
    validate_transforms(
        "import @builtin.native_buffer as Buffer\nmain : Unit -> Buffer.Outcome<Buffer.Outcome<Int>>\nmain () = resource native_buffer<R> b = 4 {\nlet size = Buffer.length b\nmatch Buffer.write (b, 0, 42) {\nBuffer.Success(()) => Buffer.read (b, 0)\nBuffer.Failure(error) => Buffer.Failure error\n}\n}\n",
        &[],
    );
}

#[test]
fn facade_helpers_preserve_canonical_operations_with_direct_acquisition_import() {
    validate_transforms(
        "import @builtin.native_buffer as Buffer\nimport facade (size)\nmain : Unit -> Buffer.Outcome<Int>\nmain () = resource native_buffer<R> b = 4 {\nsize b\n}\n",
        &[
            (
                "helper.ash",
                "import @builtin.native_buffer as Buffer\npub size<R> : Buffer.Handle<R> -> Int ! {Buffer.Ops<R>} where Buffer.Provider<R>\nsize b = Buffer.length b\n",
            ),
            ("facade.ash", "pub import helper (size)\n"),
        ],
    );
}

#[test]
fn native_success_projection_keeps_outer_values_usable_inside_their_owner() {
    validate_transforms(
        "import @builtin.cell as Cell\nimport @builtin.native_buffer as Buffer\nmain : Unit -> Int\nmain () = resource cell<S> c = 42 {\nmatch resource native_buffer<R> b = 4 {\nc\n} {\nBuffer.Success(outer) => Cell.read outer\nBuffer.Failure(error) => 0\n}\n}\n",
        &[],
    );
}
