use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::check_module,
    module::{LoadedModule, ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, ResolveModuleError, ResolveReason, resolve_module},
    resolved::CheckedModule,
    types::{EffectId, Kind, OperationId, Type},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct ModuleTree(PathBuf);

impl ModuleTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-effect-modules-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("effect fixture directory should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, source: &str) -> PathBuf {
        let path = self.0.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("effect fixture parent should be creatable");
        }
        fs::write(&path, source).expect("effect fixture should be writable");
        path
    }
}

impl Drop for ModuleTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn module_named<'a>(graph: &'a ModuleGraph, file_name: &str) -> &'a LoadedModule {
    graph
        .modules()
        .iter()
        .find(|module| {
            Path::new(module.source().display_path()).file_name() == Some(file_name.as_ref())
        })
        .expect("effect fixture module should be present")
}

fn check_graph(graph: &ModuleGraph) -> Vec<CheckedModule> {
    let mut checked = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|dependency: &&CheckedModule| dependency.module() == edge.target())
                    .expect("effect dependencies should check before their importer");
                DependencyExports::new(edge, dependency.exports())
                    .expect("effect dependency summary should authenticate its edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies)
            .expect("the successful effect module fixture should resolve");
        checked.push(check_module(resolved).expect("the successful effect module should check"));
    }
    checked
}

fn resolve_graph_error(graph: &ModuleGraph) -> ResolveModuleError {
    let mut checked = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|dependency: &&CheckedModule| dependency.module() == edge.target())
                    .expect("effect dependencies should precede their importer");
                DependencyExports::new(edge, dependency.exports()).unwrap()
            })
            .collect::<Vec<_>>();
        match resolve_module(module, &dependencies) {
            Ok(resolved) => {
                checked.push(check_module(resolved).expect("dependencies should check"))
            }
            Err(error) => return error,
        }
    }
    panic!("the rejected effect graph unexpectedly resolved")
}

#[test]
fn public_effect_identity_survives_facade_reexport() {
    let tree = ModuleTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import facade (Exchange)\n\n",
            "main : Unit -> Int\n",
            "main () = 42\n",
        ),
    );
    tree.write(
        "api.ash",
        concat!(
            "pub effect Exchange<A : Type> {\n",
            "send : A -> Unit\n",
            "receive : Unit -> A\n",
            "}\n",
        ),
    );
    tree.write("facade.ash", "pub import api (Exchange)\n");

    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the effect facade fixture should load");
    let api = module_named(&graph, "api.ash");
    let facade = module_named(&graph, "facade.ash");
    let entry = module_named(&graph, "entry.ash");
    let checked = check_graph(&graph);
    let api_checked = checked
        .iter()
        .find(|module| module.module() == api.id())
        .expect("the defining effect module should check");
    let facade_checked = checked
        .iter()
        .find(|module| module.module() == facade.id())
        .expect("the effect facade should check");
    let entry_checked = checked
        .iter()
        .find(|module| module.module() == entry.id())
        .expect("the effect importer should check");

    let [effect] = api_checked.effects() else {
        panic!("the defining module should retain one effect")
    };
    let expected_effect = EffectId::new(api.id(), 0);
    assert_eq!(effect.id, expected_effect);
    assert!(effect.public);
    assert_eq!(effect.parameters.len(), 1);
    assert_eq!(effect.parameters[0].kind, Kind::Type);
    assert_eq!(effect.operations.len(), 2);
    assert_eq!(
        effect
            .operations
            .iter()
            .map(|operation| (operation.id, operation.spelling.as_str()))
            .collect::<Vec<_>>(),
        vec![
            (OperationId::new(expected_effect, 0), "send"),
            (OperationId::new(expected_effect, 1), "receive"),
        ]
    );
    let parameter = effect.parameters[0].id;
    assert_eq!(
        effect.operations[0].annotation.ty,
        Type::function(Type::Variable(parameter), Type::Unit)
    );
    assert_eq!(
        effect.operations[1].annotation.ty,
        Type::function(Type::Unit, Type::Variable(parameter))
    );
    assert_eq!(effect.origin.primary_span().source(), api.source().id());

    let facade_export = facade_checked
        .exports()
        .effect("Exchange")
        .expect("the facade should publish the selected effect");
    assert_eq!(facade_export.id, expected_effect);
    assert_eq!(facade_export.operations[0].id, effect.operations[0].id);
    assert_eq!(facade_export.operations[1].id, effect.operations[1].id);
    assert_eq!(facade_export.origin, effect.origin);

    let imported = entry_checked
        .effect(expected_effect)
        .expect("the entry should retain the imported canonical effect fact");
    assert_eq!(imported.id, expected_effect);
    assert_eq!(imported.parameters, effect.parameters);
    assert_eq!(imported.operations, effect.operations);
    assert_eq!(imported.origin, effect.origin);
}

#[test]
fn effect_namespace_privacy_and_diamond_routes_preserve_one_identity() {
    let tree = ModuleTree::create();
    let entry = tree.write(
        "entry.ash",
        "import left as Left\nimport right as Right\n\nmain : Unit -> Int\nmain () = 42\n",
    );
    tree.write(
        "base.ash",
        "pub effect Public {\nping : Unit -> Unit\n}\n\neffect Hidden {\nsecret : Unit -> Unit\n}\n",
    );
    tree.write("left.ash", "pub import base (Public)\n");
    tree.write("right.ash", "pub import base (Public)\n");
    let graph =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("diamond graph should load");
    let base = module_named(&graph, "base.ash");
    let entry_module = module_named(&graph, "entry.ash");
    let checked = check_graph(&graph);
    let entry_checked = checked
        .iter()
        .find(|module| module.module() == entry_module.id())
        .unwrap();
    let identity = EffectId::new(base.id(), 0);
    assert_eq!(entry_checked.effect(identity).unwrap().id, identity);

    let private_tree = ModuleTree::create();
    let private_entry = private_tree.write(
        "entry.ash",
        "import base (Hidden)\n\nmain : Unit -> Int\nmain () = 42\n",
    );
    private_tree.write("base.ash", "effect Hidden {\nsecret : Unit -> Unit\n}\n");
    let private_graph = load_module_graph(&private_entry, &ModuleRoots::empty()).unwrap();
    let ResolveModuleError::Resolution(private_error) = resolve_graph_error(&private_graph) else {
        panic!("private selection should fail in resolution")
    };
    assert_eq!(
        private_error.diagnostic().reason,
        ResolveReason::UnavailableExport
    );

    let conflict_tree = ModuleTree::create();
    let conflict_entry = conflict_tree.write(
        "entry.ash",
        "import base (Public)\n\ntype Public = Local\n\nmain : Unit -> Int\nmain () = 42\n",
    );
    conflict_tree.write("base.ash", "pub effect Public {\nping : Unit -> Unit\n}\n");
    let conflict_graph = load_module_graph(&conflict_entry, &ModuleRoots::empty()).unwrap();
    let ResolveModuleError::Resolution(conflict_error) = resolve_graph_error(&conflict_graph)
    else {
        panic!("shared uppercase collision should fail in resolution")
    };
    assert_eq!(
        conflict_error.diagnostic().reason,
        ResolveReason::ImportConflict
    );
}

#[test]
fn operation_rows_are_rejected_for_public_and_private_effects() {
    for (visibility, spelling) in [("pub ", "Public"), ("", "Private")] {
        let tree = ModuleTree::create();
        let entry = tree.write(
            "entry.ash",
            &format!("{visibility}effect {spelling} {{\nbad : Unit -> Unit ! {{}}\n}}\n"),
        );
        let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
        let ResolveModuleError::Resolution(error) = resolve_graph_error(&graph) else {
            panic!("an explicit operation row should fail during resolution")
        };
        assert_eq!(
            error.diagnostic().reason,
            ResolveReason::EffectOperationShape
        );
    }
}

#[test]
fn local_and_imported_effect_rows_authenticate_effect_arity() {
    let local_tree = ModuleTree::create();
    let local_entry = local_tree.write(
        "entry.ash",
        concat!(
            "effect State<A : Type> {\nget : Unit -> A\n}\n\n",
            "main : Unit -> Unit ! {State}\n",
            "main () = ()\n",
        ),
    );
    let local_graph = load_module_graph(&local_entry, &ModuleRoots::empty()).unwrap();
    assert!(matches!(
        resolve_graph_error(&local_graph),
        ResolveModuleError::Kind(_)
    ));

    let imported_tree = ModuleTree::create();
    let imported_entry = imported_tree.write(
        "entry.ash",
        concat!(
            "import base (State)\n\n",
            "type Box<A> = Boxed(A)\n\n",
            "main : Unit -> Unit ! {State<Box>}\n",
            "main () = ()\n",
        ),
    );
    imported_tree.write(
        "base.ash",
        "pub effect State<A : Type> {\nget : Unit -> A\n}\n",
    );
    let imported_graph = load_module_graph(&imported_entry, &ModuleRoots::empty()).unwrap();
    assert!(matches!(
        resolve_graph_error(&imported_graph),
        ResolveModuleError::Kind(_)
    ));
}

#[test]
fn hidden_effect_signature_closure_survives_facade_and_diamond_routes() {
    let tree = ModuleTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import left as Left\n",
            "import right as Right\n\n",
            "main : Unit -> Unit\n",
            "main () = ()\n",
        ),
    );
    tree.write(
        "base.ash",
        concat!(
            "effect Hidden {\nping : Unit -> Unit\n}\n\n",
            "pub type Exposed = Wrap (Unit -> Unit ! {Hidden})\n",
        ),
    );
    tree.write("facade.ash", "pub import base (Exposed, Wrap)\n");
    tree.write("left.ash", "pub import facade (Exposed, Wrap)\n");
    tree.write("right.ash", "pub import facade (Exposed, Wrap)\n");

    let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    let base = module_named(&graph, "base.ash");
    let entry = module_named(&graph, "entry.ash");
    let checked = check_graph(&graph);
    let hidden = EffectId::new(base.id(), 0);
    for module in &checked {
        assert!(module.exports().effect("Hidden").is_none());
        if module.module() != entry.id() {
            assert_eq!(
                module
                    .exports()
                    .effect_by_id(hidden)
                    .unwrap_or_else(|| panic!(
                        "module {:?} lost the hidden effect",
                        module.module()
                    ))
                    .id,
                hidden
            );
        }
    }
    assert_eq!(
        checked
            .iter()
            .find(|module| module.module() == entry.id())
            .unwrap()
            .effect(hidden)
            .unwrap()
            .id,
        hidden
    );
}
