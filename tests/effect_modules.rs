use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::check_module,
    kind::{KindFailure, KindReason},
    module::{LoadedModule, ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, ResolveModuleError, ResolveReason, resolve_module},
    resolved::{CheckedModule, ResolvedDefinitionKind},
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
    try_check_graph(graph).expect("the successful effect module should check")
}

fn assert_unit_entry(entry: &Path) {
    let observation = ash::driver::run_path(ash::driver::RunConfiguration {
        entry: entry.to_owned(),
        roots: ModuleRoots::empty(),
    })
    .expect("owned imported captures should link, validate, and execute");
    assert_eq!(observation.value_display(), "()");
}

fn try_check_graph(graph: &ModuleGraph) -> Result<Vec<CheckedModule>, ash::elaborate::TypeError> {
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
        checked.push(check_module(resolved)?);
    }
    Ok(checked)
}

#[test]
fn registration_factory_dependencies_survive_opaque_facade_exports() {
    let tree = ModuleTree::create();
    tree.write("api.ash", "pub effect Adjust {\npublish : (Unit -> Int) -> (Unit -> Int)\n}\npub opaque type Box<A> = Hidden(A)\npub pack<A> : A -> Box<A>\npack value = Hidden value\npub unpack<A> : Box<A> -> A\nunpack (Hidden value) = value\npub make : (Unit -> Int) -> ((Unit -> Int) -> (Unit -> Int))\nmake saved = fn(previous) {\nsaved\n}\n");
    tree.write(
        "facade.ash",
        "pub import api (Adjust, make, Box, pack, unpack)\n",
    );
    for (result, accepted) in [("restored ()", true), ("restored", false)] {
        let output = if accepted { "Int" } else { "(Unit -> Int)" };
        let entry = tree.write("entry.ash", &format!("import @builtin.cell as Cell\nimport facade (Adjust, make, pack, unpack)\nconstant : Unit -> Int\nconstant ignored = 1\nmain : Unit -> {output}\nmain () = resource cell<R> c = 42 {{\nlet saved : Unit -> Int = fn(ignored) {{\nlet held = c\n42\n}}\nhook Adjust {{\nlet callback = unpack (pack (make saved))\nlet restored = register Adjust callback {{\nperform Adjust.publish constant\n}}\n{result}\n}}\n}}\n"));
        let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
        let result = try_check_graph(&graph);
        if accepted {
            result.unwrap();
        } else {
            assert!(format!("{:?}", result.unwrap_err()).contains("ResourceEscape"));
        }
    }
}

#[test]
fn imported_registration_is_closed_inside_the_selected_capture() {
    let tree = ModuleTree::create();
    tree.write("helper.ash", "pub effect Adjust {\npublish : Int -> Int\n}\npub effect Stop {\nstop : Unit -> Unit\n}\nidentity : Int -> Int\nidentity value = value\npub subscribe : (Unit -> Unit ! {Stop}) -> Unit ! {Adjust, Stop}\nsubscribe action = register Adjust identity {\naction ()\n}\n");
    let entry = tree.write("entry.ash", "import helper (Adjust, Stop, subscribe)\naction : Unit -> Unit ! {Stop}\naction ignored = perform Stop.stop ()\nmain : Unit -> Unit\nmain () = handle (hook Adjust {\nsubscribe action\n}) with Stop {\nstop ignored => discard\n}\n");
    let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    check_graph(&graph);
    assert_unit_entry(&entry);
}

#[test]
fn imported_handlers_are_selected_after_type_specialization() {
    let tree = ModuleTree::create();
    tree.write("helper.ash", concat!(
        "pub effect E<T> {\nask : Unit -> Unit\n}\npub effect A {\nask : Unit -> Unit\n}\npub effect B {\nask : Unit -> Unit\n}\n",
        "pub route<T, U> : (T, U) -> Unit ! {A, B, E<T>}\n",
        "route ignored = handle ({\nlet _ = perform E<U>.ask ()\nlet _ = perform A.ask ()\nperform E<T>.ask ()\n}) with E<U> {\n",
        "ask ignored => {\nlet _ = perform B.ask ()\nresume ()\n}\n}\n",
    ));
    for argument in ["(1, true)", "(1, 1)"] {
        let entry = tree.write("entry.ash", &(format!(
            "import helper (E, A, B, route)\ninvoke : Unit -> Unit ! {{A, B}}\ninvoke () = handle (route {argument}) with E<Int> {{\nask ignored => resume ()\n}}\nmain : Unit -> Unit\nmain () = handle (handle (invoke ()) with A {{\n",
        ) + concat!(
            "ask ignored => handle ({\nlet _ = resume ()\nperform B.ask ()\n}) with B {\nask ignored => discard\n}\n",
            "}) with B {\nask ignored => resume ()\n}\n",
        )));
        let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
        check_graph(&graph);
        assert_unit_entry(&entry);
    }
}

#[test]
fn imported_residual_graphs_preserve_live_and_completed_clause_owners() {
    let tree = ModuleTree::create();
    for clause in [
        "let _ = perform A.ask ()\nlet _ = perform B.ask ()\nresume ()",
        "let _ = perform A.ask ()\nlet _ = resume ()\nperform B.ask ()",
        "let _ = perform B.ask ()\nlet _ = resume ()\nperform A.ask ()",
    ] {
        tree.write("helper.ash", &format!(
            "pub effect A {{\nask : Unit -> Unit\n}}\npub effect B {{\nask : Unit -> Unit\n}}\neffect C {{\nask : Unit -> Unit\n}}\n\
             pub ask : Unit -> Unit ! {{A, B}}\nask () = handle (perform C.ask ()) with C {{\nask ignored => {{\n{clause}\n}}\n}}\n"
        ));
        tree.write("facade.ash", "pub import helper (A, B, ask)\n");
        let entry = tree.write("entry.ash", concat!(
            "import facade (A, B, ask)\nmain : Unit -> Unit\nmain () = handle (handle (ask ()) with A {\n",
            "ask ignored => handle ({\nlet _ = resume ()\nperform B.ask ()\n}) with B {\nask ignored => discard\n}\n",
            "}) with B {\nask ignored => resume ()\n}\n",
        ));
        let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
        check_graph(&graph);
        assert_unit_entry(&entry);
    }
}

#[test]
fn imported_residual_returns_continue_into_the_callers_suffix() {
    let tree = ModuleTree::create();
    tree.write("helper.ash", "pub effect A {\nask : Unit -> Unit\n}\npub ask : Unit -> Unit ! {A}\nask () = perform A.ask ()\n");
    for tail in [
        "let _ = perform B.ask ()\nresume ()",
        "let _ = resume ()\nperform B.ask ()",
    ] {
        let entry = tree.write("entry.ash", &format!(
            "import helper (A, ask)\neffect B {{\nask : Unit -> Unit\n}}\neffect C {{\nask : Unit -> Unit\n}}\n\
             main : Unit -> Unit\nmain () = handle (handle (handle (perform C.ask ()) with C {{\nask ignored => {{\nlet _ = ask ()\n{tail}\n}}\n\
             }}) with A {{\nask ignored => handle ({{\nlet _ = resume ()\nperform B.ask ()\n}}) with B {{\nask ignored => discard\n}}\n}}) with B {{\nask ignored => resume ()\n}}\n"
        ));
        let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
        check_graph(&graph);
        assert_unit_entry(&entry);
    }
}

#[test]
fn discard_summary_survives_import_and_facade_reexport() {
    let tree = ModuleTree::create();
    tree.write("helper.ash", concat!(
        "pub effect B {\nask : Unit -> Unit\n}\n",
        "pub ask : Unit -> Unit ! {B}\nask () = perform B.ask ()\n",
        "pub factory : Unit -> (Unit -> Unit ! {B})\nfactory () = fn(ignored) {\nperform B.ask ()\n}\n",
    ));
    tree.write("facade.ash", "pub import helper (B, ask, factory)\n");
    for helper in ["ask ()", "{\nlet request = factory ()\nrequest ()\n}"] {
        let entry = tree.write("entry.ash", &format!(
            "import facade (B, ask, factory)\nmain : Unit -> Unit\nmain () = handle ({helper}) with B {{\nask ignored => discard\n}}\n"
        ));
        let graph = load_module_graph(&entry, &ModuleRoots::empty()).expect("capture imports load");
        check_graph(&graph);
    }
}

#[test]
fn capture_summaries_cover_helpers_importing_only_effect_declarations() {
    let tree = ModuleTree::create();
    tree.write("effects.ash", "pub effect B {\nask : Unit -> Unit\n}\n");
    tree.write(
        "helpers.ash",
        concat!(
            "import effects (B)\n",
            "pub ask : Unit -> Unit ! {B}\nask () = perform B.ask ()\n",
            "effect A {\nask : Unit -> Unit\n}\n",
            "pub bad : Unit -> Unit ! {B}\nbad () = handle (perform A.ask ()) with A {\n",
            "ask ignored => {\nlet _ = perform B.ask ()\nresume ()\n}\n}\n",
        ),
    );
    for callee in ["ask", "bad"] {
        let entry = tree.write("entry.ash", &format!(
            "import effects (B)\nimport helpers (ask, bad)\nmain : Unit -> Unit\nmain () = handle ({callee} ()) with B {{\nask ignored => discard\n}}\n"
        ));
        let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
        check_graph(&graph);
        assert_unit_entry(&entry);
    }
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
fn inline_result_rows_survive_resolution_and_checking() {
    let tree = ModuleTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "effect State<A : Type> {\n",
            "get : Unit -> A\n",
            "}\n\n",
            "fn explicit(value : Int) -> Int ! {State<Int>} {\nvalue\n}\n\n",
            "fn pure(value : Int) -> Int {\nvalue\n}\n",
        ),
    );

    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the inline result-row fixture should load");
    let module = module_named(&graph, "entry.ash");
    let checked = check_graph(&graph);
    let checked = checked
        .iter()
        .find(|checked| checked.module() == module.id())
        .expect("the inline result-row fixture should check");
    let [explicit, pure] = checked.definitions() else {
        panic!("the fixture should retain both inline globals")
    };
    let ResolvedDefinitionKind::InlineOperational(explicit) = explicit.kind() else {
        panic!("the explicit-row global should remain inline operational")
    };
    let ResolvedDefinitionKind::InlineOperational(pure) = pure.kind() else {
        panic!("the pure global should remain inline operational")
    };

    let [instance] = explicit.header.result_effects.known() else {
        panic!("the explicit result should retain exactly one effect")
    };
    assert_eq!(instance.effect(), EffectId::new(module.id(), 0));
    assert_eq!(
        instance.arguments(),
        &[ash::types::KindedArgument::TypeArg(Type::Int)]
    );
    assert!(explicit.header.result_effects.tail().is_none());
    assert!(pure.header.result_effects.is_empty());
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

    for definition in [
        "main : Unit -> Unit ! {State<Box>}\nmain () = ()\n",
        "fn main(value : Unit) -> Unit ! {State<Box>} {\nvalue\n}\n",
    ] {
        let imported_tree = ModuleTree::create();
        let imported_entry = imported_tree.write(
            "entry.ash",
            &format!("import base (State)\n\ntype Box<A> = Boxed(A)\n\n{definition}"),
        );
        imported_tree.write(
            "base.ash",
            "pub effect State<A : Type> {\nget : Unit -> A\n}\n",
        );
        let imported_graph = load_module_graph(&imported_entry, &ModuleRoots::empty()).unwrap();
        let ResolveModuleError::Kind(KindFailure::Source(error)) =
            resolve_graph_error(&imported_graph)
        else {
            panic!("the effect argument should retain a source kind rejection: {definition}")
        };
        assert_eq!(error.reason, KindReason::Argument, "{definition}");
        let source = module_named(&imported_graph, "entry.ash").source();
        let start = source
            .text()
            .find("Box>}")
            .expect("the malformed effect argument should be present");
        assert_eq!(error.primary.span().range().start(), start as u32);
        assert_eq!(
            error.primary.span().range().end(),
            (start + "Box".len()) as u32
        );
    }
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
