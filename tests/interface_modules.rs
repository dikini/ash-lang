use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::{TypeError, check_module},
    interface::{InterfaceReason, MethodId, RequirementOwner},
    module::{LoadedModule, ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, ResolveError, ResolveModuleError, ResolveReason, resolve_module},
    resolved::{
        CheckedModule, ImportedTypeAccess, ResolvedDefinitionKind, ResolvedExprKind,
        ResolvedTermName,
    },
    types::Type,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct ModuleTree(PathBuf);

impl ModuleTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-interface-modules-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("interface module tree should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, text: &str) -> PathBuf {
        let path = self.0.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("fixture parent should be creatable");
        }
        fs::write(&path, text).expect("fixture module should be writable");
        path
    }
}

impl Drop for ModuleTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn load(tree: &ModuleTree, entry: &str, dependencies: &[(&str, &str)]) -> ModuleGraph {
    let entry = tree.write("entry.ash", entry);
    for (path, text) in dependencies {
        tree.write(path, text);
    }
    load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture graph should load")
}

fn module_named<'a>(graph: &'a ModuleGraph, file_name: &str) -> &'a LoadedModule {
    graph
        .modules()
        .iter()
        .find(|module| {
            Path::new(module.source().display_path()).file_name() == Some(file_name.as_ref())
        })
        .expect("fixture module should be present")
}

fn check_graph(graph: &ModuleGraph) -> Result<Vec<CheckedModule>, TypeError> {
    let mut checked: Vec<CheckedModule> = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|checked| checked.module() == edge.target())
                    .expect("dependency order should check the target first");
                DependencyExports::new(edge, dependency.exports())
                    .expect("checked summary should authenticate its edge")
            })
            .collect::<Vec<_>>();
        let resolved =
            resolve_module(module, &dependencies).expect("the fixture module should resolve");
        checked.push(check_module(resolved)?);
    }
    Ok(checked)
}

#[test]
fn determined_interface_methods_cross_a_body_free_dependency_summary() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency as Dependency\n",
            "size : Int -> Int where Dependency.Collection<Int, Bool>\n",
            "size value = value\n\n",
            "keep : (Int, Bool) -> Bool where Dependency.Collection<Int, Bool>\n",
            "keep pair = false\n",
        ),
        &[(
            "dependency.ash",
            concat!(
                "pub interface Collection<I, Item> where I -> Item {\n",
                "size : I -> Int\n",
                "keep : (I, Item) -> Item\n",
                "}\n",
            ),
        )],
    );

    let checked = check_graph(&graph)
        .expect("omitted and present dependents should survive body-free summary admission");
    let entry = checked
        .iter()
        .find(|module| module.module() == module_named(&graph, "entry.ash").id())
        .expect("the separately checked dependent should be published");

    assert_eq!(entry.schemes().len(), 2);
    assert!(
        entry
            .schemes()
            .iter()
            .all(|scheme| scheme.scheme.requirements.len() == 1)
    );
}

#[test]
fn hidden_and_opaque_dependents_cross_summaries_without_access_widening() {
    let fixture_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/relational-interfaces/linked-composite");
    let graph = load_module_graph(&fixture_root.join("entry.ash"), &ModuleRoots::empty())
        .expect("the shared relational fixture should load");
    let checked = check_graph(&graph).expect("the shared relational fixture should check");
    let base = checked
        .iter()
        .find(|module| module.module() == module_named(&graph, "base.ash").id())
        .expect("the checked graph should retain the relational base");
    let dependent = |spelling: &str| {
        let scheme = base
            .schemes()
            .iter()
            .find(|scheme| scheme.spelling == spelling)
            .unwrap_or_else(|| panic!("the base should retain {spelling}"));
        let [requirement] = scheme.scheme.requirements.as_ref() else {
            panic!("{spelling} should retain one relational requirement");
        };
        let [
            _,
            _,
            ash::types::KindedArgument::TypeArg(Type::Nominal(dependent)),
        ] = requirement.arguments()
        else {
            panic!("{spelling} should retain one nominal dependent in position three");
        };
        (*dependent, scheme.binder)
    };
    let (hidden, hidden_marker) = dependent("hidden_marker");
    let (twin, twin_marker) = dependent("twin_marker");
    let (opaque, opaque_marker) = dependent("opaque_marker");
    assert_ne!(
        hidden, twin,
        "same-shaped private declarations remain nominally distinct"
    );
    assert_ne!(hidden, opaque);
    assert_ne!(twin, opaque);
    for nominal in [hidden, twin] {
        let nominal = base
            .registry()
            .nominal(nominal)
            .expect("the defining registry should retain the private nominal");
        let [constructor] = nominal.constructors.as_ref() else {
            panic!("each private twin should retain one constructor");
        };
        assert_eq!(
            base.registry()
                .constructor(*constructor)
                .and_then(|constructor| constructor.payload.as_ref()),
            Some(&Type::Int),
            "the private twins should be shape-equal but identity-distinct",
        );
    }

    let entry = module_named(&graph, "entry.ash");
    let dependencies = entry
        .dependencies()
        .iter()
        .map(|edge| {
            let dependency = checked
                .iter()
                .find(|module| module.module() == edge.target())
                .expect("the body-free dependency should already be checked");
            DependencyExports::new(edge, dependency.exports())
                .expect("the entry edge should authenticate its detached summary")
        })
        .collect::<Vec<_>>();
    let resolved_entry = resolve_module(entry, &dependencies)
        .expect("hidden and opaque dependents should cross the entry summaries");
    for (identity, access) in [
        (hidden, ImportedTypeAccess::Hidden),
        (twin, ImportedTypeAccess::Hidden),
        (opaque, ImportedTypeAccess::Opaque),
    ] {
        assert_eq!(
            resolved_entry
                .imported_facts()
                .nominal(identity)
                .map(|fact| fact.access),
            Some(access),
        );
    }
    for (binder, dependent) in [
        (hidden_marker, hidden),
        (twin_marker, twin),
        (opaque_marker, opaque),
    ] {
        let imported = resolved_entry
            .imported_facts()
            .global(binder)
            .expect("the marker scheme should cross both facade summaries");
        let [requirement] = imported.scheme.requirements.as_ref() else {
            panic!("the imported marker should retain one requirement");
        };
        assert_eq!(
            requirement.arguments()[2],
            ash::types::KindedArgument::TypeArg(Type::Nominal(dependent))
        );
    }

    let base_source = fs::read_to_string(fixture_root.join("base.ash"))
        .expect("the shared base fixture should be readable");
    let tree = ModuleTree::create();
    let hidden_graph = load(
        &tree,
        "import base (Hidden)\n",
        &[("base.ash", base_source.as_str())],
    );
    let base_module = module_named(&hidden_graph, "base.ash");
    let base_checked = check_module(
        resolve_module(base_module, &[]).expect("the shared base should resolve independently"),
    )
    .expect("the shared base should check independently");
    let hidden_entry = module_named(&hidden_graph, "entry.ash");
    let hidden_dependencies = hidden_entry
        .dependencies()
        .iter()
        .map(|edge| DependencyExports::new(edge, base_checked.exports()).unwrap())
        .collect::<Vec<_>>();
    let error = expect_resolution_error(
        resolve_module(hidden_entry, &hidden_dependencies)
            .expect_err("the private dependent spelling must remain unavailable"),
    );
    assert_eq!(error.reason, ResolveReason::UnavailableExport);

    for denied in [
        concat!(
            "import base as Base\n",
            "make : Int -> Base.Opaque\n",
            "make value = Base.OpaqueValue(value)\n",
        ),
        concat!(
            "import base as Base\n",
            "read : Base.Opaque -> Int\n",
            "read Base.OpaqueValue(value) = value\n",
        ),
    ] {
        let tree = ModuleTree::create();
        let opaque_graph = load(&tree, denied, &[("base.ash", base_source.as_str())]);
        let base_module = module_named(&opaque_graph, "base.ash");
        let base_checked = check_module(
            resolve_module(base_module, &[]).expect("the shared base should resolve independently"),
        )
        .expect("the shared base should check independently");
        let opaque_entry = module_named(&opaque_graph, "entry.ash");
        let opaque_dependencies = opaque_entry
            .dependencies()
            .iter()
            .map(|edge| DependencyExports::new(edge, base_checked.exports()).unwrap())
            .collect::<Vec<_>>();
        let error = expect_resolution_error(
            resolve_module(opaque_entry, &opaque_dependencies)
                .expect_err("the public opaque dependent constructor must remain inaccessible"),
        );
        assert_eq!(error.reason, ResolveReason::OpaqueConstructor);
    }
}

fn resolve_entry_error(graph: &ModuleGraph) -> ash::resolve::ResolveError {
    let entry = module_named(graph, "entry.ash");
    let mut checked: Vec<CheckedModule> = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|checked| checked.module() == edge.target())
                    .expect("dependency order should check the target first");
                DependencyExports::new(edge, dependency.exports())
                    .expect("checked summary should authenticate its edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies);
        if module.id() == entry.id() {
            return expect_resolution_error(
                resolved.expect_err("the entry fixture should fail resolution"),
            );
        }
        checked.push(
            check_module(resolved.expect("a dependency fixture should resolve"))
                .expect("a dependency fixture should check"),
        );
    }
    panic!("the graph should contain its entry module")
}

fn expect_resolution_error(error: ResolveModuleError) -> ResolveError {
    match error {
        ResolveModuleError::Resolution(error) => error,
        ResolveModuleError::Kind(error) => {
            panic!("resolution fixture unexpectedly reached kind checking: {error:?}")
        }
        ResolveModuleError::Representation(error) => {
            panic!("fixture unexpectedly reached representation checking: {error:?}")
        }
    }
}

#[test]
fn targeted_interface_conflicts_with_same_spelled_local_interface() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency (Shared)\n",
            "interface Shared<A> {\nlocal : A -> A\n}\n",
        ),
        &[(
            "dependency.ash",
            "pub interface Shared<A> {\nshared : A -> A\n}\n",
        )],
    );

    let error = resolve_entry_error(&graph);

    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn targeted_interface_conflicts_with_same_spelled_local_nominal() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        "import dependency (Shared)\ntype Shared = Shared\n",
        &[(
            "dependency.ash",
            "pub interface Shared<A> {\nshared : A -> A\n}\n",
        )],
    );

    let error = resolve_entry_error(&graph);

    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn targeted_method_conflicts_with_same_spelled_local_method() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency (shared)\n",
            "interface Local<A> {\nshared : A -> A\n}\n",
        ),
        &[(
            "dependency.ash",
            "pub interface Shared<A> {\nshared : A -> A\n}\n",
        )],
    );

    let error = resolve_entry_error(&graph);

    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn targeted_method_renamed_uppercase_conflicts_with_same_spelled_local_constructor() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        "import dependency (shared as Shared)\ntype Local = Shared\n",
        &[(
            "dependency.ash",
            "pub interface Shared<A> {\nshared : A -> A\n}\n",
        )],
    );

    let error = resolve_entry_error(&graph);

    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn qualified_public_interface_and_method_keep_their_defining_identities() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency as Dep\n",
            "same : Int -> Int where Dep.Equal<Int>\n",
            "same value = Dep.equal(value)\n",
        ),
        &[(
            "dependency.ash",
            "pub interface Equal<A> {\nequal : A -> A\n}\n",
        )],
    );

    let dependency = module_named(&graph, "dependency.ash");
    let dependency_checked = check_module(
        resolve_module(dependency, &[]).expect("dependency should resolve before the entry"),
    )
    .expect("dependency should check before the entry");
    let entry = module_named(&graph, "entry.ash");
    let dependencies = entry
        .dependencies()
        .iter()
        .map(|edge| {
            DependencyExports::new(edge, dependency_checked.exports())
                .expect("entry edge should authenticate the dependency summary")
        })
        .collect::<Vec<_>>();
    let resolved = resolve_module(entry, &dependencies)
        .expect("qualified public interface and method should resolve");
    let [interface] = dependency_checked.checked_interfaces() else {
        panic!("dependency should retain its checked public interface");
    };
    let ResolvedDefinitionKind::Equational(same) = &resolved.definitions()[0].kind else {
        panic!("entry should retain its same definition");
    };
    let [requirement] = same.interface.requirements.as_ref() else {
        panic!("entry should retain its resolved interface requirement");
    };
    let ResolvedExprKind::Apply(application) = &same.equations[0].body.kind else {
        panic!("same should apply the qualified method");
    };
    let ResolvedExprKind::Occurrence(occurrence) = &application.function.kind else {
        panic!("same should retain the qualified method occurrence");
    };

    assert_eq!(requirement.application.interface.id, interface.id);
    assert_eq!(
        requirement.id.owner(),
        RequirementOwner::Global(same.interface.name.id)
    );
    assert_eq!(
        occurrence.term,
        ResolvedTermName::Method(MethodId::new(interface.id, 0))
    );
}

#[test]
fn targeted_method_import_resolves_without_importing_its_interface_spelling() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        "import dependency (equal)\nprobe : Int -> Int\nprobe value = equal(value)\n",
        &[(
            "dependency.ash",
            "pub interface Equal<A> {\nequal : A -> A\n}\n",
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let dependency_checked = check_module(
        resolve_module(dependency, &[]).expect("dependency should resolve before the entry"),
    )
    .expect("dependency should check before the entry");
    let entry = module_named(&graph, "entry.ash");
    let dependencies = entry
        .dependencies()
        .iter()
        .map(|edge| {
            DependencyExports::new(edge, dependency_checked.exports())
                .expect("entry edge should authenticate the dependency summary")
        })
        .collect::<Vec<_>>();
    let resolved = resolve_module(entry, &dependencies).expect("targeted method should resolve");
    let ResolvedDefinitionKind::Equational(probe) = &resolved.definitions()[0].kind else {
        panic!("entry should retain its probe definition");
    };
    let ResolvedExprKind::Apply(application) = &probe.equations[0].body.kind else {
        panic!("probe should apply the imported method");
    };
    let ResolvedExprKind::Occurrence(occurrence) = &application.function.kind else {
        panic!("probe should retain the imported method occurrence");
    };
    let [interface] = dependency_checked.checked_interfaces() else {
        panic!("dependency should retain its checked interface");
    };
    assert_eq!(
        occurrence.term,
        ResolvedTermName::Method(MethodId::new(interface.id, 0))
    );
}

#[test]
fn targeted_interface_is_usable_in_a_requirement_and_local_nominal_impl() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency (Equal, equal)\n",
            "type Local = Local\n",
            "same : Int -> Int where Equal<Int>\n",
            "same value = value\n",
            "impl Equal<Local> {\nequal value = value\n}\n",
        ),
        &[(
            "dependency.ash",
            "pub interface Equal<A> {\nequal : A -> A\n}\n",
        )],
    );

    let checked = check_graph(&graph).expect("targeted public interface should be usable");
    let entry = checked
        .iter()
        .find(|module| module.module() == module_named(&graph, "entry.ash").id())
        .expect("entry should remain checked");

    assert_eq!(entry.checked_implementations().len(), 1);
    assert_eq!(entry.schemes()[0].scheme.requirements.len(), 1);
}

#[test]
fn targeted_same_spelled_interface_and_constructor_bind_distinct_namespaces() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency (Marker, Same)\n",
            "keep : Int -> Int where Same<Int>\n",
            "keep value = value\n",
            "marker : Unit -> Marker\n",
            "marker () = Same\n",
        ),
        &[(
            "dependency.ash",
            concat!(
                "pub type Marker = Same\n",
                "pub interface Same<A> {\nsame : A -> A\n}\n",
            ),
        )],
    );

    check_graph(&graph)
        .expect("one targeted spelling should bind its interface and constructor namespaces");
}

#[test]
fn private_interface_and_method_are_not_qualified_import_bindings() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency as Dep\n",
            "same : Int -> Int where Dep.Equal<Int>\n",
            "same value = Dep.equal(value)\n",
        ),
        &[(
            "dependency.ash",
            "interface Equal<A> {\nequal : A -> A\n}\n",
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let dependency_checked =
        check_module(resolve_module(dependency, &[]).expect("private dependency should resolve"))
            .expect("private dependency should check");
    let entry = module_named(&graph, "entry.ash");
    let dependencies = entry
        .dependencies()
        .iter()
        .map(|edge| DependencyExports::new(edge, dependency_checked.exports()).unwrap())
        .collect::<Vec<_>>();
    let error = expect_resolution_error(
        resolve_module(entry, &dependencies)
            .expect_err("a private qualified interface should remain unavailable"),
    );

    assert_eq!(error.reason, ResolveReason::UnavailableExport);
}

#[test]
fn private_method_is_not_a_qualified_import_binding() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        "import dependency as Dep\nprobe : Int -> Int\nprobe value = Dep.equal(value)\n",
        &[(
            "dependency.ash",
            "interface Equal<A> {\nequal : A -> A\n}\n",
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let dependency_checked =
        check_module(resolve_module(dependency, &[]).expect("private dependency should resolve"))
            .expect("private dependency should check");
    let entry = module_named(&graph, "entry.ash");
    let dependencies = entry
        .dependencies()
        .iter()
        .map(|edge| DependencyExports::new(edge, dependency_checked.exports()).unwrap())
        .collect::<Vec<_>>();
    let error = expect_resolution_error(
        resolve_module(entry, &dependencies)
            .expect_err("a private qualified method should remain unavailable"),
    );

    assert_eq!(error.reason, ResolveReason::UnavailableExport);
}

#[test]
fn hidden_interface_metadata_in_a_constrained_summary_is_not_reexported() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        "import middle (Render)\n",
        &[
            (
                "middle.ash",
                concat!(
                    "import base as Base\n",
                    "pub apply : Int -> Int where Base.Render<Int>\n",
                    "apply value = Base.render(value)\n",
                ),
            ),
            (
                "base.ash",
                concat!(
                    "pub interface Render<A> {\nrender : A -> Int\n}\n",
                    "pub impl Render<Int> {\nrender value = value\n}\n",
                ),
            ),
        ],
    );
    let entry = module_named(&graph, "entry.ash");
    let mut checked = Vec::new();
    for module in graph
        .modules()
        .iter()
        .filter(|module| module.id() != entry.id())
    {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|checked: &&CheckedModule| checked.module() == edge.target())
                    .expect("dependencies should check before their importers");
                DependencyExports::new(edge, dependency.exports()).unwrap()
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies)
            .expect("the dependency chain should resolve before the entry");
        checked.push(check_module(resolved).expect("the dependency chain should check"));
    }
    let dependencies = entry
        .dependencies()
        .iter()
        .map(|edge| {
            let dependency = checked
                .iter()
                .find(|checked| checked.module() == edge.target())
                .expect("middle should check before the entry");
            DependencyExports::new(edge, dependency.exports()).unwrap()
        })
        .collect::<Vec<_>>();

    let error = expect_resolution_error(
        resolve_module(entry, &dependencies)
            .expect_err("hidden interface shape must not create a targeted source binding"),
    );
    assert_eq!(error.reason, ResolveReason::UnavailableExport);
}

#[test]
fn public_impl_fact_is_available_on_an_explicit_selector_edge() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        "import dependency (marker, impl Equal)\n",
        &[(
            "dependency.ash",
            concat!(
                "pub interface Equal<A> {\nequal : A -> A\n}\n",
                "pub impl Equal<Int> {\nequal value = value\n}\n",
                "pub marker : Unit -> Unit\nmarker value = value\n",
            ),
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let dependency_checked = check_module(
        resolve_module(dependency, &[]).expect("dependency should resolve before the entry"),
    )
    .expect("dependency should check before the entry");
    let [implementation] = dependency_checked.implementation_facts() else {
        panic!("dependency should retain its checked public implementation");
    };
    let entry = module_named(&graph, "entry.ash");
    let dependencies = entry
        .dependencies()
        .iter()
        .map(|edge| DependencyExports::new(edge, dependency_checked.exports()).unwrap())
        .collect::<Vec<_>>();
    let resolved = resolve_module(entry, &dependencies)
        .expect("the explicit selector should retain matching public implementation facts");

    let imported = resolved
        .imported_facts()
        .implementation(implementation.id)
        .expect("the selector edge should retain the implementation fact");
    assert_eq!(imported, implementation);
}

#[test]
fn private_impl_fact_remains_local_to_its_defining_module() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        "import dependency (Equal, equal, impl Equal)\n",
        &[(
            "dependency.ash",
            concat!(
                "pub interface Equal<A> {\nequal : A -> A\n}\n",
                "impl Equal<Int> {\nequal value = value\n}\n",
            ),
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let dependency_checked = check_module(
        resolve_module(dependency, &[]).expect("dependency should resolve before the entry"),
    )
    .expect("dependency should check before the entry");
    let [implementation] = dependency_checked.implementation_facts() else {
        panic!("the dependency should retain its private implementation locally");
    };
    let entry = module_named(&graph, "entry.ash");
    let dependencies = entry
        .dependencies()
        .iter()
        .map(|edge| DependencyExports::new(edge, dependency_checked.exports()).unwrap())
        .collect::<Vec<_>>();
    let resolved = resolve_module(entry, &dependencies)
        .expect("private implementation metadata should not affect name resolution");

    assert!(
        resolved
            .imported_facts()
            .implementation(implementation.id)
            .is_none()
    );
}

#[test]
fn public_impl_retains_its_private_head_identity_as_hidden_metadata() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        "import dependency (Equal, equal, impl Equal)\n",
        &[(
            "dependency.ash",
            concat!(
                "type Hidden = Hidden(Int)\n",
                "pub interface Equal<A> {\nequal : A -> A\n}\n",
                "pub impl Equal<Hidden> {\nequal value = value\n}\n",
            ),
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let dependency_checked = check_module(
        resolve_module(dependency, &[]).expect("dependency should resolve before the entry"),
    )
    .expect("dependency should check before the entry");
    let [implementation] = dependency_checked.implementation_facts() else {
        panic!("the dependency should retain its public implementation");
    };
    let [ash::types::KindedArgument::TypeArg(ash::types::Type::Nominal(hidden))] =
        implementation.arguments()
    else {
        panic!("the implementation head should retain the private nominal identity");
    };
    let entry = module_named(&graph, "entry.ash");
    let dependencies = entry
        .dependencies()
        .iter()
        .map(|edge| DependencyExports::new(edge, dependency_checked.exports()).unwrap())
        .collect::<Vec<_>>();
    let resolved = resolve_module(entry, &dependencies)
        .expect("the private head identity should cross as hidden metadata");

    assert!(resolved.imported_facts().nominal(*hidden).is_some());
}

#[test]
fn private_impl_head_spelling_and_constructor_remain_unavailable() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        "import dependency (impl Equal)\nimport dependency (Hidden)\n",
        &[(
            "dependency.ash",
            concat!(
                "type Hidden = Hidden(Int)\n",
                "pub interface Equal<A> {\nequal : A -> A\n}\n",
                "pub impl Equal<Hidden> {\nequal value = value\n}\n",
            ),
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let dependency_checked = check_module(
        resolve_module(dependency, &[]).expect("dependency should resolve before the entry"),
    )
    .expect("dependency should check before the entry");
    let entry = module_named(&graph, "entry.ash");
    let dependencies = entry
        .dependencies()
        .iter()
        .map(|edge| DependencyExports::new(edge, dependency_checked.exports()).unwrap())
        .collect::<Vec<_>>();

    let error = expect_resolution_error(
        resolve_module(entry, &dependencies)
            .expect_err("hidden impl-head names must not become targeted exports"),
    );
    assert_eq!(error.reason, ResolveReason::UnavailableExport);
}

#[test]
fn public_implementation_selectors_reexport_through_an_intermediary() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import middle as Middle\n",
            "import middle (impl Equal)\n",
            "probe : Int -> Int\n",
            "probe value = value\n",
        ),
        &[
            (
                "implementation.ash",
                concat!(
                    "pub interface Equal<A> {\nequal : A -> A\n}\n",
                    "pub impl Equal<Int> {\nequal value = value\n}\n",
                ),
            ),
            (
                "middle.ash",
                "import implementation as Implementation\npub import implementation (Equal, impl Equal)\n",
            ),
        ],
    );
    let mut checked: Vec<CheckedModule> = Vec::new();
    let mut implementation_id = None;
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|checked| checked.module() == edge.target())
                    .expect("dependency order should check the target first");
                DependencyExports::new(edge, dependency.exports()).unwrap()
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies).expect("module should resolve");
        let file_name = Path::new(module.source().display_path()).file_name();
        if file_name == Some("middle.ash".as_ref()) {
            let id = implementation_id.expect("implementation module should have checked first");
            assert!(
                resolved.imported_facts().implementation(id).is_some(),
                "the public selector should affect the intermediary's environment"
            );
        }
        if file_name == Some("entry.ash".as_ref()) {
            let id = implementation_id.expect("implementation module should have checked first");
            assert!(
                resolved.imported_facts().implementation(id).is_some(),
                "the entry selector should receive the intermediary's authorized implementation"
            );
        }
        let module_checked = check_module(resolved).expect("module should check");
        if file_name == Some("implementation.ash".as_ref()) {
            implementation_id = Some(module_checked.implementation_facts()[0].id);
        }
        checked.push(module_checked);
    }
}

#[test]
fn alternate_direct_routes_to_one_impl_identity_do_not_self_overlap() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        "import dependency (impl Equal)\nimport dependency (impl Equal)\n",
        &[(
            "dependency.ash",
            concat!(
                "pub interface Equal<A> {\nequal : A -> A\n}\n",
                "pub impl Equal<Int> {\nequal value = value\n}\n",
            ),
        )],
    );
    check_graph(&graph).expect("alternate routes to one ImplId should deduplicate before overlap");
}

#[test]
fn imported_and_local_determined_heads_conflict_at_the_first_combiner() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency (Relation, relate, impl Relation)\n",
            "type Local<A> = Local(A)\n",
            "impl Relation<Local<Int>, Bool> {\n",
            "relate value = 0\n",
            "}\n",
        ),
        &[(
            "dependency.ash",
            concat!(
                "pub interface Relation<A, B> where A -> B {\n",
                "relate : A -> Int\n",
                "}\n",
                "pub impl<F : Type -> Type, A> Relation<F<A>, A> {\n",
                "relate value = 0\n",
                "}\n",
            ),
        )],
    );

    let TypeError::Interface(diagnostic) =
        check_graph(&graph).expect_err("the entry first combines the conflicting heads")
    else {
        panic!("the determined pair should use an interface diagnostic");
    };
    assert_eq!(
        diagnostic.reason,
        InterfaceReason::ImplDeterminationConflict
    );
}

#[test]
fn imported_and_local_determined_heads_overlap_at_the_first_combiner() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency (Relation, relate, impl Relation)\n",
            "type Local<A> = Local(A)\n",
            "impl Relation<Local<Int>, Int> {\n",
            "relate value = 0\n",
            "}\n",
        ),
        &[(
            "dependency.ash",
            concat!(
                "pub interface Relation<A, B> where A -> B {\n",
                "relate : A -> Int\n",
                "}\n",
                "pub impl<F : Type -> Type, A> Relation<F<A>, A> {\n",
                "relate value = 0\n",
                "}\n",
            ),
        )],
    );

    let TypeError::Interface(diagnostic) =
        check_graph(&graph).expect_err("the entry first combines the overlapping heads")
    else {
        panic!("the determined pair should use an interface diagnostic");
    };
    assert_eq!(diagnostic.reason, InterfaceReason::ImplOverlap);
}

#[test]
fn rejects_foreign_interface_and_foreign_nominal_impl_as_orphan() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import equality (Equal, equal)\n",
            "import carrier (Carrier)\n",
            "impl Equal<Carrier> {\nequal value = value\n}\n",
        ),
        &[
            (
                "equality.ash",
                "pub interface Equal<A> {\nequal : A -> A\n}\n",
            ),
            ("carrier.ash", "pub type Carrier = Carrier\n"),
        ],
    );

    let TypeError::Interface(diagnostic) =
        check_graph(&graph).expect_err("the entry owns neither side of the implementation")
    else {
        panic!("the foreign implementation should fail at the interface boundary");
    };
    assert_eq!(diagnostic.reason, InterfaceReason::ImplOrphan);
}

#[test]
fn rejects_primitive_impl_for_foreign_interface_as_orphan() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        "import equality (Equal, equal)\nimpl Equal<Int> {\nequal value = value\n}\n",
        &[(
            "equality.ash",
            "pub interface Equal<A> {\nequal : A -> A\n}\n",
        )],
    );

    let TypeError::Interface(diagnostic) =
        check_graph(&graph).expect_err("a primitive type cannot provide local orphan ownership")
    else {
        panic!("the primitive implementation should fail at the interface boundary");
    };
    assert_eq!(diagnostic.reason, InterfaceReason::ImplOrphan);
}

#[test]
fn rejects_external_opaque_constructor_and_pattern_in_impl_body() {
    for (entry, denied_form) in [
        (
            concat!(
                "import token as Dep\n",
                "interface Read<A> {\nread : A -> Int\n}\n",
                "impl Read<Dep.Token> {\nread Dep.Seal(value) = value\n}\n",
            ),
            "pattern",
        ),
        (
            concat!(
                "import token as Dep\n",
                "interface Make<A> {\nmake : Int -> A\n}\n",
                "impl Make<Dep.Token> {\nmake value = Dep.Seal(value)\n}\n",
            ),
            "construction",
        ),
    ] {
        let tree = ModuleTree::create();
        let graph = load(
            &tree,
            entry,
            &[("token.ash", "pub opaque type Token = Seal(Int)\n")],
        );
        let token = module_named(&graph, "token.ash");
        let token_checked = check_module(
            resolve_module(token, &[]).expect("the opaque carrier module should resolve"),
        )
        .expect("the opaque carrier module should check");
        let entry = module_named(&graph, "entry.ash");
        let dependencies = entry
            .dependencies()
            .iter()
            .map(|edge| DependencyExports::new(edge, token_checked.exports()).unwrap())
            .collect::<Vec<_>>();

        let error = expect_resolution_error(
            resolve_module(entry, &dependencies)
                .expect_err("the imported opaque constructor should remain inaccessible"),
        );
        assert_eq!(
            error.reason,
            ResolveReason::OpaqueConstructor,
            "unexpected rejection for opaque {denied_form}",
        );
    }
}
