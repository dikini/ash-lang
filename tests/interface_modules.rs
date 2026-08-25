use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::{TypeError, check_module},
    interface::{InterfaceReason, MethodId, RequirementOwner},
    module::{LoadedModule, ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, ResolveReason, resolve_module},
    resolved::{CheckedModule, ResolvedDefinitionKind, ResolvedExprKind, ResolvedTermName},
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
            return resolved.expect_err("the entry fixture should fail resolution");
        }
        checked.push(
            check_module(resolved.expect("a dependency fixture should resolve"))
                .expect("a dependency fixture should check"),
        );
    }
    panic!("the graph should contain its entry module")
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

    assert_eq!(requirement.interface.id, interface.id);
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
    let error = resolve_module(entry, &dependencies)
        .expect_err("a private qualified interface should remain unavailable");

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
    let error = resolve_module(entry, &dependencies)
        .expect_err("a private qualified method should remain unavailable");

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

    let error = resolve_module(entry, &dependencies)
        .expect_err("hidden interface shape must not create a targeted source binding");
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
    let ash::types::Type::Nominal(hidden) = implementation.argument else {
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

    assert!(resolved.imported_facts().nominal(hidden).is_some());
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

    let error = resolve_module(entry, &dependencies)
        .expect_err("hidden impl-head names must not become targeted exports");
    assert_eq!(error.reason, ResolveReason::UnavailableExport);
}

#[test]
fn public_impls_are_not_reexported_through_an_intermediary() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        concat!(
            "import middle as Middle\n",
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
                "import implementation as Implementation\npub import implementation (impl Equal)\n",
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
                resolved.imported_facts().implementation(id).is_none(),
                "the public selector should not publish an imported implementation summary"
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

        let error = resolve_module(entry, &dependencies)
            .expect_err("the imported opaque constructor should remain inaccessible");
        assert_eq!(
            error.reason,
            ResolveReason::OpaqueConstructor,
            "unexpected rejection for opaque {denied_form}",
        );
    }
}
