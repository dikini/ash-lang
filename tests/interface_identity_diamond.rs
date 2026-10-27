use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::link_modules,
    evidence_validation::validate_interface_evidence,
    interface::{ImplId, ImplMethodId, InterfaceId, MethodId, RequirementId},
    module::{ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::{BinderId, CheckedModule, ImportedTypeAccess},
    types::NominalTypeId,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct ModuleTree(PathBuf);

impl ModuleTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "ash-interface-identity-diamond-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("interface identity tree should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, text: &str) -> PathBuf {
        let path = self.0.join(relative);
        fs::write(&path, text).expect("fixture module should be writable");
        path
    }
}

impl Drop for ModuleTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[derive(Clone, Copy)]
struct BaseIdentities {
    nominal: NominalTypeId,
    interface: InterfaceId,
    method: MethodId,
    implementation: ImplId,
    implementation_method: ImplMethodId,
    prerequisite: RequirementId,
}

#[derive(Clone, Copy)]
struct ArmIdentities {
    global: BinderId,
    requirement: RequirementId,
}

fn file_name(module: &ash::module::LoadedModule) -> &Path {
    Path::new(module.source().display_path())
        .file_name()
        .expect("fixture module should have a file name")
        .as_ref()
}

fn dependency_exports<'a>(
    module: &'a ash::module::LoadedModule,
    checked: &'a [CheckedModule],
) -> Vec<DependencyExports<'a>> {
    module
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
        .collect()
}

#[test]
fn preserves_all_interface_identity_families_through_dependency_diamond() {
    let tree = ModuleTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import left as Left\n",
            "import right as Right\n",
            "import left (impl Transform)\n",
            "import right (impl Transform)\n",
            "main : Unit -> Unit\n",
            "main () = ()\n",
        ),
    );
    tree.write(
        "base.ash",
        concat!(
            "pub type Wrap<A> = Wrap(A)\n",
            "pub interface Transform<A> {\ntransform<B> : (A, B) -> A\n}\n",
            "pub impl Transform<Wrap<A>> where Transform<A> {\n",
            "transform (value, ignored) = value\n}\n",
        ),
    );
    tree.write(
        "left.ash",
        concat!(
            "import base as Base\n",
            "pub import base (Transform, transform, impl Transform)\n",
            "pub left : A -> A where Base.Transform<A>\n",
            "left value = value\n",
        ),
    );
    tree.write(
        "right.ash",
        concat!(
            "import base as Base\n",
            "pub import base (Transform, transform, impl Transform)\n",
            "pub right : A -> A where Base.Transform<A>\n",
            "right value = value\n",
        ),
    );

    let graph = load_module_graph(&entry, &ModuleRoots::empty()).expect("diamond should load");
    assert_eq!(
        graph
            .modules()
            .iter()
            .filter(|module| {
                Path::new(module.source().display_path()).parent() == Some(tree.0.as_path())
            })
            .map(file_name)
            .collect::<std::collections::HashSet<_>>(),
        ["base.ash", "left.ash", "right.ash", "entry.ash"]
            .map(Path::new)
            .into_iter()
            .collect()
    );
    let base_module = graph
        .modules()
        .iter()
        .find(|module| file_name(module) == Path::new("base.ash"))
        .expect("base module should be present");
    assert_eq!(
        graph
            .modules()
            .iter()
            .flat_map(|module| module.dependencies())
            .filter(|edge| edge.target() == base_module.id())
            .count(),
        4,
        "left and right should each retain name and implementation edges to the shared base",
    );

    let mut checked = Vec::new();
    let mut base: Option<BaseIdentities> = None;
    let mut left: Option<ArmIdentities> = None;
    let mut right: Option<ArmIdentities> = None;

    for module in graph.modules() {
        let dependencies = dependency_exports(module, &checked);
        let resolved =
            resolve_module(module, &dependencies).expect("diamond module should resolve");

        match file_name(module)
            .to_str()
            .expect("fixture name should be UTF-8")
        {
            "base.ash" => {}
            "left.ash" | "right.ash" => {
                let identities = base.expect("base should check before either diamond arm");
                let imported_interface = resolved
                    .imported_facts()
                    .interface(identities.interface)
                    .expect("each arm should directly import the base interface fact");
                assert_eq!(imported_interface.id, identities.interface);
                assert_eq!(imported_interface.methods[0].id, identities.method);
                assert_eq!(imported_interface.methods[0].type_parameters().len(), 1);

                let imported_implementation = resolved
                    .imported_facts()
                    .implementation(identities.implementation)
                    .expect("each arm should directly import the base implementation fact");
                assert_eq!(imported_implementation.id, identities.implementation);
                assert_eq!(
                    imported_implementation.methods[0].id,
                    identities.implementation_method
                );
                assert_eq!(imported_implementation.methods[0].method, identities.method);
                assert_eq!(
                    imported_implementation.prerequisites[0].id,
                    identities.prerequisite
                );
            }
            "entry.ash" => {
                let identities = base.expect("base should check before the entry");
                let left = left.expect("left should check before the entry");
                let right = right.expect("right should check before the entry");
                let implementation = resolved
                    .imported_facts()
                    .implementation(identities.implementation)
                    .expect("the two explicit facade selectors should deduplicate one identity");
                assert_eq!(implementation.id, identities.implementation);
                assert_eq!(
                    implementation.methods[0].id,
                    identities.implementation_method
                );
                assert_ne!(left.global, right.global);
                assert_ne!(left.requirement, right.requirement);
                assert!(resolved.imported_facts().global(left.global).is_some());
                assert!(resolved.imported_facts().global(right.global).is_some());
                let imported_interface = resolved
                    .imported_facts()
                    .interface(identities.interface)
                    .expect("the constrained summaries should retain hidden interface metadata");
                assert_eq!(imported_interface.id, identities.interface);
                assert_eq!(imported_interface.methods[0].id, identities.method);
                assert_eq!(imported_interface.methods[0].type_parameters().len(), 1);
                let imported_nominal = resolved
                    .imported_facts()
                    .nominal(identities.nominal)
                    .expect("identity-only facade closure should retain the implementation head");
                assert_eq!(imported_nominal.access, ImportedTypeAccess::Hidden);
                assert!(imported_nominal.constructors.is_empty());

                for arm in [left, right] {
                    let imported = resolved
                        .imported_facts()
                        .global(arm.global)
                        .expect("entry should directly import each arm's constrained global");
                    let [requirement] = imported.scheme.requirements.as_ref() else {
                        panic!("the imported constrained global should retain one requirement");
                    };
                    assert_eq!(requirement.id, arm.requirement);
                    assert_eq!(requirement.interface(), identities.interface);
                }
            }
            other => assert_ne!(
                Path::new(module.source().display_path()).parent(),
                Some(tree.0.as_path()),
                "unexpected fixture module {other}",
            ),
        }

        let module_checked = ash::elaborate::check_module(resolved)
            .expect("every module in the identity diamond should check");
        match file_name(module)
            .to_str()
            .expect("fixture name should be UTF-8")
        {
            "base.ash" => {
                let own_nominals = module_checked
                    .registry()
                    .nominals()
                    .iter()
                    .filter(|nominal| nominal.id.module() == module.id())
                    .collect::<Vec<_>>();
                let [nominal] = own_nominals.as_slice() else {
                    panic!("base should retain one nominal identity");
                };
                let [interface] = module_checked.interface_facts() else {
                    panic!("base should retain one interface fact");
                };
                let [method] = interface.methods.as_ref() else {
                    panic!("base interface should retain one method fact");
                };
                let [implementation] = module_checked.implementation_facts() else {
                    panic!("base should retain one implementation fact");
                };
                let [implementation_method] = implementation.methods.as_ref() else {
                    panic!("base implementation should retain one method mapping");
                };
                let [prerequisite] = implementation.prerequisites.as_ref() else {
                    panic!("base implementation should retain one prerequisite");
                };
                base = Some(BaseIdentities {
                    nominal: nominal.id,
                    interface: interface.id,
                    method: method.id,
                    implementation: implementation.id,
                    implementation_method: implementation_method.id,
                    prerequisite: prerequisite.id,
                });
            }
            "left.ash" => {
                let [scheme] = module_checked.schemes() else {
                    panic!("left should retain one constrained global");
                };
                let [requirement] = scheme.scheme.requirements.as_ref() else {
                    panic!("left global should retain one requirement");
                };
                left = Some(ArmIdentities {
                    global: scheme.binder,
                    requirement: requirement.id,
                });
            }
            "right.ash" => {
                let [scheme] = module_checked.schemes() else {
                    panic!("right should retain one constrained global");
                };
                let [requirement] = scheme.scheme.requirements.as_ref() else {
                    panic!("right global should retain one requirement");
                };
                right = Some(ArmIdentities {
                    global: scheme.binder,
                    requirement: requirement.id,
                });
            }
            "entry.ash" => {}
            _ => {}
        }
        checked.push(module_checked);
    }

    let linked = link_modules(checked, graph.entry())
        .expect("the generic identity diamond should authenticate while linking");
    let validated = validate_interface_evidence(linked)
        .expect("the generic identity diamond should authenticate before Core");
    assert_eq!(validated.entry(), graph.entry());
}

#[test]
fn determined_implementation_reexport_diamond_deduplicates_one_stable_identity() {
    let tree = ModuleTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import left as Left\n",
            "import right as Right\n",
            "import left (impl Relation)\n",
            "import right (impl Relation)\n",
            "main : Unit -> Unit\n",
            "main () = ()\n",
        ),
    );
    tree.write(
        "base.ash",
        concat!(
            "pub type Wrap<A> = Wrap(A)\n",
            "pub interface Relation<A, B> where A -> B {\n",
            "relate : A -> Int\n",
            "}\n",
            "pub impl<A> Relation<Wrap<A>, A> {\n",
            "relate value = 0\n",
            "}\n",
        ),
    );
    tree.write(
        "left.ash",
        "pub import base (Relation, relate, impl Relation)\n",
    );
    tree.write(
        "right.ash",
        "pub import base (Relation, relate, impl Relation)\n",
    );

    let graph = load_module_graph(&entry, &ModuleRoots::empty()).expect("diamond should load");
    let mut checked = Vec::new();
    let mut implementation = None;
    for module in graph.modules() {
        let dependencies = dependency_exports(module, &checked);
        let resolved = resolve_module(module, &dependencies).expect("diamond should resolve");
        if file_name(module) == Path::new("entry.ash") {
            let implementation = implementation.expect("the base should check first");
            assert!(
                resolved
                    .imported_facts()
                    .implementation(implementation)
                    .is_some(),
                "both routes should retain one implementation fact",
            );
        }
        let module_checked = ash::elaborate::check_module(resolved)
            .expect("the stable implementation identity must not conflict with itself");
        if file_name(module) == Path::new("base.ash") {
            let [fact] = module_checked.implementation_facts() else {
                panic!("the base should retain one implementation fact");
            };
            implementation = Some(fact.id);
        }
        checked.push(module_checked);
    }

    assert_eq!(
        checked
            .iter()
            .filter(|checked| {
                graph.module(checked.module()).is_some_and(|module| {
                    Path::new(module.source().display_path()).parent() == Some(tree.0.as_path())
                })
            })
            .map(|checked| file_name(graph.module(checked.module()).unwrap()))
            .collect::<std::collections::HashSet<_>>(),
        ["base.ash", "left.ash", "right.ash", "entry.ash"]
            .map(Path::new)
            .into_iter()
            .collect()
    );
    let linked = link_modules(checked, graph.entry())
        .expect("the determined stable-identity diamond should link");
    let validated = validate_interface_evidence(linked)
        .expect("the determined stable-identity diamond should authenticate before Core");
    assert_eq!(validated.entry(), graph.entry());
}
