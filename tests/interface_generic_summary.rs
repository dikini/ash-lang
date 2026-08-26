use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::check_module,
    interface::{ImplId, ImplMethodId, InterfaceId, MethodId, RequirementOwner},
    module::{LoadedModule, ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    types::{Kind, NominalTypeId, Type, TypeVariableId},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct ModuleTree(PathBuf);

impl ModuleTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "ash-interface-generic-summary-{}-{id}",
                std::process::id()
            ));
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

fn load(tree: &ModuleTree, entry: &str, dependency: &str) -> ModuleGraph {
    let entry = tree.write("entry.ash", entry);
    tree.write("dependency.ash", dependency);
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

fn assert_option_of_parameter(ty: &Type, option: NominalTypeId, parameter: TypeVariableId) {
    let Type::Application(function, argument) = ty else {
        panic!("expected an applied Option type, found {ty:?}");
    };
    let Type::Nominal(actual_option) = function.as_ref() else {
        panic!("expected the Option nominal head");
    };
    let Type::Variable(actual_parameter) = argument.as_ref() else {
        panic!("expected Option to contain its implementation parameter once");
    };

    assert_eq!(*actual_option, option);
    assert_eq!(*actual_parameter, parameter);
}

#[test]
fn generic_checked_summary_binds_every_retained_parameter_occurrence() {
    let tree = ModuleTree::create();
    let graph = load(
        &tree,
        "import dependency as Dependency\nimport dependency (impl Equal)\n",
        concat!(
            "pub type Option<A> =\n",
            "    None\n",
            "    | Some(A)\n",
            "pub interface Equal<A> {\n",
            "equal : (A, A) -> Bool\n",
            "}\n",
            "pub impl Equal<Option<A>> where Equal<A> {\n",
            "equal pair = false\n",
            "}\n",
        ),
    );
    let dependency = module_named(&graph, "dependency.ash");
    let dependency_checked = check_module(
        resolve_module(dependency, &[]).expect("the dependency should resolve before its importer"),
    )
    .expect("the generic implementation should check");
    let [defining_interface] = dependency_checked.interface_facts() else {
        panic!("the dependency should retain one checked interface fact");
    };
    let [defining_implementation] = dependency_checked.implementation_facts() else {
        panic!("the dependency should retain one checked implementation fact");
    };
    let entry = module_named(&graph, "entry.ash");
    let dependencies = entry
        .dependencies()
        .iter()
        .map(|edge| {
            DependencyExports::new(edge, dependency_checked.exports())
                .expect("the checked summary should authenticate each direct edge")
        })
        .collect::<Vec<_>>();
    let resolved_entry = resolve_module(entry, &dependencies)
        .expect("the explicit selector should retain the checked implementation fact");
    let imported = resolved_entry
        .imported_facts()
        .implementation(defining_implementation.id)
        .expect("the imported facts should contain the public implementation");

    let expected_option = NominalTypeId::new(dependency.id(), 0);
    let expected_interface = InterfaceId::new(dependency.id(), 0);
    let expected_impl = ImplId::new(dependency.id(), 0);
    let expected_method = MethodId::new(expected_interface, 0);
    let expected_impl_method = ImplMethodId::new(expected_impl, expected_method);
    assert_eq!(defining_interface.id, expected_interface);
    assert_eq!(defining_implementation.id, expected_impl);
    assert_eq!(imported.id, defining_implementation.id);
    assert_eq!(imported.interface, expected_interface);

    let [head_parameter] = imported.head_parameters.as_ref() else {
        panic!("the generic implementation should bind one head parameter");
    };
    let parameter = head_parameter.id;
    assert_option_of_parameter(imported.argument(), expected_option, parameter);

    let [prerequisite] = imported.prerequisites.as_ref() else {
        panic!("the implementation should retain one prerequisite");
    };
    assert_eq!(
        prerequisite.id.owner(),
        RequirementOwner::Impl(expected_impl)
    );
    assert_eq!(prerequisite.id.declaration(), 0);
    assert_eq!(prerequisite.interface, expected_interface);
    assert_eq!(prerequisite.argument(), &Type::Variable(parameter));

    let [method] = imported.methods.as_ref() else {
        panic!("the implementation should retain one checked method scheme");
    };
    assert_eq!(method.id, expected_impl_method);
    assert_eq!(method.id, defining_implementation.methods[0].id);
    assert_eq!(method.method, expected_method);
    assert_eq!(method.method, defining_implementation.methods[0].method);
    assert_eq!(
        method.scheme.type_parameters.as_ref(),
        &[(parameter, Kind::Type)]
    );

    let [method_requirement] = method.scheme.requirements.as_ref() else {
        panic!("the implementation method scheme should retain its prerequisite");
    };
    assert_eq!(method_requirement.id, prerequisite.id);
    assert_eq!(method_requirement.interface, prerequisite.interface);
    assert_eq!(method_requirement.argument(), &Type::Variable(parameter));

    let Type::Function(domain, codomain) = method.scheme.value_type() else {
        panic!("the retained implementation method should have a function type");
    };
    let Type::Tuple(elements) = domain.as_ref() else {
        panic!("Equal.equal should retain its pair domain");
    };
    let [left, right] = elements.as_ref() else {
        panic!("Equal.equal should retain both pair components");
    };
    assert_option_of_parameter(left, expected_option, parameter);
    assert_option_of_parameter(right, expected_option, parameter);
    assert_eq!(codomain.as_ref(), &Type::Bool);
}
