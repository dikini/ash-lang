use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::check_module,
    module::{ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct ModuleTree(PathBuf);

impl ModuleTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path =
                std::env::temp_dir().join(format!("ash-kind-modules-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("kind-module fixture should be creatable: {error}"),
            }
        }
    }

    fn write(&self, name: &str, text: &str) -> PathBuf {
        let path = self.0.join(name);
        fs::write(&path, text).expect("kind-module fixture should be writable");
        path
    }
}

impl Drop for ModuleTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn body_free_summary_supplies_direct_kinds() {
    let tree = ModuleTree::create();
    tree.write(
        "dependency.ash",
        concat!(
            "pub type Option<A> =\nNone\n| Some(A)\n\n",
            "pub type Wrap<F : Type -> Type> = Wrap\n\n",
            "pub interface Consumer<C : (Type -> Type) -> Type> {\n",
            "consume : C<Option> -> Unit\n",
            "}\n\n",
            "pub lift<F : Type -> Type> : F<Int> -> F<Int>\n",
            "lift value = value\n",
            "\n",
            "pub type Holder<F : Type -> Type> = Holder\n\n",
            "pub interface Observe<A> {\n",
            "observe : A -> Bool\n",
            "}\n\n",
            "pub impl<F : Type -> Type> Observe<Holder<F>> {\n",
            "observe value = true\n",
            "}\n",
        ),
    );
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import dependency (Wrap, Consumer, lift, impl Observe)\n",
            "probe : Unit -> Unit where Consumer<Wrap>\n",
            "probe value = value\n",
        ),
    );
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the direct kind fixture should load");
    let dependency = graph
        .modules()
        .iter()
        .find(|module| module.id() != graph.entry())
        .expect("the dependency should load before the entry");
    let dependency = check_module(
        resolve_module(dependency, &[]).expect("the defining module should resolve and kind-check"),
    )
    .expect("the defining module should type-check");
    let entry = graph
        .module(graph.entry())
        .expect("the entry module should remain loaded");
    let dependencies = entry
        .dependencies()
        .iter()
        .map(|edge| DependencyExports::new(edge, dependency.exports()).unwrap())
        .collect::<Vec<_>>();

    let resolved = resolve_module(entry, &dependencies)
        .expect("direct body-free nominal, interface, and scheme kinds should authenticate");
    assert_eq!(resolved.definitions().len(), 1);
    assert!(resolved.interfaces().is_empty());
    assert!(resolved.registry().nominals().is_empty());
}
