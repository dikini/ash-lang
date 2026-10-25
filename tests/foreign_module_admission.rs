//! Ordinary facade effect-signature closure, hidden kinds and source privacy.
use ash::{
    elaborate::check_module,
    module::{ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

static IDS: AtomicU64 = AtomicU64::new(0);
struct Tree(PathBuf);
impl Tree {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "ash-foreign-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }
    fn write(&self, name: &str, text: &str) -> PathBuf {
        let path = self.0.join(name);
        fs::write(&path, text).unwrap();
        path
    }
}
impl Drop for Tree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn check_graph(graph: &ash::module::ModuleGraph) -> Vec<CheckedModule> {
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
        checked.push(
            check_module(resolve_module(module, &dependencies).unwrap())
                .unwrap_or_else(|error| panic!("{}: {error:?}", module.source().display_path())),
        );
    }
    checked
}
const SOURCE: &str = r"type Maybe<A> = None
| Some(A)
type Higher<F : Type -> Type> = Higher(F<Int>)
type Token<R> = HiddenNativeToken(R)
type Fault = Oops
type Start<S, E> = Started(S)
| Denied(E)
type Stop<S, E> = Stopped
| StopFailed(E)
| Kept(S, E)
pub effect Requests<R> {
    begin : Int -> Start<Token<R>, Fault>
    read : Token<R> -> Int
    end : Token<R> -> Stop<Token<R>, Fault>
    higher : Higher<Maybe> -> Higher<Maybe>
}
";

#[test]
fn ordinary_effect_facades_keep_hidden_report_kinds_without_exporting_names() {
    let tree = Tree::new();
    tree.write("native.ash", SOURCE);
    tree.write("facade.ash", "pub import native (Requests)\n");
    let entry = tree.write("entry.ash",
        "import facade as Facade\nprobe : Unit -> Unit ! {Facade.Requests<Int>}\nprobe () = ()\nmain : Unit -> Unit\nmain () = ()\n");
    let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    let checked = check_graph(&graph);
    let module_named = |name: &str| {
        checked
            .iter()
            .find(|module| {
                graph
                    .module(module.module())
                    .unwrap()
                    .source()
                    .display_path()
                    .ends_with(name)
            })
            .unwrap()
    };
    let native = module_named("native.ash");
    let facade = module_named("facade.ash");
    let original = native.exports().effect("Requests").unwrap();
    let forwarded = facade.exports().effect("Requests").unwrap();
    assert_eq!(forwarded.id, original.id);
    assert_eq!(forwarded.operations.len(), original.operations.len());
    for (before, after) in original.operations.iter().zip(&forwarded.operations) {
        assert_eq!(before.id, after.id);
        assert_eq!(before.annotation.ty, after.annotation.ty);
    }
    let consumer = graph.module(graph.entry()).unwrap();
    let dependencies = consumer
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
    let resolved = resolve_module(consumer, &dependencies).unwrap();
    assert_eq!(
        resolved.imported_facts().effect(original.id).unwrap().id,
        original.id
    );
    for spelling in ["Maybe", "Higher", "Token", "Fault", "Start", "Stop"] {
        let nominal = native
            .registry()
            .nominals()
            .iter()
            .find(|nominal| nominal.spelling == spelling)
            .unwrap();
        let parameters = native.registry().nominal_parameters(nominal.id).unwrap();
        let retained = resolved
            .imported_facts()
            .nominal(nominal.id)
            .unwrap_or_else(|| panic!("effect signature closure lost {spelling}"));
        assert_eq!(retained.id, nominal.id);
        assert_eq!(retained.parameter_count, parameters.len());
        assert_eq!(retained.parameters.len(), parameters.len());
        for (before, after) in parameters.iter().zip(&retained.parameters) {
            assert_eq!(before.id, after.id);
            assert_eq!(before.kind, after.kind);
        }
        assert!(
            retained.display_is_private,
            "hidden type {spelling} must remain private"
        );
        if spelling == "Higher" {
            assert_eq!(
                retained.parameters[0].kind,
                ash::types::Kind::Arrow(
                    Box::new(ash::types::Kind::Type),
                    Box::new(ash::types::Kind::Type)
                )
            );
        }
    }
    assert_eq!(
        ash::driver::run_path(ash::driver::RunConfiguration {
            entry,
            roots: ModuleRoots::empty()
        })
        .unwrap()
        .value_display(),
        "()"
    );
}

#[test]
fn effect_signature_closure_does_not_export_hidden_names_or_constructors() {
    let tree = Tree::new();
    tree.write("native.ash", SOURCE);
    tree.write("facade.ash", "pub import native (Requests)\n");
    for name in [
        "Start",
        "Stop",
        "Started",
        "HiddenNativeToken",
        "Token",
        "Fault",
        "Oops",
        "Maybe",
        "Some",
        "Higher",
    ] {
        let entry = tree.write(
            "entry.ash",
            &format!("import facade ({name})\nmain : Unit -> Unit\nmain () = ()\n"),
        );
        let failure = ash::driver::run_path(ash::driver::RunConfiguration {
            entry,
            roots: ModuleRoots::empty(),
        })
        .unwrap_err();
        assert!(
            matches!(failure.pipeline_failure(),
            Some(ash::driver::PipelineFailure::Resolution(error)) if error.reason==ash::resolve::ResolveReason::UnavailableExport),
            "signature metadata must not publish {name}: {failure:?}"
        );
    }
}
