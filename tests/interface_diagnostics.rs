use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    diagnostic::{Diagnostic, SourceLabel},
    elaborate::{TypeError, check_module},
    interface::InterfaceReason,
    module::{LoadedModule, ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
    source::{SourceFile, Span},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct ModuleTree(PathBuf);

impl ModuleTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "ash-interface-diagnostics-{}-{id}",
                std::process::id()
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("diagnostic fixture directory should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, text: &str) -> PathBuf {
        let path = self.0.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("fixture parent should be creatable");
        }
        fs::write(&path, text).expect("diagnostic fixture should be writable");
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
        .expect("the diagnostic fixture module should be loaded")
}

fn check_graph(graph: &ModuleGraph) -> Result<Vec<CheckedModule>, TypeError> {
    let mut checked = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|checked: &&CheckedModule| checked.module() == edge.target())
                    .expect("dependencies should check before their importers");
                DependencyExports::new(edge, dependency.exports())
                    .expect("the dependency summary should authenticate its import edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies)
            .expect("the diagnostic fixture should resolve before checking");
        checked.push(check_module(resolved)?);
    }
    Ok(checked)
}

fn interface_diagnostic(error: TypeError) -> Box<Diagnostic<InterfaceReason>> {
    match error {
        TypeError::Interface(diagnostic) => diagnostic,
        other => panic!("the fixture should retain an interface diagnostic: {other:?}"),
    }
}

fn exact_span(source: &SourceFile, needle: &str) -> (u32, u32) {
    let start = source
        .text()
        .find(needle)
        .unwrap_or_else(|| panic!("{needle:?} should occur in the fixture source"));
    let end = start + needle.len();
    (
        u32::try_from(start).expect("fixture offset should fit the source model"),
        u32::try_from(end).expect("fixture offset should fit the source model"),
    )
}

fn span_matches(span: Span, source: &SourceFile, needle: &str) -> bool {
    let (start, end) = exact_span(source, needle);
    span.source() == source.id() && span.range().start() == start && span.range().end() == end
}

fn span_matches_last(span: Span, source: &SourceFile, needle: &str) -> bool {
    let start = source
        .text()
        .rfind(needle)
        .unwrap_or_else(|| panic!("{needle:?} should occur in the fixture source"));
    let end = start + needle.len();
    span.source() == source.id()
        && span.range().start() == u32::try_from(start).expect("fixture offset should fit")
        && span.range().end() == u32::try_from(end).expect("fixture offset should fit")
}

fn label_index(labels: &[SourceLabel], source: &SourceFile, needle: &str) -> usize {
    labels
        .iter()
        .position(|label| span_matches(label.span(), source, needle))
        .unwrap_or_else(|| panic!("a related label should identify {needle:?}"))
}

fn assert_no_label_overlaps(labels: &[SourceLabel], source: &SourceFile, needle: &str) {
    let (start, end) = exact_span(source, needle);
    assert!(labels.iter().all(|label| {
        let span = label.span();
        span.source() != source.id() || span.range().end() <= start || end <= span.range().start()
    }));
}

#[test]
fn imported_method_failure_relates_public_cause_without_leaking_private_impl() {
    let tree = ModuleTree::create();
    let entry_text = concat!(
        "import dependency as Dependency\n\n",
        "main : Unit -> Int\n",
        "main () = Dependency.render(42)\n",
    );
    let dependency_text = concat!(
        "pub interface Render<A> {\n",
        "render : A -> Int\n",
        "}\n\n",
        "impl Render<Int> {\n",
        "render value = value\n",
        "}\n",
    );
    let entry = tree.write("entry.ash", entry_text);
    tree.write("dependency.ash", dependency_text);
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the private-implementation fixture should load");

    let diagnostic = interface_diagnostic(
        check_graph(&graph).expect_err("a private dependency implementation is unavailable"),
    );
    let entry = module_named(&graph, "entry.ash").source();
    let dependency = module_named(&graph, "dependency.ash").source();

    assert_eq!(diagnostic.reason, InterfaceReason::Unsatisfied);
    assert!(span_matches(
        diagnostic.primary.span(),
        entry,
        "Dependency.render"
    ));
    let declaration = label_index(&diagnostic.related, dependency, "render : A -> Int");
    let import = label_index(
        &diagnostic.related,
        entry,
        "import dependency as Dependency",
    );
    assert!(declaration < import);
    assert_no_label_overlaps(
        &diagnostic.related,
        dependency,
        "impl Render<Int> {\nrender value = value\n}",
    );
    assert!(diagnostic.expected.is_none());
    assert!(diagnostic.found.is_none());
    assert!(diagnostic.help.is_none());
}

#[test]
fn constrained_import_failure_does_not_leak_a_transitive_impl_route() {
    let tree = ModuleTree::create();
    let entry_text = concat!(
        "import middle as Middle\n\n",
        "main : Unit -> Int\n",
        "main () = Middle.apply(42)\n",
    );
    let middle_text = concat!(
        "import base as Base\n\n",
        "pub apply : Int -> Int where Base.Render<Int>\n",
        "apply value = Base.render(value)\n",
    );
    let base_text = concat!(
        "pub interface Render<A> {\n",
        "render : A -> Int\n",
        "}\n\n",
        "pub impl Render<Int> {\n",
        "render value = value\n",
        "}\n",
    );
    let entry = tree.write("entry.ash", entry_text);
    tree.write("middle.ash", middle_text);
    tree.write("base.ash", base_text);
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the transitive-implementation fixture should load");

    let diagnostic = interface_diagnostic(
        check_graph(&graph).expect_err("a transitive implementation is not ambient"),
    );
    let entry = module_named(&graph, "entry.ash").source();
    let middle = module_named(&graph, "middle.ash").source();
    let base = module_named(&graph, "base.ash").source();

    assert_eq!(diagnostic.reason, InterfaceReason::Unsatisfied);
    assert!(span_matches(
        diagnostic.primary.span(),
        entry,
        "Middle.apply"
    ));
    let declaration = label_index(&diagnostic.related, middle, "apply");
    let import = label_index(&diagnostic.related, entry, "import middle as Middle");
    assert!(declaration < import);
    assert_no_label_overlaps(
        &diagnostic.related,
        base,
        "pub impl Render<Int> {\nrender value = value\n}",
    );
    assert_no_label_overlaps(&diagnostic.related, middle, "import base as Base");
    assert!(diagnostic.expected.is_none());
    assert!(diagnostic.found.is_none());
    assert!(diagnostic.help.is_none());
}

#[test]
fn qualified_method_failure_relates_the_import_alias_used_by_the_occurrence() {
    let tree = ModuleTree::create();
    let entry_text = concat!(
        "import dependency as First\n",
        "import dependency as Second\n\n",
        "main : Unit -> Int\n",
        "main () = Second.render(42)\n",
    );
    let dependency_text = concat!("pub interface Render<A> {\n", "render : A -> Int\n", "}\n",);
    let entry = tree.write("entry.ash", entry_text);
    tree.write("dependency.ash", dependency_text);
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the duplicate-qualified-import fixture should load");

    let diagnostic = interface_diagnostic(
        check_graph(&graph).expect_err("the imported interface has no implementation"),
    );
    let entry = module_named(&graph, "entry.ash").source();

    assert_eq!(diagnostic.reason, InterfaceReason::Unsatisfied);
    assert!(span_matches(
        diagnostic.primary.span(),
        entry,
        "Second.render"
    ));
    label_index(&diagnostic.related, entry, "import dependency as Second");
    assert_no_label_overlaps(&diagnostic.related, entry, "import dependency as First");
}

#[test]
fn targeted_global_failure_relates_the_import_binding_used_by_the_occurrence() {
    let tree = ModuleTree::create();
    let entry_text = concat!(
        "import dependency (apply as first_apply)\n",
        "import dependency (apply as second_apply)\n\n",
        "main : Unit -> Int\n",
        "main () = second_apply(42)\n",
    );
    let dependency_text = concat!(
        "pub interface Render<A> {\n",
        "render : A -> Int\n",
        "}\n\n",
        "pub apply : Int -> Int where Render<Int>\n",
        "apply value = render(value)\n",
    );
    let entry = tree.write("entry.ash", entry_text);
    tree.write("dependency.ash", dependency_text);
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the duplicate-targeted-import fixture should load");

    let diagnostic = interface_diagnostic(
        check_graph(&graph).expect_err("the imported constrained global has no evidence"),
    );
    let entry = module_named(&graph, "entry.ash").source();

    assert_eq!(diagnostic.reason, InterfaceReason::Unsatisfied);
    assert!(span_matches_last(
        diagnostic.primary.span(),
        entry,
        "second_apply"
    ));
    label_index(&diagnostic.related, entry, "apply as second_apply");
    assert_no_label_overlaps(&diagnostic.related, entry, "apply as first_apply");
}

#[test]
fn nested_unsatisfied_failure_retains_the_selected_implementation_chain() {
    let tree = ModuleTree::create();
    let entry_text = concat!(
        "import dependency as Dependency\n",
        "import dependency (impl First)\n\n",
        "main : Unit -> Int\n",
        "main () = Dependency.first(1)\n",
    );
    let dependency_text = concat!(
        "pub interface First<A> {\n",
        "first : A -> A\n",
        "}\n\n",
        "pub interface Second<A> {\n",
        "second : A -> A\n",
        "}\n\n",
        "pub impl First<Int> where Second<Int> {\n",
        "first value = value\n",
        "}\n",
    );
    let entry = tree.write("entry.ash", entry_text);
    tree.write("dependency.ash", dependency_text);
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the nested-unsatisfied fixture should load");

    let diagnostic = interface_diagnostic(
        check_graph(&graph).expect_err("the selected implementation prerequisite is unsatisfied"),
    );
    let entry = module_named(&graph, "entry.ash").source();
    let dependency = module_named(&graph, "dependency.ash").source();

    assert_eq!(diagnostic.reason, InterfaceReason::Unsatisfied);
    assert!(span_matches(
        diagnostic.primary.span(),
        entry,
        "Dependency.first"
    ));
    let first_interface = label_index(
        &diagnostic.related,
        dependency,
        "pub interface First<A> {\nfirst : A -> A\n}",
    );
    let implementation_import = diagnostic
        .related
        .iter()
        .position(|label| {
            span_matches(label.span(), entry, "import dependency (impl First)")
                && label.message() == "this import made the selected implementation available"
        })
        .expect("the direct import should authenticate the selected public implementation");
    let first_implementation = label_index(
        &diagnostic.related,
        dependency,
        "pub impl First<Int> where Second<Int> {\nfirst value = value\n}",
    );
    let first_method = label_index(&diagnostic.related, dependency, "first value = value");
    let second_interface = label_index(
        &diagnostic.related,
        dependency,
        "pub interface Second<A> {\nsecond : A -> A\n}",
    );
    assert!(first_interface < implementation_import);
    assert!(implementation_import < first_implementation);
    assert!(first_implementation < first_method);
    assert!(first_method < second_interface);
}

#[test]
fn concrete_prerequisite_cycle_retains_each_selected_implementation_chain() {
    let tree = ModuleTree::create();
    let entry_text = concat!(
        "interface First<A> {\n",
        "first : A -> A\n",
        "}\n\n",
        "interface Second<A> {\n",
        "second : A -> A\n",
        "}\n\n",
        "impl First<Int> where Second<Int> {\n",
        "first value = value\n",
        "}\n\n",
        "impl Second<Int> where First<Int> {\n",
        "second value = value\n",
        "}\n\n",
        "main : Unit -> Int\n",
        "main () = first(1)\n",
    );
    let entry = tree.write("entry.ash", entry_text);
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("the concrete-prerequisite-cycle fixture should load");

    let diagnostic = interface_diagnostic(
        check_graph(&graph).expect_err("the selected implementation prerequisites form a cycle"),
    );
    let entry = module_named(&graph, "entry.ash").source();

    assert_eq!(diagnostic.reason, InterfaceReason::Cycle);
    assert!(span_matches_last(diagnostic.primary.span(), entry, "first"));
    let first_interface = label_index(
        &diagnostic.related,
        entry,
        "interface First<A> {\nfirst : A -> A\n}",
    );
    let first_implementation = label_index(
        &diagnostic.related,
        entry,
        "impl First<Int> where Second<Int> {\nfirst value = value\n}",
    );
    let first_method = label_index(&diagnostic.related, entry, "first value = value");
    let second_interface = label_index(
        &diagnostic.related,
        entry,
        "interface Second<A> {\nsecond : A -> A\n}",
    );
    let second_implementation = label_index(
        &diagnostic.related,
        entry,
        "impl Second<Int> where First<Int> {\nsecond value = value\n}",
    );
    let second_method = label_index(&diagnostic.related, entry, "second value = value");
    assert!(first_interface < first_implementation);
    assert!(first_implementation < first_method);
    assert!(first_method < second_interface);
    assert!(second_interface < second_implementation);
    assert!(second_implementation < second_method);
}
