//! DN-0036 evidence for complete source owner arguments and imported closure.
use ash::{
    driver::{PipelineFailure, RunConfiguration, run_path},
    elaborate::check_module,
    foreign::{ForeignRegistrations, provider_manifest, sqlite_manifest},
    module::{ForeignRegistrationId, LoadGraphError, ModuleRoots, load_module_graph},
    parser::{ResourceFailure, STRUCTURAL_DEPTH_LIMIT},
    resolve::{DependencyExports, ResolveModuleError, ResolveReason, resolve_module},
    resolved::{CheckedModule, ResolvedDefinitionKind, ResolvedExprKind, ResolvedModule},
    types::{EffectRowVariable, KindedArgument},
};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/provider-experiments/owner-rows")
        .join(name)
}

fn roots() -> ModuleRoots {
    ModuleRoots::empty().with_foreign_registrations(
        ForeignRegistrations::new([
            provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
            sqlite_manifest(ForeignRegistrationId::new(2)).unwrap(),
        ])
        .unwrap(),
    )
}

struct FixtureCopy(PathBuf);
impl FixtureCopy {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-owner-rows-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        fs::create_dir(&path).unwrap();
        for name in ["provider.ash", "library.ash", "entry.ash"] {
            fs::copy(fixture(name), path.join(name)).unwrap();
        }
        Self(path)
    }
    fn replace(&self, name: &str, before: &str, after: &str) {
        let path = self.0.join(name);
        let source = fs::read_to_string(&path).unwrap();
        assert!(
            source.contains(before),
            "fixture mutation must reach its source site"
        );
        fs::write(path, source.replacen(before, after, 1)).unwrap();
    }
    fn resolve_entry(&self, source: &str) -> Result<ResolvedModule, ResolveModuleError> {
        fs::write(self.0.join("entry.ash"), source).unwrap();
        let graph = load_module_graph(&self.0.join("entry.ash"), &roots()).unwrap();
        let mut checked: Vec<CheckedModule> = Vec::new();
        for loaded in graph.modules() {
            let dependencies = loaded
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
            let resolved = resolve_module(loaded, &dependencies)?;
            if loaded.id() == graph.entry() {
                return Ok(resolved);
            }
            checked.push(
                check_module(resolved)
                    .expect("the imported mixed-owner fixture must remain admitted"),
            );
        }
        panic!("the loaded entry must occur in its graph")
    }
    fn run(&self) -> Result<ash::driver::Observation, ash::driver::FileFailure> {
        run_path(RunConfiguration {
            entry: self.0.join("entry.ash"),
            roots: roots(),
        })
    }
}
impl Drop for FixtureCopy {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn mixed_owner_declarations_and_imported_callbacks_check_through_public_driver() {
    let observation = run_path(RunConfiguration {
        entry: fixture("entry.ash"),
        roots: roots(),
    })
    .expect("complete mixed owner arguments and inherited callback rows should check and publish");
    assert_eq!(observation.value_display(), "()");
    assert_eq!(observation.type_display(), "Unit");
}

#[test]
fn targeted_reexport_retains_nested_row_effect_owner_metadata() {
    let observation = run_path(RunConfiguration {
        entry: fixture("nested-entry.ash"),
        roots: roots(),
    })
    .expect("a targeted imported constraint must retain Outer and nested Inner signatures");
    assert_eq!(observation.value_display(), "()");
}

#[test]
fn source_owner_arguments_reject_wrong_tags_kinds_and_saturation() {
    for (name, before, after) in [
        (
            "interface row tag",
            "provider ConnectionProvider<R, {| Rows}>",
            "provider ConnectionProvider<R, Rows>",
        ),
        (
            "resource Type tag",
            "Connection<R, {| Rows}>",
            "Connection<{}, {| Rows}>",
        ),
        (
            "resource saturation",
            "Connection<R, {| Rows}>",
            "Connection<R>",
        ),
        (
            "effect saturation",
            "effect ConnectionOps<R, {| Rows}>",
            "effect ConnectionOps<R>",
        ),
        (
            "interface saturation",
            "provider ConnectionProvider<R, {| Rows}>",
            "provider ConnectionProvider<R>",
        ),
        ("row tail kind", "Rows : EffectRow", "Rows : Type"),
    ] {
        let tree = FixtureCopy::new();
        tree.replace("library.ash", before, after);
        let failure = tree.run().expect_err(name);
        assert!(
            matches!(
                failure.pipeline_failure(),
                Some(
                    PipelineFailure::Resolution(_)
                        | PipelineFailure::Kind(_)
                        | PipelineFailure::Typing(_)
                )
            ),
            "{name} must reach owner checking after parsing: {failure:?}"
        );
        assert!(
            failure.is_source_rejection(),
            "{name} must reject source: {failure:?}"
        );
    }
}

#[test]
fn row_arguments_have_no_standalone_or_ordinary_nominal_type_denotation() {
    for (declaration, standalone_row) in [
        ("pub invalid : {| Rows} -> Unit\ninvalid value = ()\n", true),
        ("pub type Invalid<A : EffectRow> = Invalid(A)\n", false),
        (
            "pub type Box<A> = Box(A)\npub invalid : Box<{}> -> Unit\ninvalid value = ()\n",
            false,
        ),
    ] {
        let tree = FixtureCopy::new();
        tree.replace(
            "entry.ash",
            "main : Unit -> Unit",
            &format!("{declaration}\nmain : Unit -> Unit"),
        );
        let failure = tree
            .run()
            .expect_err("ordinary monotypes cannot absorb row arguments or row-kind arrows");
        if standalone_row {
            assert!(
                matches!(failure.graph_failure(), Some(LoadGraphError::Syntax(_))),
                "a standalone row is outside atomic type syntax: {failure:?}"
            );
        } else {
            assert!(
                matches!(
                    failure.pipeline_failure(),
                    Some(
                        PipelineFailure::Resolution(_)
                            | PipelineFailure::Kind(_)
                            | PipelineFailure::Typing(_)
                    )
                ),
                "ordinary owner rows parse before kind rejection: {failure:?}"
            );
        }
        assert!(failure.is_source_rejection(), "{failure:?}");
    }
}

#[test]
fn nested_owner_rows_obey_the_existing_depth_limit_on_a_small_stack() {
    std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
        for depth in [STRUCTURAL_DEPTH_LIMIT + 1, 1_024] {
            let tree = FixtureCopy::new();
            let row = format!("{}{{Library.Inner}}{}", "{Library.Outer<".repeat(depth - 1), ">}".repeat(depth - 1));
            tree.replace("entry.ash", "main : Unit -> Unit", &format!("pub deep : Unit -> Unit where Library.Witness<{row}>\ndeep () = ()\n\nmain : Unit -> Unit"));
            let failure = tree.run().expect_err("complete owner rows must consume the existing structural depth budget");
            let Some(LoadGraphError::Syntax(syntax)) = failure.graph_failure() else {
                panic!("the parser must reject the depth before recursive source checking: {failure:?}");
            };
            assert_eq!(syntax.resource, Some(ResourceFailure::StructuralDepth { limit: STRUCTURAL_DEPTH_LIMIT }));
            assert!(syntax.lexical.is_empty());
            assert!(syntax.parser.is_empty());
            assert!(!failure.is_source_rejection(), "a replaceable implementation depth limit is not a language rejection");
        }
    }).unwrap().join().unwrap();
}

#[test]
fn resource_instance_actuals_preserve_preceding_row_scope_and_order() {
    let tree = FixtureCopy::new();
    let module = tree.resolve_entry("import library as Library\nprobe<Delta : EffectRow> : (Unit -> Unit ! {| Delta}) -> Unit\nprobe callback = resource Library.Connection<C, {| Delta}> db = () {\n()\n}\nmain : Unit -> Unit\nmain () = ()\n").expect("the complete imported resource actual must resolve before fresh identity admission");
    let ResolvedDefinitionKind::Equational(probe) = &module.definitions()[0].kind else {
        panic!("equational probe")
    };
    let delta = probe.interface.type_parameters[0].id;
    let ResolvedExprKind::ProviderResource(instance) = &probe.equations[0].body.kind else {
        panic!("resource instance")
    };
    let arguments = instance.arguments.as_ref().expect("explicit remainder");
    assert_eq!(arguments.len(), 1);
    let KindedArgument::RowArg(row) = &arguments[0].ty else {
        panic!("written row tag")
    };
    assert_eq!(
        row.tail().unwrap().variable(),
        EffectRowVariable::Rigid(delta)
    );
    assert_ne!(instance.identity.id, delta);
    assert!(row.known().is_empty());
    assert!(
        row.tail().unwrap().lacks().is_empty(),
        "instance resolution must not invent lacks conditions"
    );
}

#[test]
fn resource_instance_actuals_reject_omission_wrong_tags_and_fresh_scope_dependencies() {
    for (name, application, initializer) in [
        ("omitted row slot", "C", "()"),
        ("extra actual", "C, {}, Int", "()"),
        ("bare Type tag", "C, Delta", "()"),
        ("fresh row tail", "C, {| C}", "()"),
        (
            "fresh nested identity",
            "C, {Library.ConnectionOps<C, {}>}",
            "()",
        ),
        ("fresh initializer access", "C, {}", "db"),
    ] {
        let tree = FixtureCopy::new();
        let source = format!(
            "import library as Library\nprobe<Delta : EffectRow> : (Unit -> Unit ! {{| Delta}}) -> Unit\nprobe callback = resource Library.Connection<{application}> db = {initializer} {{\n()\n}}\nmain : Unit -> Unit\nmain () = ()\n"
        );
        let failure = tree.resolve_entry(&source).expect_err(name);
        let rejected = match &failure {
            ResolveModuleError::Resolution(error) => matches!(
                error.reason,
                ResolveReason::TypeKind | ResolveReason::UnknownType | ResolveReason::UnknownName
            ),
            ResolveModuleError::Kind(ash::kind::KindFailure::Source(error)) => {
                name == "bare Type tag" && error.reason == ash::kind::KindReason::Argument
            }
            _ => false,
        };
        assert!(
            rejected,
            "{name} must reject at a source boundary: {failure:?}"
        );
    }
}

#[test]
fn resource_instance_rows_use_the_existing_depth_limit() {
    std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
        for depth in [STRUCTURAL_DEPTH_LIMIT + 1, 1_024] {
            let tree = FixtureCopy::new();
            let row = format!("{}{{Library.Inner}}{}", "{Library.Outer<".repeat(depth - 1), ">}".repeat(depth - 1));
            tree.replace("entry.ash", "main () = ()", &format!("main () = resource Library.Connection<C, {row}> db = () {{\n()\n}}"));
            let failure = tree.run().expect_err("resource instance actual rows must consume the existing structural depth budget");
            let Some(LoadGraphError::Syntax(syntax)) = failure.graph_failure() else { panic!("depth must reject before source checking: {failure:?}") };
            assert_eq!(syntax.resource, Some(ResourceFailure::StructuralDepth { limit: STRUCTURAL_DEPTH_LIMIT }));
            assert!(syntax.lexical.is_empty());
            assert!(syntax.parser.is_empty());
        }
    }).unwrap().join().unwrap();
}

#[test]
fn row_free_resource_instances_preserve_explicit_and_deferred_retained_arguments() {
    for explicit in [false, true] {
        let tree = FixtureCopy::new();
        fs::copy(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/provider-experiments/sqlite-copying/sqlite.ash"),
            tree.0.join("sqlite.ash"),
        )
        .unwrap();
        let statement_parameters = if explicit { "S, C" } else { "S" };
        let source = format!(
            "import sqlite as Sqlite\nmain : Unit -> Unit\nmain () = resource Sqlite.Connection<C> db = (Sqlite.memory ()) {{\nresource Sqlite.Statement<{statement_parameters}> stmt = (db, (Sqlite.select_parameter ())) {{\n()\n}}\n}}\n"
        );
        let module = tree
            .resolve_entry(&source)
            .expect("both row-free source forms should resolve through the same owner carrier");
        let ResolvedDefinitionKind::Equational(main) = &module.definitions()[0].kind else {
            panic!("equational entry")
        };
        let ResolvedExprKind::ProviderResource(connection) = &main.equations[0].body.kind else {
            panic!("connection")
        };
        let ResolvedExprKind::Block(body) = &connection.body.kind else {
            panic!("connection body")
        };
        let ResolvedExprKind::ProviderResource(statement) = &body.result.kind else {
            panic!("statement")
        };
        // Kind admission must use the imported defining inventory, while the
        // source registry and both fresh identities remain in the client.
        assert_ne!(connection.definition.module(), module.module());
        assert_ne!(statement.definition.module(), module.module());
        assert_eq!(connection.identity.id.module(), Some(module.module()));
        assert_eq!(statement.identity.id.module(), Some(module.module()));
        assert_ne!(connection.identity.id, statement.identity.id);
        assert!(connection.arguments.is_none());
        if explicit {
            let arguments = statement
                .arguments
                .as_ref()
                .expect("explicit retained owner");
            assert_eq!(arguments.len(), 1);
            assert!(
                matches!(arguments[0].ty, KindedArgument::TypeArg(ash::types::Type::Variable(identity)) if identity == connection.identity.id)
            );
        } else {
            assert!(
                statement.arguments.is_none(),
                "initializer inference remains deferred to typing"
            );
        }
    }
}
