use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{PipelineFailure, RunConfiguration, run_path},
    elaborate::check_module,
    module::{LoadedModule, ModuleGraph, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, ResolveModuleError, ResolveReason, resolve_module},
    resolved::{Binder, CheckedModule, ResolvedDefinition, ResolvedDefinitionKind, ResolvedModule},
    types::TYPE_WORK_LIMIT,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

#[test]
fn qualified_non_effect_retains_the_selected_name() {
    use ash::presentation::{compile_resolve_diagnostic, write_json};
    let tree = TempTree::create();
    tree.write("library.ash", "pub type Thing = Thing\n");
    let failure = run_path(RunConfiguration {
        entry: tree.write(
            "entry.ash",
            "import library as Lib\nprobe : Unit -> Unit ! {Lib.Thing}\nprobe () = ()\n",
        ),
        roots: ModuleRoots::empty(),
    })
    .unwrap_err();
    let Some(PipelineFailure::Resolution(error)) = failure.pipeline_failure() else {
        panic!("{failure:?}")
    };
    assert_eq!(error.reason, ResolveReason::EffectKind);
    let sources: Vec<_> = failure.sources().iter().collect();
    let view = compile_resolve_diagnostic(error, &sources).unwrap();
    let mut output = Vec::new();
    write_json(&mut output, &view).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(json["facts"][0]["value"], "Thing");
    assert_eq!(json["facts"][1]["value"], "effect-required");
}

#[test]
fn inaccessible_names_render_access_causes_and_cross_file_declarations() {
    use ash::{
        message::{Catalogue, Locale},
        presentation::{compile_resolve_diagnostic, write_human, write_json},
    };
    for (entry, name, reason, access, english, related) in [
        (
            "import library as Lib\nmain : Unit -> Int\nmain () = Lib.hidden ()\n",
            "hidden",
            ResolveReason::UnavailableExport,
            "private",
            "The declaration `hidden` is private to its defining module.",
            true,
        ),
        (
            "import library as Lib\nmain : Unit -> Int\nmain () = Lib.absent ()\n",
            "absent",
            ResolveReason::UnavailableExport,
            "not-exported",
            "No imported declaration named `absent` is available in this namespace.",
            false,
        ),
        (
            "main : Unit -> Int\nmain () = Missing.absent ()\n",
            "Missing",
            ResolveReason::UnavailableExport,
            "unknown-module-alias",
            "No module alias named `Missing` is in scope.",
            false,
        ),
        (
            "import library as Lib\nmain : Unit -> Lib.Box\nmain () = Lib.Box 1\n",
            "Box",
            ResolveReason::OpaqueConstructor,
            "opaque-constructor",
            "The constructor `Box` belongs to an opaque type and is not accessible here.",
            true,
        ),
        (
            "import library (Box as Renamed)\nmain : Unit -> Renamed\nmain () = Renamed 1\n",
            "Renamed",
            ResolveReason::OpaqueConstructor,
            "opaque-constructor",
            "The constructor `Renamed` belongs to an opaque type and is not accessible here.",
            true,
        ),
    ] {
        let tree = TempTree::create();
        tree.write(
            "library.ash",
            "pub opaque type Box = Box(Int)\nhidden : Unit -> Int\nhidden () = 1\n",
        );
        let failure = run_path(RunConfiguration {
            entry: tree.write("entry.ash", entry),
            roots: ModuleRoots::empty(),
        })
        .unwrap_err();
        let Some(PipelineFailure::Resolution(error)) = failure.pipeline_failure() else {
            panic!("{failure:?}")
        };
        assert_eq!(error.reason, reason);
        let sources: Vec<_> = failure.sources().iter().collect();
        let diagnostic = compile_resolve_diagnostic(error, &sources).unwrap();
        for locale in [Locale::English, Locale::Bulgarian] {
            let mut output = Vec::new();
            write_human(&mut output, &diagnostic, &Catalogue::new(locale).unwrap()).unwrap();
            let output = String::from_utf8(output).unwrap();
            assert!(output.contains(&format!("`{name}`")));
            if locale == Locale::English {
                assert!(output.contains(english), "{output}");
            }
            if related {
                assert!(output.contains("library.ash"));
            }
        }
        let mut output = Vec::new();
        write_json(&mut output, &diagnostic).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["facts"][0]["value"], name);
        assert_eq!(json["facts"][1]["name"], "access");
        assert_eq!(json["facts"][1]["value"], access);
        if related {
            assert_eq!(
                json["labels"][1]["relationship"],
                "inaccessible_declaration"
            );
            // The local spelling may be an alias, not the declaration's own name.
            assert!(json["labels"][1]["facts"].as_array().unwrap().is_empty());
            assert!(
                json["labels"][1]["path"]
                    .as_str()
                    .unwrap()
                    .ends_with("library.ash")
            );
            let entry_sources: Vec<_> = sources
                .iter()
                .copied()
                .filter(|source| source.id() == error.primary.span().source())
                .collect();
            assert!(compile_resolve_diagnostic(error, &entry_sources).is_err());
        } else {
            assert_eq!(json["labels"].as_array().unwrap().len(), 1);
        }
    }
}

struct TempTree(PathBuf);

impl TempTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-module-resolution-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("test tree should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, text: &str) -> PathBuf {
        let path = self.0.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("fixture parent should be creatable");
        }
        fs::write(&path, text).expect("fixture should be writable");
        path
    }
}

impl Drop for TempTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn load(tree: &TempTree, entry_text: &str, dependencies: &[(&str, &str)]) -> ModuleGraph {
    let entry = tree.write("entry.ash", entry_text);
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

fn resolve_leaf(graph: &ModuleGraph, target: &LoadedModule) -> ResolvedModule {
    let mut checked: Vec<CheckedModule> = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|dependency| dependency.module() == edge.target())
                    .expect("dependencies should precede their importer");
                DependencyExports::new(edge, dependency.exports())
                    .expect("exact target summary should authenticate")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies).expect("fixture should resolve");
        if module.id() == target.id() {
            return resolved;
        }
        checked.push(check_module(resolved).expect("preceding dependency should check"));
    }
    panic!("target should belong to the graph")
}

fn definition_binder(definition: &ResolvedDefinition) -> &Binder {
    match &definition.kind {
        ResolvedDefinitionKind::Equational(global)
        | ResolvedDefinitionKind::ForeignConstant(global) => &global.interface.name,
        ResolvedDefinitionKind::InlineOperational(global) => &global.header.name,
    }
}

#[test]
fn local_binder_numbers_are_qualified_by_their_defining_module() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import first as First\nimport second as Second\n",
        &[
            ("first.ash", "same : Unit -> Unit\nsame value = value\n"),
            ("second.ash", "same : Unit -> Unit\nsame value = value\n"),
        ],
    );
    let first = module_named(&graph, "first.ash");
    let second = module_named(&graph, "second.ash");
    let first_resolved = resolve_leaf(&graph, first);
    let second_resolved = resolve_leaf(&graph, second);
    let first_id = definition_binder(&first_resolved.definitions()[0]).id;
    let second_id = definition_binder(&second_resolved.definitions()[0]).id;

    assert_eq!(first_id.local(), second_id.local());
    assert_ne!(first_id, second_id);
    assert_eq!(first_id.module(), Some(first.id()));
    assert_eq!(second_id.module(), Some(second.id()));
}

#[test]
fn selected_opaque_identity_agrees_with_a_helpers_hidden_signature_closure() {
    let tree = TempTree::create();
    tree.write(
        "base.ash",
        "pub opaque type Token<R> = Hidden\npub interface Read<R> {\nread : Token<R> -> Int\n}\n",
    );
    tree.write("helper.ash", "import base as Base\npub forward<R> : Base.Token<R> -> Int where Base.Read<R>\nforward value = Base.read value\n");
    tree.write("facade.ash", "pub import helper (forward)\n");
    for imports in [
        "import base (Token)\nimport facade (forward)\n",
        "import facade (forward)\nimport base (Token)\n",
    ] {
        let entry = tree.write(
            "entry.ash",
            &format!("{imports}main : Unit -> Int\nmain () = 42\n"),
        );
        assert_eq!(
            run_path(RunConfiguration {
                entry,
                roots: ModuleRoots::empty()
            })
            .expect("route visibility is not defining metadata")
            .value_display(),
            "42"
        );
    }
    for (source, reason) in [
        (
            "import base (Token)\nimport facade (forward)\nmain : Unit -> Int\nmain () = Hidden\n",
            "resolve.unknown-constructor",
        ),
        (
            "import facade (forward)\ninspect : Token<Int> -> Int\ninspect value = 42\nmain : Unit -> Int\nmain () = 42\n",
            "kind.not-applicable",
        ),
    ] {
        let entry = tree.write("entry.ash", source);
        let failure = run_path(RunConfiguration {
            entry,
            roots: ModuleRoots::empty(),
        })
        .unwrap_err();
        assert_eq!(failure.reason_code(), reason, "{failure:?}");
    }
}

#[test]
fn resolved_modules_are_declarations_only() {
    let tree = TempTree::create();
    let graph = load(&tree, "main : Unit -> Int\nmain () = 42\n", &[]);
    let entry = module_named(&graph, "entry.ash");
    let resolved = resolve_leaf(&graph, entry);

    assert_eq!(resolved.module(), entry.id());
    assert_eq!(resolved.definitions().len(), 1);
    assert_eq!(resolved.span(), entry.surface().span);
}

#[test]
fn export_candidates_reflect_term_and_type_visibility() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "type Hidden = Hidden(Int)\n",
            "pub opaque type Opaque = Opaque(Int)\n",
            "pub type Visible = Visible(Int)\n",
            "private_value : Unit -> Int\n",
            "private_value () = 0\n",
            "pub public_value : Unit -> Int\n",
            "public_value () = 1\n",
        ),
        &[],
    );
    let resolved = resolve_leaf(&graph, module_named(&graph, "entry.ash"));
    let candidate = resolved.export_candidate();

    assert!(candidate.term("private_value").is_none());
    assert!(candidate.term("public_value").is_some());
    assert!(candidate.is_private("private_value"));

    assert!(candidate.nominal("Hidden").is_none());
    assert!(candidate.constructor("Hidden").is_none());
    assert!(candidate.is_private("Hidden"));
    let hidden = resolved
        .registry()
        .nominals()
        .iter()
        .filter(|nominal| nominal.id.module() == resolved.module() && nominal.spelling == "Hidden")
        .collect::<Vec<_>>();
    let [hidden] = hidden.as_slice() else {
        panic!("one entry-owned Hidden nominal")
    };
    assert!(candidate.hidden_nominal(hidden.id).is_some());

    assert!(candidate.nominal("Opaque").is_some());
    assert!(candidate.constructor("Opaque").is_none());
    assert!(candidate.is_opaque_constructor("Opaque"));

    assert!(candidate.nominal("Visible").is_some());
    assert!(candidate.constructor("Visible").is_some());
}

#[test]
fn a_public_inline_operational_global_is_available_to_a_targeted_import() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import operations (increment)\n",
            "main : Unit -> Int\n",
            "main () = increment 41\n",
        ),
    );
    tree.write(
        "operations.ash",
        "pub fn increment(value : Int) -> Int {\n    value + 1\n}\n",
    );

    let observation = run_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect("the public operational term should enter the targeted import scope");

    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn duplicate_module_aliases_are_rejected_before_export_lookup() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import first as Shared\nimport second as Shared\n",
        &[("first.ash", ""), ("second.ash", "")],
    );
    let entry = module_named(&graph, "entry.ash");
    let no_exports: &[DependencyExports<'_>] = &[];

    let ResolveModuleError::Resolution(error) = resolve_module(entry, no_exports)
        .expect_err("a duplicate alias should fail before dependency export lookup")
    else {
        panic!("duplicate aliases should fail in resolution")
    };

    assert_eq!(error.reason, ResolveReason::DuplicateModuleAlias);
}

#[test]
fn export_candidates_keep_withheld_type_and_constructor_namespaces_separate() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!("type Foo = PrivateFoo\n", "pub opaque type Token = Foo\n",),
        &[],
    );
    let resolved = resolve_leaf(&graph, module_named(&graph, "entry.ash"));
    let candidate = resolved.export_candidate();

    assert!(candidate.is_private("Foo"));
    assert!(candidate.is_opaque_constructor("Foo"));
}

#[test]
fn repeated_summary_imports_share_one_graph_type_work_budget() {
    const PAYLOAD_WIDTH: usize = 32;
    const CONSTRUCTOR_NAME_BYTES: usize = 4_096;
    // Original authentication prepays both spelling byte slices in TypeWork.
    // Keep the payload modest so its independent constraint comparisons do not
    // exhaust that ledger before the repeated summary imports reach TypeWork.
    const DEPENDENT_COUNT: usize = TYPE_WORK_LIMIT / (2 * CONSTRUCTOR_NAME_BYTES) + 2;

    let tree = TempTree::create();
    let mut base = String::with_capacity(PAYLOAD_WIDTH * 5 + 32);
    base.push_str("pub type Wide =\n");
    base.push_str(&"W".repeat(CONSTRUCTOR_NAME_BYTES));
    base.push('(');
    for index in 0..PAYLOAD_WIDTH {
        if index > 0 {
            base.push_str(", ");
        }
        base.push_str("Int");
    }
    base.push_str(")\n");
    tree.write("base.ash", &base);

    let control = tree.write(
        "control.ash",
        "import base as Base\nmain : Unit -> Int\nmain () = 0\n",
    );
    let observation = run_path(RunConfiguration {
        entry: control,
        roots: ModuleRoots::empty(),
    })
    .expect("one complete summary import must fit all ordinary budgets");
    assert_eq!(observation.value_display(), "0");
    assert_eq!(observation.type_display(), "Int");

    let mut entry = String::new();
    for index in 0..DEPENDENT_COUNT {
        entry.push_str(&format!("import dependency{index} as Dependency{index}\n"));
        tree.write(&format!("dependency{index}.ash"), "import base as Base\n");
    }
    entry.push_str("main : Unit -> Int\nmain () = 0\n");
    let entry = tree.write("entry.ash", &entry);

    let observation = run_path(RunConfiguration {
        entry: entry.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("the input-sized graph allowance should admit all repeated summaries");
    assert_eq!(observation.value_display(), "0");
    assert_eq!(observation.type_display(), "Int");

    #[cfg(feature = "resource-calibration")]
    {
        let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
        let source_bytes = graph
            .modules()
            .iter()
            .map(|module| module.source().text().len())
            .sum::<usize>();
        let allowance = TYPE_WORK_LIMIT.max(80 * source_bytes);
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_ash"))
            .arg(&entry)
            .env_remove("ASH_CALIBRATION_LIMIT")
            .env("ASH_CALIBRATION_OBSERVE", "1")
            .output()
            .expect("observer child should execute");
        assert!(output.status.success(), "{:?}", output.stderr);
        assert_eq!(output.stdout, b"0 : Int\n");
        let records = String::from_utf8_lossy(&output.stderr)
            .lines()
            .filter_map(|line| line.strip_prefix("ASH_CALIBRATION "))
            .map(|json| serde_json::from_str::<serde_json::Value>(json).unwrap())
            .filter(|record| record["phase"] == "resolution")
            .collect::<Vec<_>>();
        assert!(records.iter().all(|record| record["completed"] == true
            && record["normal_limit"] == allowance
            && record["diagnostic_limit"] == allowance));
        let phases = records
            .iter()
            .filter(|record| record["event"] == "phase")
            .collect::<Vec<_>>();
        assert_eq!(phases.len(), graph.modules().len());
        // Each phase observes the supplied owner directly; a reset between
        // canonical modules would break cumulative growth or the endpoint.
        let mut previous = 0;
        for phase in &phases {
            let used = phase["work_cumulative"].as_u64().unwrap();
            assert!(used > previous);
            previous = used;
        }
        let endpoints = records
            .iter()
            .filter(|record| record["event"] == "work")
            .collect::<Vec<_>>();
        let [endpoint] = endpoints.as_slice() else {
            panic!("one completed resolution endpoint")
        };
        assert_eq!(endpoint["work_cumulative"], previous);
        assert!(previous > TYPE_WORK_LIMIT as u64);
    }
}

#[test]
fn repeated_targeted_nominal_metadata_shares_one_graph_type_work_budget() {
    const CONSTRUCTOR_COUNT: usize = 1_024;
    const ALIAS_COUNT: usize = TYPE_WORK_LIMIT / CONSTRUCTOR_COUNT + 1;

    let tree = TempTree::create();
    let mut base = String::from("pub type Wide =\n");
    for index in 0..CONSTRUCTOR_COUNT {
        if index > 0 {
            base.push_str("\n| ");
        }
        base.push_str(&format!("Case{index}"));
    }
    base.push('\n');
    tree.write("base.ash", &base);

    let mut entry = String::new();
    for index in 0..ALIAS_COUNT {
        entry.push_str(&format!("import base (Wide as Alias{index})\n"));
    }
    entry.push_str("main : Unit -> Unit\nmain value = value\n");
    let entry = tree.write("entry.ash", &entry);

    let failure = run_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect_err("repeated nominal metadata retention must share graph type work");

    let PipelineFailure::Resolution(error) = failure.pipeline_failure().expect("pipeline failure")
    else {
        panic!("graph type work should remain owned by resolution: {failure:?}");
    };
    assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
}
