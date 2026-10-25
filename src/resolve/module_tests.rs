use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use crate::{
    elaborate::check_module,
    module::{LoadedModule, ModuleGraph, ModuleRoots, load_module_graph},
    resolved::{
        BinderId, ExportSummary, ExportedTypeAccess, ImportedNominalFactRef, ImportedTypeAccess,
        ResolvedBuildFailure, ResolvedDefinitionKind, ResolvedExprKind, ResolvedModule,
        ResolvedPatternKind, ResolvedTypeVariable, SummaryCarrierMutationForTest,
        SummaryConstructorFusionMutationForTest, SummaryDuplicateFactForTest,
        SummaryHiddenDiamondMutationForTest, SummaryOrderForTest, SummaryWithheldMutationForTest,
    },
    source::Origin,
    types::{
        ConstructorId, Kind, NominalTypeId, TYPE_WORK_LIMIT, Type, TypeVariableId, TypeWorkBudget,
    },
};

use super::{
    DependencyExports, ResolveError, ResolveModuleError, ResolveReason, Resolver, resolve_module,
    resolve_module_with_budget,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

#[test]
fn generic_cell_summary_authenticates_complete_facade_facts() {
    use crate::resolved::BuiltinCellSummaryMutationForTest::*;
    for mutation in [
        OperationResult,
        ProviderResult,
        MissingHandle,
        MissingOps,
        HandleKind,
    ] {
        let tree = TempTree::create();
        tree.write("facade.ash", "pub import @builtin.generic_cell (read)\n");
        let graph = load(&tree, "import facade (read)\n", &[]);
        let builtin = &graph.modules()[0];
        let checked = check_module(resolve_module(builtin, &[]).unwrap()).unwrap();
        let facade = &graph.modules()[1];
        let dependency =
            DependencyExports::new(&facade.dependencies()[0], checked.exports()).unwrap();
        let mut summary = check_module(resolve_module(facade, &[dependency]).unwrap())
            .unwrap()
            .into_exports();
        summary.corrupt_builtin_fact_for_test(mutation);
        let entry = graph.module(graph.entry()).unwrap();
        let dependency = DependencyExports::new(&entry.dependencies()[0], &summary).unwrap();
        assert!(
            resolve_module(entry, &[dependency]).is_err(),
            "generic summary forgery admitted"
        );
    }
}

#[test]
fn generic_cell_duplicate_import_routes_reject_erased_contents_capture_fact() {
    for erase in [false, true] {
        let tree = TempTree::create();
        tree.write("helper.ash", "import @builtin.generic_cell as Cell\npub put<R,T> : (Cell.Cell<R,T>,T) -> Unit ! {Cell.Ops<R,T>} where Cell.Provider<R,T>\nput pair = Cell.write pair\n");
        tree.write("facade.ash", "pub import helper (put)\n");
        let graph = load(
            &tree,
            "import @builtin.generic_cell as Cell\nimport helper (put as direct)\nimport facade (put as via_facade)\nmain : Unit -> Int\nmain () = resource Cell.Cell<R,Int> c = 41 {\nlet _ = direct (c,42)\nlet _ = via_facade (c,43)\nCell.read c\n}\n",
            &[],
        );
        let mut summaries = Vec::new();
        for module in graph.modules() {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    DependencyExports::new(
                        edge,
                        summaries
                            .iter()
                            .find(|(id, _)| *id == edge.target())
                            .map(|(_, summary)| summary)
                            .unwrap(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let resolved = resolve_module(module, &dependencies);
            if module.id() == graph.entry() {
                if erase {
                    let error = resolved.unwrap_err();
                    assert!(
                        matches!(error,ResolveModuleError::Resolution(ref diagnostic) if diagnostic.reason==ResolveReason::InternalState),
                        "{error:?}"
                    );
                    assert!(
                        format!("{error:?}")
                            .contains("a dependency summary failed body-free authentication"),
                        "{error:?}"
                    );
                } else {
                    check_module(resolved.unwrap()).unwrap();
                }
                break;
            }
            let mut summary = check_module(resolved.unwrap()).unwrap().into_exports();
            if erase && module.source().display_path().ends_with("facade.ash") {
                summary.erase_exported_capture_for_test("put");
            }
            summaries.push((module.id(), summary));
        }
    }
}

#[test]
fn builtin_cell_summary_rejects_well_kinded_operation_tampering() {
    use crate::resolved::BuiltinCellSummaryMutationForTest;
    let tree = TempTree::create();
    let graph = load(&tree, "import @builtin.cell as Cell\n", &[]);
    let builtin = &graph.modules()[0];
    let mut summary = check_module(resolve_module(builtin, &[]).unwrap())
        .unwrap()
        .into_exports();
    summary.corrupt_builtin_fact_for_test(BuiltinCellSummaryMutationForTest::OperationResult);
    let entry = graph.module(graph.entry()).unwrap();
    let dependency = DependencyExports::new(&entry.dependencies()[0], &summary).unwrap();
    let error = resolve_module(entry, &[dependency]).expect_err("builtin signature is fixed");
    assert!(
        matches!(error, ResolveModuleError::Resolution(ref error) if error.reason == ResolveReason::InternalState)
    );
}

#[test]
fn builtin_cell_facade_rejects_tampered_or_detached_hidden_facts() {
    use crate::resolved::BuiltinCellSummaryMutationForTest::*;
    for mutation in [
        OperationResult,
        ProviderResult,
        MissingHandle,
        MissingOps,
        HandleKind,
    ] {
        let tree = TempTree::create();
        tree.write("facade.ash", "pub import @builtin.cell (read)\n");
        let graph = load(&tree, "import facade (read)\n", &[]);
        let builtin = &graph.modules()[0];
        let builtin_checked = check_module(resolve_module(builtin, &[]).unwrap()).unwrap();
        let facade = &graph.modules()[1];
        let dependency =
            DependencyExports::new(&facade.dependencies()[0], builtin_checked.exports()).unwrap();
        let mut summary = check_module(resolve_module(facade, &[dependency]).unwrap())
            .unwrap()
            .into_exports();
        summary.corrupt_builtin_fact_for_test(mutation);
        let entry = graph.module(graph.entry()).unwrap();
        let dependency = DependencyExports::new(&entry.dependencies()[0], &summary).unwrap();
        let error = resolve_module(entry, &[dependency])
            .expect_err("selected method needs authentic complete hidden facts");
        assert!(
            matches!(error, ResolveModuleError::Resolution(ref error) if error.reason == ResolveReason::InternalState)
        );
    }
}

#[test]
fn ordinary_effect_operation_summary_authenticates_retained_nominal_kinds() {
    use crate::resolved::BuiltinCellSummaryMutationForTest::{HandleKind, MissingHandle};
    for mutation in [HandleKind, MissingHandle] {
        let tree = TempTree::create();
        tree.write(
            "cell.ash",
            "pub opaque type Handle<R> = Hidden\npub effect Ops<R> {\nread : Handle<R> -> Int\n}\n",
        );
        let graph = load(&tree, "import cell as Cell\n", &[]);
        let ordinary = &graph.modules()[0];
        let mut summary = check_module(resolve_module(ordinary, &[]).unwrap())
            .unwrap()
            .into_exports();
        summary.corrupt_builtin_fact_for_test(mutation);
        let entry = graph.module(graph.entry()).unwrap();
        let dependency = DependencyExports::new(&entry.dependencies()[0], &summary).unwrap();
        let error = resolve_module(entry, &[dependency])
            .expect_err("effect signatures require their retained nominal kinds");
        assert!(
            matches!(error, ResolveModuleError::Resolution(ref error) if error.reason == ResolveReason::InternalState)
        );
    }
}

struct TempTree(PathBuf);

impl TempTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "ash-resolve-module-unit-{}-{id}",
                std::process::id()
            ));
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

fn resolve_with(
    module: &LoadedModule,
    summaries: &[&ExportSummary],
) -> Result<ResolvedModule, ResolveError> {
    assert_eq!(module.dependencies().len(), summaries.len());
    let dependencies = module
        .dependencies()
        .iter()
        .zip(summaries)
        .map(|(edge, summary)| {
            DependencyExports::new(edge, summary).expect("summary should match its import edge")
        })
        .collect::<Vec<_>>();
    resolve_module(module, &dependencies).map_err(|error| match error {
        ResolveModuleError::Resolution(error) => error,
        ResolveModuleError::Kind(error) => {
            panic!("module resolution fixture unexpectedly reached kind failure: {error:?}")
        }
        ResolveModuleError::Representation(error) => {
            panic!(
                "module resolution fixture unexpectedly reached representation failure: {error:?}"
            )
        }
    })
}

#[test]
fn globals_and_implementation_methods_share_capture_scans_per_import_edge() {
    let mut dependency = String::from("pub interface Observe<A> {\n");
    for index in 0..96 {
        dependency.push_str(&format!("observe{index} : A -> Int\n"));
    }
    dependency.push_str("}\n\npub impl Observe<Unit> {\n");
    for index in 0..96 {
        dependency.push_str(&format!("observe{index} () = {index}\n"));
    }
    dependency.push_str("}\n\n");
    for index in 0..96 {
        dependency.push_str(&format!(
            "pub value{index} : Unit -> Int\nvalue{index} () = {index}\n\n"
        ));
    }
    for methods_first in [false, true] {
        let mut selected = (0..96)
            .map(|index| format!("value{index}"))
            .collect::<Vec<_>>();
        if methods_first {
            selected.insert(0, "impl Observe".to_owned());
        } else {
            selected.push("impl Observe".to_owned());
        }
        let tree = TempTree::create();
        let graph = load(
            &tree,
            &format!("import dependency ({})\n", selected.join(", ")),
            &[("dependency.ash", &dependency)],
        );
        let defining = module_named(&graph, "dependency.ash");
        let checked = check_module(resolve_module(defining, &[]).unwrap()).unwrap();
        let entry = module_named(&graph, "entry.ash");
        let resolved = resolve_with(entry, &[checked.exports()])
            .expect("global and method capture metadata should fit the default import budget");
        assert_eq!(resolved.imported_facts().globals().count(), 96);
        assert_eq!(resolved.imported_facts().implementations().count(), 1);

        let imports =
            [DependencyExports::new(&entry.dependencies()[0], checked.exports()).unwrap()];
        let install = |limit| {
            let mut resolver = Resolver::with_budgets(
                entry.id(),
                TypeWorkBudget::with_limit(limit),
                crate::interface::InterfaceConstraintBudget::default(),
            );
            let result = resolver.install_imports(entry.surface(), &imports);
            (result, resolver.type_work.used())
        };
        let (result, exact) = install(TYPE_WORK_LIMIT);
        result.expect("shared scans should fit the default budget");
        let (result, used) = install(exact - 1);
        assert_eq!(
            result.unwrap_err().reason,
            ResolveReason::TypeResourceExhausted
        );
        assert_eq!(used, exact - 1);
        let (result, used) = install(exact);
        result.expect("fresh exact-budget retry should retain every selected fact");
        assert_eq!(used, exact);
    }
}

#[test]
fn fresh_import_capture_scan_rejects_missing_metadata_even_after_retention() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (first)\nimport dependency (second)\n",
        &[(
            "dependency.ash",
            concat!(
                "type Token = Token\n\n",
                "identity : Token -> Token\nidentity value = value\n\n",
                "pub first : Unit -> Int\nfirst () = match identity Token {\nToken => 1\n}\n\n",
                "pub second : Unit -> Int\nsecond () = match identity Token {\nToken => 2\n}\n",
            ),
        )],
    );
    let defining = module_named(&graph, "dependency.ash");
    let checked = check_module(resolve_module(defining, &[]).unwrap()).unwrap();
    let summary = checked.exports();
    let entry = module_named(&graph, "entry.ash");
    let missing = ExportSummary::test_fixture(defining.id(), vec![], vec![], vec![], vec![]);
    let mut resolver = Resolver::new(entry.id());
    resolver
        .retain_imported_global(
            summary.term("first").unwrap(),
            summary,
            entry.dependencies()[0].import_span(),
            &mut super::CaptureGraphVisits::default(),
        )
        .unwrap();
    let second_span = entry.dependencies()[1].import_span();
    let error = resolver
        .retain_imported_global(
            summary.term("second").unwrap(),
            &missing,
            second_span,
            &mut super::CaptureGraphVisits::default(),
        )
        .expect_err("a fresh route must consult its own summary's capture metadata");
    assert_eq!(error.reason, ResolveReason::InternalState);
    assert_eq!(error.primary.span(), second_span);
}

#[test]
fn reordered_dependency_pairs_are_rejected_before_scope_installation() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import first as First\nimport second as Second\n",
        &[("first.ash", ""), ("second.ash", "")],
    );
    let importer = module_named(&graph, "entry.ash");
    let first = module_named(&graph, "first.ash");
    let second = module_named(&graph, "second.ash");
    let first_summary = ExportSummary::test_fixture(first.id(), vec![], vec![], vec![], vec![]);
    let second_summary = ExportSummary::test_fixture(second.id(), vec![], vec![], vec![], vec![]);
    let mut dependencies = importer
        .dependencies()
        .iter()
        .zip([&first_summary, &second_summary])
        .map(|(edge, summary)| DependencyExports::new(edge, summary).expect("matching summary"))
        .collect::<Vec<_>>();
    dependencies.swap(0, 1);

    let error = resolve_module(importer, &dependencies)
        .expect_err("source import order must authenticate dependency pairs");

    let ResolveModuleError::Resolution(error) = error else {
        panic!("mismatched dependencies should fail during resolution")
    };
    assert_eq!(error.reason, ResolveReason::InternalState);
    let diagnostic =
        crate::presentation::compile_resolve_diagnostic(&error, &[importer.source()]).unwrap();
    for locale in [
        crate::message::Locale::English,
        crate::message::Locale::Bulgarian,
    ] {
        let mut output = Vec::new();
        crate::presentation::write_human(
            &mut output,
            &diagnostic,
            &crate::message::Catalogue::new(locale).unwrap(),
        )
        .unwrap();
        assert!(!output.is_empty());
    }
    let mut output = Vec::new();
    crate::presentation::write_json(&mut output, &diagnostic).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(json["responsibility"], "compiler");
    assert_eq!(json["facts"][0]["value"], "dependency-summary-mismatch");
}

#[test]
fn malformed_summary_admission_precedes_later_type_resource_in_dependency_order() {
    for malformed_first in [true, false] {
        let tree = TempTree::create();
        let first = if malformed_first {
            "malformed"
        } else {
            "clean"
        };
        let second = if malformed_first {
            "clean"
        } else {
            "malformed"
        };
        let entry = format!("import {first} as First\nimport {second} as Second\n");
        let graph = load(&tree, &entry, &[("malformed.ash", ""), ("clean.ash", "")]);
        let malformed = module_named(&graph, "malformed.ash");
        let clean = module_named(&graph, "clean.ash");
        let make_summary = |module: &LoadedModule| {
            ExportSummary::test_fixture(
                module.id(),
                vec![(
                    "unit",
                    BinderId::resolved(module.id(), 0),
                    Type::Unit,
                    Origin::Source(module.surface().span),
                )],
                vec![],
                vec![],
                vec![],
            )
        };
        let mut malformed_summary = make_summary(malformed);
        assert!(malformed_summary.corrupt_order_for_test(SummaryOrderForTest::Term));
        let clean_summary = make_summary(clean);
        let importer = module_named(&graph, "entry.ash");
        let summaries = if malformed_first {
            [&malformed_summary, &clean_summary]
        } else {
            [&clean_summary, &malformed_summary]
        };
        let dependencies = importer
            .dependencies()
            .iter()
            .zip(summaries)
            .map(|(edge, summary)| {
                DependencyExports::new(edge, summary).expect("the summary must match its edge")
            })
            .collect::<Vec<_>>();
        let mut type_work = TypeWorkBudget::with_limit(3);
        let error = resolve_module_with_budget(
            importer,
            &dependencies,
            &mut type_work,
            &mut crate::interface::InterfaceConstraintBudget::default(),
        )
        .expect_err("the first dependency boundary must own the failure");
        let ResolveModuleError::Resolution(error) = error else {
            panic!("summary admission should fail before the local Kind gate")
        };
        assert_eq!(
            error.reason,
            if malformed_first {
                ResolveReason::InternalState
            } else {
                ResolveReason::TypeResourceExhausted
            },
        );
        // The first summary's completed publication consumes the fixed
        // original/provenance admission cells before this boundary fails.
        assert_eq!(type_work.used(), 3);
    }
}

#[test]
fn unselected_kind_invalid_summary_fact_is_rejected_before_local_checking() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (Token)\nmain : Unit -> Unit\nmain () = ()\n",
        &[(
            "dependency.ash",
            concat!(
                "pub type Token = Token\n\n",
                "pub lift<F : Type -> Type> : F<Int> -> F<Int>\n",
                "lift value = value\n",
            ),
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let checked = check_module(
        resolve_module(dependency, &[]).expect("the dependency should resolve before mutation"),
    )
    .expect("the dependency should check before mutation");
    let mut summary = checked.into_exports();
    assert!(summary.replace_first_term_parameter_kind_for_test(Kind::Type));
    let importer = module_named(&graph, "entry.ash");

    let error = resolve_with(importer, &[&summary])
        .expect_err("an unselected forged scheme must fail dependency-summary admission");

    assert_eq!(error.reason, ResolveReason::InternalState);
}

#[test]
fn frozen_summary_retains_authoritative_declaration_order() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency as Dependency\n",
        &[(
            "dependency.ash",
            concat!(
                "pub zeta : Unit -> Unit\nzeta value = value\n\n",
                "pub alpha : Unit -> Unit\nalpha value = value\n\n",
                "pub type Zed = Zed\n\n",
                "pub type Able = Able\n",
            ),
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let summary = check_module(
        resolve_module(dependency, &[]).expect("the ordered dependency should resolve"),
    )
    .expect("the ordered dependency should check")
    .into_exports();

    assert_eq!(
        summary.term_authentication_order_for_test(),
        ["zeta", "alpha"],
    );
    assert_eq!(
        summary.nominal_authentication_order_for_test(),
        ["Zed", "Able"],
    );
    assert_eq!(
        summary.constructor_authentication_order_for_test(),
        ["Zed", "Able"],
    );
    let importer = module_named(&graph, "entry.ash");
    let retained = resolve_with(importer, &[&summary])
        .expect("the qualified import should preserve authenticated freeze order");
    let retained_binders = retained
        .imported_facts()
        .globals()
        .map(|global| global.binder)
        .collect::<Vec<_>>();
    let expected_binders = summary
        .terms()
        .map(|(_, global)| global.binder)
        .collect::<Vec<_>>();
    assert_eq!(retained_binders, expected_binders);
}

#[test]
fn unselected_constructor_scheme_corruption_fails_summary_admission() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (marker)\nmain : Unit -> Unit\nmain () = marker(())\n",
        &[(
            "dependency.ash",
            concat!(
                "pub type Boxed<A> = Boxed(A)\n\n",
                "pub marker : Unit -> Unit\nmarker value = value\n",
            ),
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let checked = check_module(
        resolve_module(dependency, &[]).expect("the constructor dependency should resolve"),
    )
    .expect("the constructor dependency should check");
    let mut summary = checked.into_exports();
    assert!(summary.replace_first_constructor_scheme_value_type_for_test(Type::Unit));
    let importer = module_named(&graph, "entry.ash");

    let error = resolve_with(importer, &[&summary])
        .expect_err("an unselected forged constructor scheme must fail admission");

    assert_eq!(error.reason, ResolveReason::InternalState);
}

#[test]
fn unselected_implementation_method_corruption_fails_summary_admission() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (marker)\nmain : Unit -> Unit\nmain () = marker(())\n",
        &[(
            "dependency.ash",
            concat!(
                "pub interface Observe<A> {\nobserve : A -> A\n}\n\n",
                "pub impl Observe<Int> {\nobserve value = value\n}\n\n",
                "pub marker : Unit -> Unit\nmarker value = value\n",
            ),
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let checked = check_module(
        resolve_module(dependency, &[]).expect("the implementation dependency should resolve"),
    )
    .expect("the implementation dependency should check");
    let mut summary = checked.into_exports();
    assert!(summary.replace_first_implementation_method_value_type_for_test(Type::Unit));
    let importer = module_named(&graph, "entry.ash");

    let error = resolve_with(importer, &[&summary])
        .expect_err("an unselected kind-valid method forgery must fail admission");

    assert_eq!(error.reason, ResolveReason::InternalState);
}

#[test]
fn exhaustive_summary_orders_indexes_aliases_and_owners_fail_before_local_checking() {
    #[derive(Clone, Copy)]
    enum Mutation {
        Order(SummaryOrderForTest),
        NominalIndex,
        ConstructorIndex,
        ConflictingGlobalAlias,
        ConflictingNominalAlias,
        ConstructorCount,
        HiddenConstructorCount,
        CrossOwnerBinder,
        InterfacePosition,
        ImplementationPosition,
        WithheldBijection,
        Withheld(SummaryWithheldMutationForTest),
        ExpressionCollision,
        TypeCollision,
        BinderCollision,
    }

    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (Wrap)\nmain : Unit -> Unit\nmain () = ()\n",
        &[(
            "dependency.ash",
            concat!(
                "pub type Wrap<F : Type -> Type> = Wrap(F<Int>)\n\n",
                "type Secret<F : Type -> Type> = Secret(F<Int>)\n\n",
                "private_marker : Unit -> Unit\nprivate_marker value = value\n\n",
                "pub interface Observe<A> {\nobserve : A -> A\n}\n\n",
                "pub expose<F : Type -> Type> : Secret<F> -> Secret<F>\n",
                "expose value = value\n\n",
                "pub impl<F : Type -> Type> Observe<Wrap<F>> {\n",
                "observe value = value\n}\n",
            ),
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let mutations = [
        Mutation::Order(SummaryOrderForTest::Term),
        Mutation::Order(SummaryOrderForTest::Nominal),
        Mutation::Order(SummaryOrderForTest::Constructor),
        Mutation::Order(SummaryOrderForTest::InterfaceName),
        Mutation::Order(SummaryOrderForTest::MethodName),
        Mutation::Order(SummaryOrderForTest::HiddenNominal),
        Mutation::NominalIndex,
        Mutation::ConstructorIndex,
        Mutation::ConflictingGlobalAlias,
        Mutation::ConflictingNominalAlias,
        Mutation::ConstructorCount,
        Mutation::HiddenConstructorCount,
        Mutation::CrossOwnerBinder,
        Mutation::InterfacePosition,
        Mutation::ImplementationPosition,
        Mutation::WithheldBijection,
        Mutation::Withheld(SummaryWithheldMutationForTest::TermKind),
        Mutation::Withheld(SummaryWithheldMutationForTest::TermOwner),
        Mutation::Withheld(SummaryWithheldMutationForTest::NominalKind),
        Mutation::Withheld(SummaryWithheldMutationForTest::NominalOwner),
        Mutation::Withheld(SummaryWithheldMutationForTest::ConstructorOwner),
        Mutation::Withheld(SummaryWithheldMutationForTest::ConstructorPosition),
        Mutation::Withheld(SummaryWithheldMutationForTest::MapOnly),
        Mutation::ExpressionCollision,
        Mutation::TypeCollision,
        Mutation::BinderCollision,
    ];

    for mutation in mutations {
        let checked = check_module(
            resolve_module(dependency, &[]).expect("the matrix dependency should resolve"),
        )
        .expect("the matrix dependency should check");
        let mut summary = checked.into_exports();
        let changed = match mutation {
            Mutation::Order(order) => summary.corrupt_order_for_test(order),
            Mutation::NominalIndex => summary.remove_first_reverse_index_for_test(false),
            Mutation::ConstructorIndex => summary.remove_first_reverse_index_for_test(true),
            Mutation::ConflictingGlobalAlias => summary
                .duplicate_first_global_with_conflicting_scheme_for_test("forged", Type::Unit),
            Mutation::ConflictingNominalAlias => {
                summary.duplicate_first_nominal_with_conflicting_origin_for_test("ForgedWrap")
            }
            Mutation::ConstructorCount => summary.increment_first_constructor_count_for_test(),
            Mutation::HiddenConstructorCount => {
                summary.increment_first_hidden_constructor_count_for_test()
            }
            Mutation::CrossOwnerBinder => {
                summary.reuse_nominal_parameter_as_interface_owner_for_test()
            }
            Mutation::InterfacePosition => summary.corrupt_position_index_for_test(false),
            Mutation::ImplementationPosition => summary.corrupt_position_index_for_test(true),
            Mutation::WithheldBijection => summary.duplicate_withheld_order_entry_for_test(),
            Mutation::Withheld(mutation) => summary.corrupt_withheld_for_test(mutation),
            Mutation::ExpressionCollision => {
                summary.collide_first_method_with_first_term_for_test()
            }
            Mutation::TypeCollision => {
                summary.collide_first_interface_with_first_nominal_for_test()
            }
            Mutation::BinderCollision => {
                summary.collide_first_implementation_method_with_global_for_test()
            }
        };
        assert!(changed, "the selected matrix carrier should be present");
        let error = resolve_with(importer, &[&summary])
            .expect_err("every forged summary carrier must fail exhaustive admission");
        assert_eq!(error.reason, ResolveReason::InternalState);
    }
}

#[test]
fn exhaustive_public_and_hidden_summary_carriers_fail_before_local_checking() {
    const BASE_SOURCE: &str = concat!(
        "pub type Wrap<F : Type -> Type, A> =\n",
        "First(F<A>)\n",
        "| Second(F<A>)\n\n",
        "pub type Other<F : Type -> Type, A> = Other(F<A>)\n\n",
        "pub interface Observe<A> {\nobserve : A -> A\n}\n\n",
        "pub interface Witness<A> {\nwitness : A -> A\n}\n\n",
        "pub generic<B, A> : A -> B -> A where Observe<B>\n",
        "generic left right = left\n\n",
        "pub impl<F : Type -> Type, A> Observe<Wrap<F, A>> where Observe<A>, Witness<A> {\n",
        "observe value = value\n}\n\n",
        "pub impl<F : Type -> Type, A> Observe<Other<F, A>> {\n",
        "observe value = value\n}\n",
    );
    let direct_mutations = [
        SummaryCarrierMutationForTest::PublicNominalKind,
        SummaryCarrierMutationForTest::PublicNominalParameterIdentity,
        SummaryCarrierMutationForTest::PublicNominalParameterOwner,
        SummaryCarrierMutationForTest::PublicNominalParameterOrder,
        SummaryCarrierMutationForTest::PublicConstructorFamilyOrdinal,
        SummaryCarrierMutationForTest::PublicConstructorFamilyOwner,
        SummaryCarrierMutationForTest::PublicConstructorResultOwner,
        SummaryCarrierMutationForTest::PublicConstructorPayload,
        SummaryCarrierMutationForTest::PublicConstructorPayloadDomainKind,
        SummaryCarrierMutationForTest::PublicConstructorSchemeKind,
        SummaryCarrierMutationForTest::PublicConstructorSchemeParameterIdentity,
        SummaryCarrierMutationForTest::PublicInterfaceKind,
        SummaryCarrierMutationForTest::PublicInterfaceParameterIdentity,
        SummaryCarrierMutationForTest::PublicInterfaceParameterOwner,
        SummaryCarrierMutationForTest::PublicInterfaceMethodType,
        SummaryCarrierMutationForTest::PublicInterfaceMethodFreeBinder,
        SummaryCarrierMutationForTest::PublicInterfaceMethodKind,
        SummaryCarrierMutationForTest::PublicInterfaceMethodNonFunction,
        SummaryCarrierMutationForTest::PublicInterfaceEmptyMethods,
        SummaryCarrierMutationForTest::InterfaceIdentity,
        SummaryCarrierMutationForTest::MethodIdentity,
        SummaryCarrierMutationForTest::MethodOrdinal,
        SummaryCarrierMutationForTest::InterfaceNameTarget,
        SummaryCarrierMutationForTest::MethodNameTarget,
        SummaryCarrierMutationForTest::GlobalParameterIdentity,
        SummaryCarrierMutationForTest::GlobalParameterOrder,
        SummaryCarrierMutationForTest::GlobalUnusedParameter,
        SummaryCarrierMutationForTest::GlobalRequirementIdentity,
        SummaryCarrierMutationForTest::GlobalRequirementInterface,
        SummaryCarrierMutationForTest::GlobalRequirementArgumentKind,
        SummaryCarrierMutationForTest::GlobalParameterOwner,
        SummaryCarrierMutationForTest::GlobalParameterKind,
        SummaryCarrierMutationForTest::ImplementationHeadKind,
        SummaryCarrierMutationForTest::ImplementationHeadIdentity,
        SummaryCarrierMutationForTest::ImplementationHeadOrder,
        SummaryCarrierMutationForTest::ImplementationHeadOwner,
        SummaryCarrierMutationForTest::ImplementationArgument,
        SummaryCarrierMutationForTest::ImplementationSemanticHead,
        SummaryCarrierMutationForTest::ImplementationInterfaceIdentity,
        SummaryCarrierMutationForTest::ImplementationPrerequisiteIdentity,
        SummaryCarrierMutationForTest::ImplementationPrerequisiteOrder,
        SummaryCarrierMutationForTest::ImplementationPrerequisiteDuplicate,
        SummaryCarrierMutationForTest::ImplementationPrerequisiteKind,
        SummaryCarrierMutationForTest::ImplementationPrerequisiteInterface,
        SummaryCarrierMutationForTest::ImplementationPrerequisiteArgument,
        SummaryCarrierMutationForTest::ImplementationPrerequisiteOriginMirror,
        SummaryCarrierMutationForTest::ImplementationPrerequisiteSpanMirror,
        SummaryCarrierMutationForTest::ImplementationMethodRequirementIdentity,
        SummaryCarrierMutationForTest::ImplementationMethodSchemeParameterIdentity,
        SummaryCarrierMutationForTest::ImplementationMethodSchemeParameterKind,
        SummaryCarrierMutationForTest::ImplementationMethodIdentity,
        SummaryCarrierMutationForTest::ImplementationMethodMapping,
        SummaryCarrierMutationForTest::ImplementationMethodBinder,
        SummaryCarrierMutationForTest::ImplementationAuthorization,
        SummaryCarrierMutationForTest::ImplementationOverlap,
    ];

    for mutation in direct_mutations {
        let tree = TempTree::create();
        let graph = load(
            &tree,
            "import dependency as Dependency\nmain : Unit -> Unit\nmain value = value\n",
            &[("dependency.ash", BASE_SOURCE)],
        );
        let dependency = module_named(&graph, "dependency.ash");
        let mut summary = check_module(
            resolve_module(dependency, &[]).expect("the rich dependency should resolve"),
        )
        .expect("the rich dependency should check")
        .into_exports();
        assert!(
            summary.corrupt_carrier_for_test(mutation),
            "the direct carrier {mutation:?} should exist",
        );
        assert_eq!(
            summary.authenticate(
                &mut TypeWorkBudget::default(),
                &mut crate::interface::InterfaceConstraintBudget::default(),
            ),
            Err(ResolvedBuildFailure::InvalidState),
            "the raw boundary must reject {mutation:?} independently",
        );
        let importer = module_named(&graph, "entry.ash");
        let error = resolve_with(importer, &[&summary])
            .expect_err("every forged public summary carrier must fail admission");
        assert_eq!(error.reason, ResolveReason::InternalState, "{mutation:?}");
    }

    let hidden_mutations = [
        SummaryCarrierMutationForTest::HiddenNominalKind,
        SummaryCarrierMutationForTest::HiddenNominalParameterIdentity,
        SummaryCarrierMutationForTest::HiddenNominalParameterOwner,
        SummaryCarrierMutationForTest::HiddenNominalParameterOrder,
        SummaryCarrierMutationForTest::HiddenNominalAccess,
        SummaryCarrierMutationForTest::HiddenConstructorPayload,
        SummaryCarrierMutationForTest::HiddenConstructorPayloadDomainKind,
        SummaryCarrierMutationForTest::HiddenConstructorSchemeKind,
        SummaryCarrierMutationForTest::HiddenConstructorSchemeParameterIdentity,
        SummaryCarrierMutationForTest::HiddenConstructorResultOwner,
        SummaryCarrierMutationForTest::HiddenInterfaceKind,
        SummaryCarrierMutationForTest::HiddenInterfaceParameterIdentity,
        SummaryCarrierMutationForTest::HiddenInterfaceParameterOwner,
        SummaryCarrierMutationForTest::HiddenInterfaceIdentity,
        SummaryCarrierMutationForTest::HiddenInterfaceMethodType,
        SummaryCarrierMutationForTest::HiddenInterfaceMethodIdentity,
        SummaryCarrierMutationForTest::HiddenInterfaceMethodOwner,
        SummaryCarrierMutationForTest::HiddenInterfaceMethodFreeBinder,
        SummaryCarrierMutationForTest::HiddenInterfaceMethodKind,
    ];
    for mutation in hidden_mutations {
        let tree = TempTree::create();
        let graph = load(
            &tree,
            "import facade as Facade\nmain : Unit -> Unit\nmain value = value\n",
            &[
                ("facade.ash", "pub import base (First, impl Observe)\n"),
                ("base.ash", BASE_SOURCE),
            ],
        );
        let base = module_named(&graph, "base.ash");
        let base_summary = check_module(
            resolve_module(base, &[]).expect("the hidden-carrier base should resolve"),
        )
        .expect("the hidden-carrier base should check")
        .into_exports();
        let facade = module_named(&graph, "facade.ash");
        let mut summary = check_module(
            resolve_with(facade, &[&base_summary]).expect("the facade should resolve"),
        )
        .expect("the facade should check")
        .into_exports();
        assert!(
            summary.corrupt_carrier_for_test(mutation),
            "the hidden carrier {mutation:?} should exist",
        );
        assert_eq!(
            summary.authenticate(
                &mut TypeWorkBudget::default(),
                &mut crate::interface::InterfaceConstraintBudget::default(),
            ),
            Err(ResolvedBuildFailure::InvalidState),
            "the raw boundary must reject {mutation:?} independently",
        );
        let importer = module_named(&graph, "entry.ash");
        let error = resolve_with(importer, &[&summary])
            .expect_err("every forged hidden summary carrier must fail admission");
        assert_eq!(error.reason, ResolveReason::InternalState, "{mutation:?}");
    }
}

#[test]
fn relational_summary_rejects_complete_parameter_and_application_tampering_matrix() {
    const SOURCE: &str = concat!(
        "pub type Option<A> =\nNone\n| Some(A)\n\n",
        "pub interface Relation<Left, Right> {\n",
        "relation : (Left, Right) -> Bool\n",
        "}\n\n",
        "pub impl Relation<Int, Bool> {\n",
        "relation pair = true\n",
        "}\n",
    );
    let mutations = [
        SummaryCarrierMutationForTest::RelationalInterfaceParameterMissing,
        SummaryCarrierMutationForTest::RelationalInterfaceParameterExtra,
        SummaryCarrierMutationForTest::RelationalInterfaceParameterReordered,
        SummaryCarrierMutationForTest::RelationalInterfaceParameterIdentity,
        SummaryCarrierMutationForTest::RelationalInterfaceParameterWrongKind,
        SummaryCarrierMutationForTest::RelationalImplementationArgumentMissing,
        SummaryCarrierMutationForTest::RelationalImplementationArgumentExtra,
        SummaryCarrierMutationForTest::RelationalImplementationArgumentReordered,
        SummaryCarrierMutationForTest::RelationalImplementationArgumentWrongKind,
        SummaryCarrierMutationForTest::RelationalImplementationInterfaceIdentity,
    ];

    for mutation in mutations {
        let tree = TempTree::create();
        let graph = load(
            &tree,
            "import dependency as Dependency\nmain : Unit -> Unit\nmain value = value\n",
            &[("dependency.ash", SOURCE)],
        );
        let dependency = module_named(&graph, "dependency.ash");
        let mut summary = check_module(
            resolve_module(dependency, &[]).expect("the relational dependency should resolve"),
        )
        .expect("the relational dependency should check")
        .into_exports();
        assert!(
            summary.corrupt_carrier_for_test(mutation),
            "the relational carrier {mutation:?} should exist",
        );
        assert_eq!(
            summary.authenticate(
                &mut TypeWorkBudget::default(),
                &mut crate::interface::InterfaceConstraintBudget::default(),
            ),
            Err(ResolvedBuildFailure::InvalidState),
            "the raw summary boundary must reject {mutation:?}",
        );
        let importer = module_named(&graph, "entry.ash");
        let error = resolve_with(importer, &[&summary])
            .expect_err("the forged relational summary must fail before local checking");
        assert_eq!(error.reason, ResolveReason::InternalState, "{mutation:?}");
    }
}

#[test]
fn determined_summary_method_seed_has_exact_admission_boundaries() {
    // Each of the two methods adds one determinant-subset comparison and one
    // required-key coverage lookup to the predecessor body-free kind work.
    // Both methods independently authenticate their two inherited owner slots.
    // Canonical records live in the kind table, tiny permission domains borrow
    // their original IDs, and complete function synthesis supplies Type directly.
    const TYPE_WORK: usize = 26 + 2 * 2;
    const CONSTRAINT_WORK: usize = 11;
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency as Dependency\n",
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
    let dependency = module_named(&graph, "dependency.ash");
    let summary = check_module(
        resolve_module(dependency, &[]).expect("the determined dependency should resolve"),
    )
    .expect("the determined dependency should check locally")
    .into_exports();

    let mut measured_type = TypeWorkBudget::unbounded();
    let mut measured_constraint = crate::interface::InterfaceConstraintBudget::default();
    summary
        .authenticate(&mut measured_type, &mut measured_constraint)
        .expect("the honest determined summary should authenticate");
    assert_eq!(measured_type.used(), TYPE_WORK);
    assert_eq!(measured_constraint.used(), CONSTRAINT_WORK);

    let mut type_short = TypeWorkBudget::with_limit(TYPE_WORK - 1);
    assert_eq!(
        summary.authenticate(
            &mut type_short,
            &mut crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK),
        ),
        Err(ResolvedBuildFailure::TypeResource),
    );
    assert_eq!(type_short.used(), TYPE_WORK - 1);

    let mut constraint_short =
        crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK - 1);
    assert_eq!(
        summary.authenticate(
            &mut TypeWorkBudget::with_limit(TYPE_WORK),
            &mut constraint_short,
        ),
        Err(ResolvedBuildFailure::ConstraintResource),
    );
    assert_eq!(constraint_short.used(), CONSTRAINT_WORK - 1);

    for _ in 0..2 {
        let mut exact_type_budget = TypeWorkBudget::with_limit(TYPE_WORK);
        let mut exact_constraint_budget =
            crate::interface::InterfaceConstraintBudget::with_limit(CONSTRAINT_WORK);
        summary
            .authenticate(&mut exact_type_budget, &mut exact_constraint_budget)
            .expect("the exact immutable determined summary should remain reusable");
        assert_eq!(exact_type_budget.used(), TYPE_WORK);
        assert_eq!(exact_constraint_budget.used(), CONSTRAINT_WORK);
    }
}

#[test]
fn summary_admission_rejects_every_malformed_private_determination_key() {
    const SOURCE: &str = concat!(
        "pub interface Relation<A, B, C> {\n",
        "relation : (A, B, C) -> Bool\n",
        "}\n",
    );
    for mutation in [
        SummaryCarrierMutationForTest::DeterminationPositionsEmpty,
        SummaryCarrierMutationForTest::DeterminationPositionsFull,
        SummaryCarrierMutationForTest::DeterminationPositionsRepeated,
        SummaryCarrierMutationForTest::DeterminationPositionsReordered,
        SummaryCarrierMutationForTest::DeterminationPositionsOutOfRange,
    ] {
        let tree = TempTree::create();
        let graph = load(
            &tree,
            "import dependency as Dependency\n",
            &[("dependency.ash", SOURCE)],
        );
        let dependency = module_named(&graph, "dependency.ash");
        let mut summary = check_module(
            resolve_module(dependency, &[]).expect("the no-edge dependency should resolve"),
        )
        .expect("the no-edge dependency should check")
        .into_exports();
        assert!(summary.corrupt_carrier_for_test(mutation));

        assert_eq!(
            summary.authenticate(
                &mut TypeWorkBudget::default(),
                &mut crate::interface::InterfaceConstraintBudget::default(),
            ),
            Err(ResolvedBuildFailure::InvalidState),
            "the private determinant positions must reject {mutation:?}",
        );
    }
}

#[test]
fn detached_summary_rechecks_variable_head_against_an_alternate_key() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "pub type List<A> = List(A)\n\n",
            "pub interface Relation<A, B> where A -> B {\n",
            "relation : (A, B) -> Unit\n",
            "}\n\n",
            "pub impl<X> Relation<List<X>, X> {\n",
            "relation value = ()\n",
            "}\n",
        ),
        &[],
    );
    let module = module_named(&graph, "entry.ash");
    let mut summary = check_module(
        resolve_module(module, &[]).expect("the honest determined module should resolve"),
    )
    .expect("the honest structured selection key should check")
    .into_exports();
    summary
        .authenticate(
            &mut TypeWorkBudget::default(),
            &mut crate::interface::InterfaceConstraintBudget::default(),
        )
        .expect("the honest determined summary should authenticate");
    assert!(summary.corrupt_carrier_for_test(
        SummaryCarrierMutationForTest::DeterminationPositionsAlternateKey,
    ));

    assert_eq!(
        summary.authenticate(
            &mut TypeWorkBudget::default(),
            &mut crate::interface::InterfaceConstraintBudget::default(),
        ),
        Err(ResolvedBuildFailure::InvalidState),
        "the alternate key makes the implementation selection key a bare variable",
    );
}

#[test]
fn detached_summary_rechecks_dependent_coverage_against_an_alternate_key() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "pub type List<A> = List(A)\n\n",
            "pub interface Relation<A, B, C> where (A, B) -> C {\n",
            "relation : (A, B, C) -> Unit\n",
            "}\n\n",
            "pub impl<X> Relation<List<X>, Int, X> {\n",
            "relation value = ()\n",
            "}\n",
        ),
        &[],
    );
    let module = module_named(&graph, "entry.ash");
    let mut summary = check_module(
        resolve_module(module, &[]).expect("the honestly covered module should resolve"),
    )
    .expect("the honest determinant key should cover its dependent variable")
    .into_exports();
    summary
        .authenticate(
            &mut TypeWorkBudget::default(),
            &mut crate::interface::InterfaceConstraintBudget::default(),
        )
        .expect("the honest covered summary should authenticate");
    assert!(summary.corrupt_carrier_for_test(
        SummaryCarrierMutationForTest::DeterminationPositionsAlternateKey,
    ));

    assert_eq!(
        summary.authenticate(
            &mut TypeWorkBudget::default(),
            &mut crate::interface::InterfaceConstraintBudget::default(),
        ),
        Err(ResolvedBuildFailure::InvalidState),
        "the alternate key no longer covers the dependent head variable",
    );
}

#[test]
fn detached_summary_rechecks_orphan_ownership_against_an_alternate_key() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency (Relation, relation)\n",
            "pub type Local = Local\n\n",
            "pub impl Relation<Local, Int, Bool> {\n",
            "relation value = ()\n",
            "}\n",
        ),
        &[(
            "dependency.ash",
            concat!(
                "pub interface Relation<A, B, C> where (A, B) -> C {\n",
                "relation : (A, B, C) -> Unit\n",
                "}\n",
            ),
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let dependency_summary = check_module(
        resolve_module(dependency, &[]).expect("the foreign interface should resolve"),
    )
    .expect("the foreign interface should check")
    .into_exports();
    let entry = module_named(&graph, "entry.ash");
    let mut summary = check_module(
        resolve_with(entry, &[&dependency_summary])
            .expect("the honestly authorized foreign implementation should resolve"),
    )
    .expect("the local outer nominal in the honest key should authorize the implementation")
    .into_exports();
    summary
        .authenticate(
            &mut TypeWorkBudget::default(),
            &mut crate::interface::InterfaceConstraintBudget::default(),
        )
        .expect("the honest orphan-authorized summary should authenticate");
    assert!(summary.corrupt_carrier_for_test(
        SummaryCarrierMutationForTest::DeterminationPositionsAlternateKey,
    ));

    assert_eq!(
        summary.authenticate(
            &mut TypeWorkBudget::default(),
            &mut crate::interface::InterfaceConstraintBudget::default(),
        ),
        Err(ResolvedBuildFailure::InvalidState),
        "the alternate key leaves the local nominal dependent-only",
    );
}

#[test]
fn determined_summary_relationship_authentication_has_an_exact_retry_boundary() {
    let build_summary = || {
        let tree = TempTree::create();
        let graph = load(
            &tree,
            concat!(
                "pub type List<A> = List(A)\n\n",
                "pub interface Relation<A, B> where A -> B {\n",
                "relation : (A, B) -> Unit\n",
                "}\n\n",
                "pub impl<X> Relation<List<X>, X> {\n",
                "relation value = ()\n",
                "}\n",
            ),
            &[],
        );
        let module = module_named(&graph, "entry.ash");
        check_module(
            resolve_module(module, &[]).expect("the exact relationship fixture should resolve"),
        )
        .expect("the exact relationship fixture should check")
        .into_exports()
    };

    let summary = build_summary();
    let mut measured_type = TypeWorkBudget::default();
    let mut measured_constraint = crate::interface::InterfaceConstraintBudget::default();
    summary
        .authenticate(&mut measured_type, &mut measured_constraint)
        .expect("the exact relationship fixture should authenticate");
    const PARAMETER_COUNT: usize = 2;
    const DETERMINANT_COUNT: usize = 1;
    const PARTITION_WORK: usize = DETERMINANT_COUNT + PARAMETER_COUNT + PARAMETER_COUNT;
    const VARIABLE_HEAD_WORK: usize = 1;
    const KEY_FREE_VARIABLE_WORK: usize = 7;
    const DEPENDENT_FREE_VARIABLE_WORK: usize = 3;
    const COVERAGE_SUBSET_WORK: usize = 1;
    const RELATIONSHIP_WORK: usize = PARTITION_WORK
        + VARIABLE_HEAD_WORK
        + KEY_FREE_VARIABLE_WORK
        + DEPENDENT_FREE_VARIABLE_WORK
        + COVERAGE_SUBSET_WORK;
    const PREDECESSOR_CONSTRAINT_WORK: usize = 60;
    // Complete tagged arguments are traversed for structural determination,
    // rather than dropping their tag at the relationship boundary.
    const COMPLETE_ARGUMENT_WORK: usize = 15;
    // Original constructor and completed implementation publications are
    // authenticated before relationship coverage. These retained ordinary
    // checks contribute 44 constraint units independently of foreign policy.
    const ORIGINAL_FACT_CONSTRAINT_WORK: usize = 44;
    const EXACT_CONSTRAINT_WORK: usize = PREDECESSOR_CONSTRAINT_WORK
        + RELATIONSHIP_WORK
        + COMPLETE_ARGUMENT_WORK
        + ORIGINAL_FACT_CONSTRAINT_WORK;
    // Canonical and inherited-role authentication retains every visit while
    // sharing four kind-table records and borrowing the two-ID method domain.
    // Complete function synthesis supplies its intrinsic Type without a pair walk.
    // List<X>'s XI installation also scans its one formal's owner kind.
    // Method callable-graph closure adds 27 paid visits even though this
    // fixture's retained types contain no effect identity.
    // Original constructor matching and the implementation's immutable capture
    // comparison contribute another 30 type-work units before this boundary.
    const ORIGINAL_FACT_TYPE_WORK: usize = 30;
    const EXACT_TYPE_WORK: usize = 104 + 1 + 27 + ORIGINAL_FACT_TYPE_WORK;
    assert_eq!(
        (measured_constraint.used(), measured_type.used()),
        (EXACT_CONSTRAINT_WORK, EXACT_TYPE_WORK),
    );

    let mut short =
        crate::interface::InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1);
    assert_eq!(
        summary.authenticate(&mut TypeWorkBudget::with_limit(EXACT_TYPE_WORK), &mut short,),
        Err(ResolvedBuildFailure::ConstraintResource),
    );
    assert_eq!(short.used(), EXACT_CONSTRAINT_WORK - 2);

    let mut type_short = TypeWorkBudget::with_limit(EXACT_TYPE_WORK - 1);
    assert_eq!(
        summary.authenticate(
            &mut type_short,
            &mut crate::interface::InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK,),
        ),
        Err(ResolvedBuildFailure::TypeResource),
    );
    assert_eq!(type_short.used(), EXACT_TYPE_WORK - 1);

    for _ in 0..2 {
        let mut exact_type = TypeWorkBudget::with_limit(EXACT_TYPE_WORK);
        let mut exact_constraint =
            crate::interface::InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        summary
            .authenticate(&mut exact_type, &mut exact_constraint)
            .expect("the exact immutable relationship summary should remain reusable");
        assert_eq!(exact_constraint.used(), EXACT_CONSTRAINT_WORK);
        assert_eq!(exact_type.used(), EXACT_TYPE_WORK);
    }
    assert_eq!(
        summary
            .interface("Relation")
            .and_then(|interface| interface.determinant_positions()),
        Some(&[0][..]),
    );
    let implementation = summary
        .implementations()
        .next()
        .expect("the exact fixture should retain one implementation");
    assert!(matches!(
        implementation.fact().arguments(),
        [
            crate::types::KindedArgument::TypeArg(Type::Application(_, _)),
            crate::types::KindedArgument::TypeArg(Type::Variable(_))
        ]
    ));
}

#[test]
fn relational_summary_application_arity_precedes_a_late_wrong_kind() {
    const SOURCE: &str = concat!(
        "pub type Option<A> =\nNone\n| Some(A)\n\n",
        "pub interface Relation<Left, Right> {\n",
        "relation : (Left, Right) -> Bool\n",
        "}\n\n",
        "pub impl Relation<Int, Bool> {\n",
        "relation pair = true\n",
        "}\n",
    );
    let measure = |mutation| {
        let tree = TempTree::create();
        let graph = load(
            &tree,
            "import dependency as Dependency\nmain : Unit -> Unit\nmain value = value\n",
            &[("dependency.ash", SOURCE)],
        );
        let dependency = module_named(&graph, "dependency.ash");
        let mut summary = check_module(
            resolve_module(dependency, &[]).expect("the relational dependency should resolve"),
        )
        .expect("the relational dependency should check")
        .into_exports();
        assert!(summary.corrupt_carrier_for_test(mutation));
        let mut type_work = TypeWorkBudget::default();
        assert_eq!(
            summary.authenticate(
                &mut type_work,
                &mut crate::interface::InterfaceConstraintBudget::default(),
            ),
            Err(ResolvedBuildFailure::InvalidState),
        );
        type_work.used()
    };

    let extra = measure(SummaryCarrierMutationForTest::RelationalImplementationArgumentExtra);
    let extra_with_late_wrong_kind = measure(
        SummaryCarrierMutationForTest::RelationalImplementationArgumentExtraWithLateWrongKind,
    );
    assert_eq!(
        extra_with_late_wrong_kind, extra,
        "argument-count rejection must stop before positional kind authentication",
    );
}

#[test]
fn fused_constructor_scheme_authentication_rejects_every_independent_type_obligation() {
    let mutations = [
        SummaryConstructorFusionMutationForTest::UnboundPayloadVariable,
        SummaryConstructorFusionMutationForTest::RegisteredForeignPayloadVariable,
        SummaryConstructorFusionMutationForTest::InferencePayload,
        SummaryConstructorFusionMutationForTest::OuterForallPayload,
        SummaryConstructorFusionMutationForTest::NestedForallPayload,
        SummaryConstructorFusionMutationForTest::UnexpectedRequirement,
        SummaryConstructorFusionMutationForTest::ResultSpineTooShort,
        SummaryConstructorFusionMutationForTest::ResultSpineExtra,
        SummaryConstructorFusionMutationForTest::ResultArgumentSwap,
        SummaryConstructorFusionMutationForTest::ResultArgumentDuplicate,
    ];
    for mutation in mutations {
        let tree = TempTree::create();
        let graph = load(
            &tree,
            "import dependency as Dependency\nmain : Unit -> Unit\nmain value = value\n",
            &[(
                "dependency.ash",
                concat!(
                    "pub type Pair<A, B> = Make(A)\n\n",
                    "pub interface Marker<A> {\nmark : A -> A\n}\n",
                ),
            )],
        );
        let dependency = module_named(&graph, "dependency.ash");
        let importer = module_named(&graph, "entry.ash");
        let mut summary = check_module(
            resolve_module(dependency, &[]).expect("the phantom-parameter fixture should resolve"),
        )
        .expect("a constructor payload need not mention every owner parameter")
        .into_exports();
        summary
            .authenticate(
                &mut TypeWorkBudget::default(),
                &mut crate::interface::InterfaceConstraintBudget::default(),
            )
            .expect("the canonical two-parameter constructor scheme should authenticate");
        assert!(
            summary.corrupt_first_constructor_fusion_obligation_for_test(mutation),
            "the constructor mutation {mutation:?} should apply",
        );
        assert_eq!(
            summary.authenticate(
                &mut TypeWorkBudget::default(),
                &mut crate::interface::InterfaceConstraintBudget::default(),
            ),
            Err(ResolvedBuildFailure::InvalidState),
            "the fused raw boundary must reject {mutation:?}",
        );
        let error = resolve_with(importer, &[&summary])
            .expect_err("forged constructor closure must fail before local checking");
        assert_eq!(error.reason, ResolveReason::InternalState, "{mutation:?}");
    }
}

#[test]
fn fused_constructor_payload_clone_preserves_first_nominal_occurrence_order() {
    // One owner insertion costs three Type cells; two hidden prerequisite
    // nominal insertions cost two each. Three prepared nominal actions and one
    // staged constructor action cost four, while the four-cell payload,
    // six-cell physical scheme, and constructor-map record cost eleven.
    const EXACT_TYPE_WORK: usize = 23;
    // The owner shape and one family-plan action cost three Constraint cells.
    // The six-cell scheme observes three unique nominal identities for twelve;
    // the four-cell payload observes no new identity. Two absent foreign
    // nominal validations and their plan records cost four.
    const EXACT_CONSTRAINT_WORK: usize = 23;
    let tree = TempTree::create();
    let graph = load(&tree, "", &[]);
    let dependency = module_named(&graph, "entry.ash");
    let module = dependency.id();
    let owner = NominalTypeId::new(module, 0);
    let first = NominalTypeId::new(module, 1);
    let second = NominalTypeId::new(module, 2);
    let span = dependency.surface().span;
    let origin = Origin::Source(span);
    let summary = ExportSummary::test_fixture(
        module,
        Vec::new(),
        vec![
            (
                "Owner",
                owner,
                ExportedTypeAccess::Transparent,
                origin.clone(),
            ),
            ("N1", first, ExportedTypeAccess::Transparent, origin.clone()),
            (
                "N2",
                second,
                ExportedTypeAccess::Transparent,
                origin.clone(),
            ),
        ],
        vec![
            (
                "Make",
                ConstructorId::new(owner, 0),
                Some(Type::Tuple(
                    vec![
                        Type::Nominal(first),
                        Type::Nominal(second),
                        Type::Nominal(first),
                    ]
                    .into_boxed_slice(),
                )),
                origin.clone(),
            ),
            (
                "N1Value",
                ConstructorId::new(first, 0),
                None,
                origin.clone(),
            ),
            ("N2Value", ConstructorId::new(second, 0), None, origin),
        ],
        Vec::new(),
    );
    summary
        .authenticate(
            &mut TypeWorkBudget::default(),
            &mut crate::interface::InterfaceConstraintBudget::default(),
        )
        .expect("the repeated-nominal payload summary should authenticate");
    let exported = summary.constructor("Make").expect("Make should be public");

    let mut constraint_short = Resolver::with_budgets(
        module,
        TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
        crate::interface::InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1),
    );
    let error = constraint_short
        .retain_imported_constructor(exported, &summary, span)
        .expect_err("one missing nominal-plan cell should reject the complete transaction");
    assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
    assert_eq!(
        constraint_short.constraint_work.used(),
        EXACT_CONSTRAINT_WORK - 1
    );
    assert_eq!(constraint_short.type_work.used(), 0);
    assert!(constraint_short.imported.constructor(exported.id).is_none());
    assert!(constraint_short.imported.nominals().next().is_none());

    let mut type_short = Resolver::with_budgets(
        module,
        TypeWorkBudget::with_limit(EXACT_TYPE_WORK - 1),
        crate::interface::InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK),
    );
    let error = type_short
        .retain_imported_constructor(exported, &summary, span)
        .expect_err("one missing aggregate Type cell should reject the complete transaction");
    assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
    assert_eq!(type_short.type_work.used(), 0);
    assert_eq!(type_short.constraint_work.used(), EXACT_CONSTRAINT_WORK);
    assert!(type_short.imported.constructor(exported.id).is_none());
    assert!(type_short.imported.nominals().next().is_none());

    let mut exact = Resolver::with_budgets(
        module,
        TypeWorkBudget::with_limit(EXACT_TYPE_WORK),
        crate::interface::InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK),
    );
    exact
        .retain_imported_constructor(exported, &summary, span)
        .expect("the exact fused clone/discovery formula should fit");
    assert_eq!(exact.type_work.used(), EXACT_TYPE_WORK);
    assert_eq!(exact.constraint_work.used(), EXACT_CONSTRAINT_WORK);
    assert_eq!(
        exact
            .imported
            .nominals()
            .map(|fact| fact.id)
            .collect::<Vec<_>>(),
        vec![owner, first, second],
    );
}

#[test]
fn public_admission_rejects_one_short_constructor_closure_without_publishing_output() {
    const DEPTH: usize = 32_768;
    std::thread::Builder::new()
        .name("deep-constructor-public-admission".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let tree = TempTree::create();
            let graph = load(
                &tree,
                "import dependency (Make)\nmain : Unit -> Unit\nmain value = value\n",
                &[("dependency.ash", "")],
            );
            let dependency = module_named(&graph, "dependency.ash");
            let importer = module_named(&graph, "entry.ash");
            let nominal = NominalTypeId::new(dependency.id(), 0);
            let constructor = ConstructorId::new(nominal, 0);
            let mut payload = Type::Unit;
            for _ in 0..DEPTH {
                payload = Type::Function(Box::new(Type::Int), Box::new(payload));
            }
            let summary = ExportSummary::test_fixture(
                dependency.id(),
                Vec::new(),
                vec![(
                    "Deep",
                    nominal,
                    ExportedTypeAccess::Transparent,
                    Origin::Source(dependency.surface().span),
                )],
                vec![(
                    "Make",
                    constructor,
                    Some(payload),
                    Origin::Source(dependency.surface().span),
                )],
                Vec::new(),
            );
            let exports = importer
                .dependencies()
                .iter()
                .map(|edge| DependencyExports::new(edge, &summary).expect("matching dependency"))
                .collect::<Vec<_>>();

            let mut measured = TypeWorkBudget::with_limit(usize::MAX);
            let measured_module = resolve_module_with_budget(
                importer,
                &exports,
                &mut measured,
                &mut crate::interface::InterfaceConstraintBudget::default(),
            )
            .expect("the complete body-free constructor closure should resolve");
            let exact_work = measured.used();
            assert!(exact_work <= TYPE_WORK_LIMIT, "{exact_work}");
            drop(measured_module);

            let mut one_short = TypeWorkBudget::with_limit(exact_work - 1);
            resolve_module_with_budget(
                importer,
                &exports,
                &mut one_short,
                &mut crate::interface::InterfaceConstraintBudget::default(),
            )
            .expect_err("one missing public-admission cell must publish no resolved module");

            let mut exact = TypeWorkBudget::with_limit(exact_work);
            let resolved = resolve_module_with_budget(
                importer,
                &exports,
                &mut exact,
                &mut crate::interface::InterfaceConstraintBudget::default(),
            )
            .expect("the same immutable summary must remain reusable after rejection");
            assert_eq!(exact.used(), exact_work);
            drop(resolved);
            drop(summary);
        })
        .expect("the public-admission lifecycle worker should spawn")
        .join()
        .expect("accepted and rejected public admission must tear down iteratively");
}

#[test]
fn hidden_constructor_order_and_family_coverage_are_authenticated() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import facade (First)\nmain : Unit -> Unit\nmain () = ()\n",
        &[
            ("facade.ash", "pub import base (First)\n"),
            ("base.ash", "pub type Pair<A> =\nFirst(A)\n| Second(A)\n"),
        ],
    );
    let base = module_named(&graph, "base.ash");
    let base_summary =
        check_module(resolve_module(base, &[]).expect("the constructor base should resolve"))
            .expect("the constructor base should check")
            .into_exports();
    let facade = module_named(&graph, "facade.ash");
    let importer = module_named(&graph, "entry.ash");

    for remove_fact in [false, true] {
        let mut summary = check_module(
            resolve_with(facade, &[&base_summary]).expect("the constructor facade should resolve"),
        )
        .expect("the constructor facade should check")
        .into_exports();
        let changed = if remove_fact {
            summary.remove_first_hidden_constructor_for_test()
        } else {
            summary.corrupt_order_for_test(SummaryOrderForTest::HiddenConstructor)
        };
        assert!(
            changed,
            "the partial family should retain its hidden sibling"
        );
        let error = resolve_with(importer, &[&summary])
            .expect_err("hidden constructor closure must authenticate before local checking");
        assert_eq!(error.reason, ResolveReason::InternalState);
    }
}

#[test]
fn diamond_routes_require_complete_fact_agreement_before_route_mutation() {
    let mutations = [
        SummaryDuplicateFactForTest::Global,
        SummaryDuplicateFactForTest::GlobalValueType,
        SummaryDuplicateFactForTest::GlobalRequirementOrigin,
        SummaryDuplicateFactForTest::GlobalRequirementSpan,
        SummaryDuplicateFactForTest::Nominal,
        SummaryDuplicateFactForTest::NominalParameterOrigin,
        SummaryDuplicateFactForTest::Constructor,
        SummaryDuplicateFactForTest::ConstructorOrigin,
        SummaryDuplicateFactForTest::Interface,
        SummaryDuplicateFactForTest::InterfaceOrigin,
        SummaryDuplicateFactForTest::InterfaceSpan,
        SummaryDuplicateFactForTest::InterfaceParameterOrigin,
        SummaryDuplicateFactForTest::InterfaceMethodSpan,
        SummaryDuplicateFactForTest::InterfaceWithoutImplementationType,
        SummaryDuplicateFactForTest::Implementation,
        SummaryDuplicateFactForTest::ImplementationOrigin,
        SummaryDuplicateFactForTest::ImplementationSpan,
        SummaryDuplicateFactForTest::ImplementationHeadParameterOrigin,
        SummaryDuplicateFactForTest::ImplementationHeadArgument,
        SummaryDuplicateFactForTest::ImplementationPrerequisiteOrigin,
        SummaryDuplicateFactForTest::ImplementationPrerequisiteSpan,
        SummaryDuplicateFactForTest::ImplementationPrerequisiteType,
        SummaryDuplicateFactForTest::ImplementationMethodSpan,
        SummaryDuplicateFactForTest::OpaqueNominalKindClosure,
    ];

    for mutation in mutations {
        for reverse in [false, true] {
            let tree = TempTree::create();
            let first = if reverse { "right" } else { "left" };
            let second = if reverse { "left" } else { "right" };
            let entry = if matches!(
                mutation,
                SummaryDuplicateFactForTest::Implementation
                    | SummaryDuplicateFactForTest::ImplementationOrigin
                    | SummaryDuplicateFactForTest::ImplementationSpan
                    | SummaryDuplicateFactForTest::ImplementationHeadParameterOrigin
                    | SummaryDuplicateFactForTest::ImplementationHeadArgument
                    | SummaryDuplicateFactForTest::ImplementationPrerequisiteOrigin
                    | SummaryDuplicateFactForTest::ImplementationPrerequisiteSpan
                    | SummaryDuplicateFactForTest::ImplementationPrerequisiteType
                    | SummaryDuplicateFactForTest::ImplementationMethodSpan
            ) {
                format!("import {first} (impl Observe)\nimport {second} (impl Observe)\n")
            } else {
                format!("import {first} as First\nimport {second} as Second\n")
            };
            let facade = concat!(
                "pub import base (value, generic, Box, Capsule, Observe, observe, ",
                "Witness, witness, impl Observe)\n",
            );
            let graph = load(
                &tree,
                &entry,
                &[
                    ("left.ash", facade),
                    ("right.ash", facade),
                    (
                        "base.ash",
                        concat!(
                            "pub type Box<A> = Box(A)\n\n",
                            "pub opaque type Capsule<F : Type -> Type> = Seal(Unit)\n\n",
                            "pub value : Unit -> Unit\nvalue item = item\n\n",
                            "pub generic<A> : A -> A where Observe<A>\n",
                            "generic value = value\n\n",
                            "pub interface Observe<A> {\nobserve : A -> Unit\n}\n\n",
                            "pub interface Witness<A> {\nwitness : A -> A\n}\n\n",
                            "pub impl Observe<Box<Int>> {\nobserve value = ()\n}\n",
                            "\npub impl<F : Type -> Type> Observe<Capsule<F>> where Witness<Int> {\n",
                            "observe value = ()\n}\n",
                        ),
                    ),
                ],
            );
            let base = module_named(&graph, "base.ash");
            let base_summary =
                check_module(resolve_module(base, &[]).expect("the diamond base should resolve"))
                    .expect("the diamond base should check")
                    .into_exports();
            let left = module_named(&graph, "left.ash");
            let left_summary = check_module(
                resolve_with(left, &[&base_summary]).expect("the left facade should resolve"),
            )
            .expect("the left facade should check")
            .into_exports();
            let right = module_named(&graph, "right.ash");
            let mut right_summary = check_module(
                resolve_with(right, &[&base_summary]).expect("the right facade should resolve"),
            )
            .expect("the right facade should check")
            .into_exports();
            let importer = module_named(&graph, "entry.ash");
            let clean = if reverse {
                [&right_summary, &left_summary]
            } else {
                [&left_summary, &right_summary]
            };
            resolve_with(importer, &clean).expect("exact diamond mirrors should deduplicate");

            let changed = right_summary.corrupt_first_duplicate_fact_for_test(mutation);
            assert!(
                changed,
                "the selected diamond carrier {mutation:?} should be present (reverse={reverse})",
            );
            right_summary
                .authenticate(
                    &mut TypeWorkBudget::default(),
                    &mut crate::interface::InterfaceConstraintBudget::default(),
                )
                .unwrap_or_else(|error| {
                    panic!(
                        "alternate {mutation:?} must authenticate (reverse={reverse}): {error:?}"
                    )
                });
            let conflicting = if reverse {
                [&right_summary, &left_summary]
            } else {
                [&left_summary, &right_summary]
            };
            let error = match resolve_with(importer, &conflicting) {
                Err(error) => error,
                Ok(_) => {
                    panic!("conflicting diamond fact {mutation:?} must fail at the second route")
                }
            };
            assert_eq!(error.reason, ResolveReason::InternalState);
            let second_import = importer.dependencies()[1].import_span();
            let primary = error.primary.span();
            assert_eq!(primary.source(), second_import.source());
            assert!(
                primary.range().start() >= second_import.range().start()
                    && primary.range().end() <= second_import.range().end(),
                "the retained first route must remain the comparison baseline",
            );
        }
    }
}

#[test]
fn hidden_diamond_facts_require_complete_provenance_agreement_in_dependency_order() {
    let mutations = [
        SummaryHiddenDiamondMutationForTest::NominalOrigin,
        SummaryHiddenDiamondMutationForTest::NominalParameterOrigin,
        SummaryHiddenDiamondMutationForTest::ConstructorOrigin,
        SummaryHiddenDiamondMutationForTest::InterfaceOrigin,
        SummaryHiddenDiamondMutationForTest::InterfaceParameterOrigin,
        SummaryHiddenDiamondMutationForTest::InterfaceMethodOrigin,
        SummaryHiddenDiamondMutationForTest::InterfaceMethodSpan,
        SummaryHiddenDiamondMutationForTest::InterfaceMethodType,
    ];
    for mutation in mutations {
        for reverse in [false, true] {
            let tree = TempTree::create();
            let first = if reverse { "right" } else { "left" };
            let second = if reverse { "left" } else { "right" };
            let entry = format!("import {first} as First\nimport {second} as Second\n");
            let graph = load(
                &tree,
                &entry,
                &[
                    (
                        "left.ash",
                        "pub import base (expose, First, impl Observe)\n",
                    ),
                    (
                        "right.ash",
                        "pub import base (expose, First, impl Observe)\n",
                    ),
                    (
                        "base.ash",
                        concat!(
                            "type Secret<F : Type -> Type> = Secret(F<Int>)\n\n",
                            "pub expose<F : Type -> Type> : Secret<F> -> Secret<F>\n",
                            "expose value = value\n\n",
                            "pub type Wrap<A> =\nFirst(A)\n| Second(A)\n\n",
                            "pub interface Observe<A> {\nobserve : A -> A\n}\n\n",
                            "pub interface Witness<A> {\nwitness : A -> A\n}\n\n",
                            "pub impl<A> Observe<Wrap<A>> where Witness<A> {\n",
                            "observe value = value\n}\n",
                        ),
                    ),
                ],
            );
            let base = module_named(&graph, "base.ash");
            let base_summary = check_module(
                resolve_module(base, &[]).expect("the hidden diamond base should resolve"),
            )
            .expect("the hidden diamond base should check")
            .into_exports();
            let left = module_named(&graph, "left.ash");
            let left_summary = check_module(
                resolve_with(left, &[&base_summary]).expect("the left facade should resolve"),
            )
            .expect("the left facade should check")
            .into_exports();
            let right = module_named(&graph, "right.ash");
            let mut right_summary = check_module(
                resolve_with(right, &[&base_summary]).expect("the right facade should resolve"),
            )
            .expect("the right facade should check")
            .into_exports();
            assert!(
                right_summary.corrupt_hidden_diamond_fact_for_test(mutation),
                "the hidden diamond carrier {mutation:?} should exist",
            );
            right_summary
                .authenticate(
                    &mut TypeWorkBudget::default(),
                    &mut crate::interface::InterfaceConstraintBudget::default(),
                )
                .unwrap_or_else(|error| panic!("hidden alternate {mutation:?} must authenticate (reverse={reverse}): {error:?}"));
            let importer = module_named(&graph, "entry.ash");
            let summaries = if reverse {
                [&right_summary, &left_summary]
            } else {
                [&left_summary, &right_summary]
            };
            let error = match resolve_with(importer, &summaries) {
                Err(error) => error,
                Ok(_) => panic!(
                    "hidden diamond provenance {mutation:?} must agree before route mutation (reverse={reverse})",
                ),
            };
            assert_eq!(error.reason, ResolveReason::InternalState, "{mutation:?}");
            let second_import = importer.dependencies()[1].import_span();
            assert_eq!(error.primary.span().source(), second_import.source());
        }
    }
}

#[test]
fn interface_and_implementation_only_diamonds_compare_hidden_nominal_closure() {
    let cases = [
        (
            "interface",
            "pub import base (Observe)\n",
            concat!(
                "type Secret<A> = Secret(A)\n\n",
                "pub interface Observe<A> {\nobserve : Secret<A> -> Secret<A>\n}\n",
            ),
        ),
        (
            "implementation",
            "pub import base (First, impl Observe)\n",
            concat!(
                "pub type Marker = First\n\n",
                "type Secret<A> = Secret(A)\n\n",
                "pub interface Observe<A> {\nobserve : A -> A\n}\n\n",
                "pub impl<A> Observe<Secret<A>> {\nobserve value = value\n}\n",
            ),
        ),
    ];
    for (carrier, facade, base_source) in cases {
        for reverse in [false, true] {
            let tree = TempTree::create();
            let first = if reverse { "right" } else { "left" };
            let second = if reverse { "left" } else { "right" };
            let entry = format!("import {first} as First\nimport {second} as Second\n");
            let graph = load(
                &tree,
                &entry,
                &[
                    ("left.ash", facade),
                    ("right.ash", facade),
                    ("base.ash", base_source),
                ],
            );
            let base = module_named(&graph, "base.ash");
            let base_summary = check_module(
                resolve_module(base, &[]).expect("the nominal-closure base should resolve"),
            )
            .expect("the nominal-closure base should check")
            .into_exports();
            let left = module_named(&graph, "left.ash");
            let left_summary = check_module(
                resolve_with(left, &[&base_summary]).expect("the left facade should resolve"),
            )
            .expect("the left facade should check")
            .into_exports();
            let right = module_named(&graph, "right.ash");
            let mut right_summary = check_module(
                resolve_with(right, &[&base_summary]).expect("the right facade should resolve"),
            )
            .expect("the right facade should check")
            .into_exports();
            assert!(right_summary.corrupt_hidden_diamond_fact_for_test(
                SummaryHiddenDiamondMutationForTest::NominalOrigin,
            ));
            right_summary
                .authenticate(
                    &mut TypeWorkBudget::default(),
                    &mut crate::interface::InterfaceConstraintBudget::default(),
                )
                .expect("the coherent alternate closure should authenticate independently");

            let importer = module_named(&graph, "entry.ash");
            let summaries = if reverse {
                [&right_summary, &left_summary]
            } else {
                [&left_summary, &right_summary]
            };
            let error = resolve_with(importer, &summaries).expect_err(&format!(
                "the {carrier}-only diamond should reject conflicting nominal provenance",
            ));
            assert_eq!(error.reason, ResolveReason::InternalState, "{carrier}");
            assert_eq!(
                error.primary.span().source(),
                importer.dependencies()[1].import_span().source(),
                "{carrier}",
            );
        }
    }
}

#[test]
fn targeted_constructor_diamond_authenticates_its_hidden_owner_before_deduplication() {
    for reverse in [false, true] {
        let tree = TempTree::create();
        let first = if reverse { "right" } else { "left" };
        let second = if reverse { "left" } else { "right" };
        let entry = format!(
            "import {first} (First as FirstRoute)\nimport {second} (First as SecondRoute)\n"
        );
        let graph = load(
            &tree,
            &entry,
            &[
                ("left.ash", "pub import base (First)\n"),
                ("right.ash", "pub import base (First)\n"),
                ("base.ash", "pub type Pair<A> =\nFirst(A)\n| Second(A)\n"),
            ],
        );
        let base = module_named(&graph, "base.ash");
        let base_summary =
            check_module(resolve_module(base, &[]).expect("the Pair base should resolve"))
                .expect("the Pair base should check")
                .into_exports();
        let left = module_named(&graph, "left.ash");
        let left_summary = check_module(
            resolve_with(left, &[&base_summary])
                .expect("the left constructor facade should resolve"),
        )
        .expect("the left constructor facade should check")
        .into_exports();
        let right = module_named(&graph, "right.ash");
        let mut right_summary = check_module(
            resolve_with(right, &[&base_summary])
                .expect("the right constructor facade should resolve"),
        )
        .expect("the right constructor facade should check")
        .into_exports();
        let importer = module_named(&graph, "entry.ash");
        let clean = if reverse {
            [&right_summary, &left_summary]
        } else {
            [&left_summary, &right_summary]
        };
        resolve_with(importer, &clean)
            .expect("exact targeted constructor and hidden-owner mirrors should deduplicate");

        assert!(right_summary.corrupt_hidden_diamond_fact_for_test(
            SummaryHiddenDiamondMutationForTest::NominalOrigin
        ));
        right_summary
            .authenticate(
                &mut TypeWorkBudget::default(),
                &mut crate::interface::InterfaceConstraintBudget::default(),
            )
            .expect("the coherent hidden owner mutation should authenticate independently");
        let conflicting = if reverse {
            [&right_summary, &left_summary]
        } else {
            [&left_summary, &right_summary]
        };
        let error = resolve_with(importer, &conflicting)
            .expect_err("constructor deduplication must not skip its hidden owner mirror");
        assert_eq!(error.reason, ResolveReason::InternalState);
        let second_import = importer.dependencies()[1].import_span();
        assert_eq!(error.primary.span().source(), second_import.source());
    }
}

#[test]
fn duplicate_constructor_payload_routes_compare_foreign_nominal_provenance() {
    for reverse in [false, true] {
        let tree = TempTree::create();
        let first = if reverse { "right" } else { "left" };
        let second = if reverse { "left" } else { "right" };
        let entry =
            format!("import {first} (Wrap as FirstWrap)\nimport {second} (Wrap as SecondWrap)\n",);
        let graph = load(
            &tree,
            &entry,
            &[
                ("left.ash", "pub import base (Container, Wrap)\n"),
                ("right.ash", "pub import base (Container, Wrap)\n"),
                (
                    "base.ash",
                    "type Secret = Secret\n\npub type Container = Wrap(Secret)\n",
                ),
            ],
        );
        let base = module_named(&graph, "base.ash");
        let base_summary = check_module(
            resolve_module(base, &[]).expect("the constructor-payload base should resolve"),
        )
        .expect("the constructor-payload base should check")
        .into_exports();
        let left = module_named(&graph, "left.ash");
        let left_summary = check_module(
            resolve_with(left, &[&base_summary]).expect("the left facade should resolve"),
        )
        .expect("the left facade should check")
        .into_exports();
        let right = module_named(&graph, "right.ash");
        let mut right_summary = check_module(
            resolve_with(right, &[&base_summary]).expect("the right facade should resolve"),
        )
        .expect("the right facade should check")
        .into_exports();
        assert!(right_summary.corrupt_hidden_diamond_fact_for_test(
            SummaryHiddenDiamondMutationForTest::NominalOrigin,
        ));
        right_summary
            .authenticate(
                &mut TypeWorkBudget::default(),
                &mut crate::interface::InterfaceConstraintBudget::default(),
            )
            .expect("the coherent foreign-payload closure should authenticate independently");

        let importer = module_named(&graph, "entry.ash");
        let summaries = if reverse {
            [&right_summary, &left_summary]
        } else {
            [&left_summary, &right_summary]
        };
        let error = resolve_with(importer, &summaries)
            .expect_err("duplicate constructors should compare foreign payload nominal provenance");
        assert_eq!(error.reason, ResolveReason::InternalState);
        assert_eq!(
            error.primary.span().source(),
            importer.dependencies()[1].import_span().source(),
        );
    }
}

#[test]
fn unselected_non_decreasing_prerequisite_fails_summary_admission() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (marker)\nmain : Unit -> Unit\nmain () = marker(())\n",
        &[(
            "dependency.ash",
            concat!(
                "pub type Option<A> =\nNone\n| Some(A)\n\n",
                "pub interface Parent<A> {\nparent : A -> A\n}\n\n",
                "pub interface Child<A> {\nchild : A -> A\n}\n\n",
                "pub impl<A> Child<Option<A>> where Parent<A> {\n",
                "child value = value\n}\n\n",
                "pub marker : Unit -> Unit\nmarker value = value\n",
            ),
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let mut summary = check_module(
        resolve_module(dependency, &[]).expect("the prerequisite dependency should resolve"),
    )
    .expect("the decreasing prerequisite should check")
    .into_exports();
    assert!(summary.replace_first_implementation_prerequisite_with_head_for_test());
    let importer = module_named(&graph, "entry.ash");

    let error = resolve_with(importer, &[&summary])
        .expect_err("a non-strict imported prerequisite must fail summary admission");

    assert_eq!(error.reason, ResolveReason::InternalState);
}

#[test]
fn unselected_kind_valid_bare_variable_head_fails_summary_admission() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (marker)\nmain : Unit -> Unit\nmain () = marker(())\n",
        &[(
            "dependency.ash",
            concat!(
                "pub type Option<A> =\nNone\n| Some(A)\n\n",
                "pub interface Observe<A> {\nobserve : A -> Unit\n}\n\n",
                "pub impl<A> Observe<Option<A>> {\nobserve value = ()\n}\n\n",
                "pub marker : Unit -> Unit\nmarker value = value\n",
            ),
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let mut summary = check_module(
        resolve_module(dependency, &[]).expect("the generic dependency should resolve"),
    )
    .expect("the concrete generic head should check")
    .into_exports();
    assert!(summary.replace_first_implementation_head_with_bare_parameter_for_test());
    let importer = module_named(&graph, "entry.ash");

    let error = resolve_with(importer, &[&summary])
        .expect_err("a bare-variable imported implementation head must fail admission");

    assert_eq!(error.reason, ResolveReason::InternalState);
}

#[test]
fn unselected_kind_valid_orphan_head_fails_summary_admission() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (marker)\nmain : Unit -> Unit\nmain () = marker(())\n",
        &[
            (
                "dependency.ash",
                concat!(
                    "pub import base (Foreign, Observe, observe)\n\n",
                    "pub type Local = Local\n\n",
                    "pub impl Observe<Local> {\nobserve value = ()\n}\n\n",
                    "pub marker : Unit -> Unit\nmarker value = value\n",
                ),
            ),
            (
                "base.ash",
                concat!(
                    "pub type Foreign = Foreign\n\n",
                    "pub interface Observe<A> {\nobserve : A -> Unit\n}\n",
                ),
            ),
        ],
    );
    let base = module_named(&graph, "base.ash");
    let base_summary =
        check_module(resolve_module(base, &[]).expect("the foreign base should resolve"))
            .expect("the foreign base should check")
            .into_exports();
    let dependency = module_named(&graph, "dependency.ash");
    let mut summary = check_module(
        resolve_with(dependency, &[&base_summary])
            .expect("the local orphan-safe impl should resolve"),
    )
    .expect("the local nominal should satisfy the owner rule")
    .into_exports();
    assert!(summary.replace_first_implementation_head_with_foreign_nominal_for_test());
    let importer = module_named(&graph, "entry.ash");

    let error = resolve_with(importer, &[&summary])
        .expect_err("a foreign-interface/foreign-nominal impl must fail admission");

    assert_eq!(error.reason, ResolveReason::InternalState);
}

fn equational(module: &ResolvedModule, index: usize) -> &crate::resolved::ResolvedEquationalGlobal {
    let ResolvedDefinitionKind::Equational(definition) = &module.definitions()[index].kind else {
        panic!("expected an equational definition");
    };
    definition
}

fn nominal_function_parts(ty: &Type) -> (NominalTypeId, NominalTypeId) {
    let Type::Function(domain, codomain) = ty else {
        panic!("expected a function type");
    };
    let Type::Nominal(domain) = domain.as_ref() else {
        panic!("expected a nominal domain");
    };
    let Type::Nominal(codomain) = codomain.as_ref() else {
        panic!("expected a nominal codomain");
    };
    (*domain, *codomain)
}

#[test]
fn qualified_import_resolves_term_type_and_constructor_identities() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency as Dep\n",
            "main : Dep.Box -> Dep.Box\n",
            "main Dep.Box = Dep.answer\n",
        ),
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let binder = BinderId::resolved(dependency.id(), 7);
    let nominal = NominalTypeId::new(dependency.id(), 3);
    let constructor = ConstructorId::new(nominal, 0);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![("answer", binder, Type::Unit, origin.clone())],
        vec![(
            "Box",
            nominal,
            ExportedTypeAccess::Transparent,
            origin.clone(),
        )],
        vec![("Box", constructor, None, origin)],
        vec![],
    );

    let resolved = resolve_with(importer, &[&summary]).expect("qualified imports should resolve");
    let definition = equational(&resolved, 0);
    assert_eq!(
        nominal_function_parts(&definition.interface.annotation.ty),
        (nominal, nominal)
    );
    assert!(matches!(
        definition.equations[0].patterns[0].kind,
        ResolvedPatternKind::Constructor {
            constructor: found,
            ..
        } if found == constructor
    ));
    assert!(matches!(
        definition.equations[0].body.kind,
        ResolvedExprKind::Occurrence(ref occurrence)
            if occurrence.global_binder() == Some(binder)
    ));
}

#[test]
fn targeted_import_rename_preserves_the_exported_binder_identity() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (answer as renamed)\nmain : Unit -> Unit\nmain () = renamed\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let binder = BinderId::resolved(dependency.id(), 9);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![(
            "answer",
            binder,
            Type::Unit,
            Origin::Source(dependency.surface().span),
        )],
        vec![],
        vec![],
        vec![],
    );

    let resolved = resolve_with(importer, &[&summary]).expect("the rename should resolve");
    assert!(matches!(
        equational(&resolved, 0).equations[0].body.kind,
        ResolvedExprKind::Occurrence(ref occurrence)
            if occurrence.spelling == "renamed"
                && occurrence.global_binder() == Some(binder)
    ));
}

#[test]
fn one_targeted_selector_imports_same_spelled_type_and_constructor() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (Box)\nmain : Unit -> Box\nmain () = Box\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let nominal = NominalTypeId::new(dependency.id(), 0);
    let constructor = ConstructorId::new(nominal, 0);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![],
        vec![(
            "Box",
            nominal,
            ExportedTypeAccess::Transparent,
            origin.clone(),
        )],
        vec![("Box", constructor, None, origin)],
        vec![],
    );

    let resolved = resolve_with(importer, &[&summary]).expect("both namespaces should resolve");
    let definition = equational(&resolved, 0);
    let Type::Function(_, codomain) = &definition.interface.annotation.ty else {
        panic!("expected a function type");
    };
    assert_eq!(codomain.as_ref(), &Type::Nominal(nominal));
    assert!(matches!(
        definition.equations[0].body.kind,
        ResolvedExprKind::Constructor(ref occurrence) if occurrence.constructor == constructor
    ));
}

#[test]
fn duplicate_targeted_selector_is_an_import_conflict() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (answer, answer)\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![(
            "answer",
            BinderId::resolved(dependency.id(), 0),
            Type::Unit,
            Origin::Source(dependency.surface().span),
        )],
        vec![],
        vec![],
        vec![],
    );

    let error = resolve_with(importer, &[&summary]).expect_err("the duplicate should conflict");
    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn bindings_from_distinct_imports_cannot_silently_shadow() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import first (answer)\nimport second (answer)\n",
        &[("first.ash", ""), ("second.ash", "")],
    );
    let importer = module_named(&graph, "entry.ash");
    let first = module_named(&graph, "first.ash");
    let second = module_named(&graph, "second.ash");
    let first_summary = ExportSummary::test_fixture(
        first.id(),
        vec![(
            "answer",
            BinderId::resolved(first.id(), 0),
            Type::Unit,
            Origin::Source(first.surface().span),
        )],
        vec![],
        vec![],
        vec![],
    );
    let second_summary = ExportSummary::test_fixture(
        second.id(),
        vec![(
            "answer",
            BinderId::resolved(second.id(), 0),
            Type::Unit,
            Origin::Source(second.surface().span),
        )],
        vec![],
        vec![],
        vec![],
    );

    let error = resolve_with(importer, &[&first_summary, &second_summary])
        .expect_err("the second import should conflict");
    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn targeted_term_and_constructor_cannot_share_a_renamed_expression_spelling() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import first (answer as Clash)\nimport second (Some as Clash)\n",
        &[("first.ash", ""), ("second.ash", "")],
    );
    let importer = module_named(&graph, "entry.ash");
    let first = module_named(&graph, "first.ash");
    let second = module_named(&graph, "second.ash");
    let first_summary = ExportSummary::test_fixture(
        first.id(),
        vec![(
            "answer",
            BinderId::resolved(first.id(), 0),
            Type::Unit,
            Origin::Source(first.surface().span),
        )],
        vec![],
        vec![],
        vec![],
    );
    let nominal = NominalTypeId::new(second.id(), 0);
    let second_summary = ExportSummary::test_fixture(
        second.id(),
        vec![],
        vec![(
            "Option",
            nominal,
            ExportedTypeAccess::Transparent,
            Origin::Source(second.surface().span),
        )],
        vec![(
            "Some",
            ConstructorId::new(nominal, 0),
            None,
            Origin::Source(second.surface().span),
        )],
        vec![],
    );

    let error = resolve_with(importer, &[&first_summary, &second_summary])
        .expect_err("term and constructor imports must not shadow in expression scope");
    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn targeted_term_cannot_shadow_a_local_constructor() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (answer as Some)\ntype Option = Some\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![(
            "answer",
            BinderId::resolved(dependency.id(), 0),
            Type::Unit,
            Origin::Source(dependency.surface().span),
        )],
        vec![],
        vec![],
        vec![],
    );

    let error = resolve_with(importer, &[&summary])
        .expect_err("an imported term must not shadow a local constructor");
    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn targeted_import_cannot_shadow_a_local_global() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (main)\nmain : Unit -> Unit\nmain value = value\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![(
            "main",
            BinderId::resolved(dependency.id(), 0),
            Type::Unit,
            Origin::Source(dependency.surface().span),
        )],
        vec![],
        vec![],
        vec![],
    );

    let error = resolve_with(importer, &[&summary]).expect_err("the local should conflict");
    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn local_interface_cannot_shadow_a_qualified_module_alias() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency as Equal\ninterface Equal<A> {\nequal : A -> Bool\n}\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = ExportSummary::test_fixture(dependency.id(), vec![], vec![], vec![], vec![]);

    let error = resolve_with(importer, &[&summary])
        .expect_err("a local interface must not shadow a qualified module alias");

    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn local_interface_cannot_shadow_a_targeted_nominal() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (Equal)\ninterface Equal<A> {\nequal : A -> Bool\n}\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let nominal = NominalTypeId::new(dependency.id(), 0);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![],
        vec![(
            "Equal",
            nominal,
            ExportedTypeAccess::Transparent,
            origin.clone(),
        )],
        vec![("Equal", ConstructorId::new(nominal, 0), None, origin)],
        vec![],
    );

    let error = resolve_with(importer, &[&summary])
        .expect_err("a local interface must not shadow a targeted nominal");

    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn local_method_cannot_shadow_a_targeted_global_term() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (equal)\ninterface Equal<A> {\nequal : A -> Bool\n}\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![(
            "equal",
            BinderId::resolved(dependency.id(), 0),
            Type::Unit,
            Origin::Source(dependency.surface().span),
        )],
        vec![],
        vec![],
        vec![],
    );

    let error = resolve_with(importer, &[&summary])
        .expect_err("a local method must not shadow a targeted global term");

    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn local_method_cannot_shadow_a_targeted_constructor_under_a_lowercase_rename() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (Some as equal)\ninterface Equal<A> {\nequal : A -> Bool\n}\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let nominal = NominalTypeId::new(dependency.id(), 0);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![],
        vec![(
            "Option",
            nominal,
            ExportedTypeAccess::Transparent,
            origin.clone(),
        )],
        vec![("Some", ConstructorId::new(nominal, 0), None, origin)],
        vec![],
    );

    let error = resolve_with(importer, &[&summary])
        .expect_err("a local method must not shadow a targeted renamed constructor");

    assert_eq!(error.reason, ResolveReason::ImportConflict);
}

#[test]
fn imported_non_interface_targets_report_interface_kind() {
    for (entry, label) in [
        (
            "import dependency (Make)\nvalue : Unit -> Bool where Make<Int>\nvalue () = true\n",
            "targeted constructor",
        ),
        (
            "import dependency as Dep\nvalue : Unit -> Bool where Dep.Make<Int>\nvalue () = true\n",
            "qualified constructor",
        ),
        (
            "import dependency as Dep\nvalue : Unit -> Bool where Dep<Int>\nvalue () = true\n",
            "unqualified module alias",
        ),
    ] {
        let tree = TempTree::create();
        let graph = load(&tree, entry, &[("dependency.ash", "")]);
        let dependency = module_named(&graph, "dependency.ash");
        let importer = module_named(&graph, "entry.ash");
        let nominal = NominalTypeId::new(dependency.id(), 0);
        let origin = Origin::Source(dependency.surface().span);
        let summary = ExportSummary::test_fixture(
            dependency.id(),
            vec![],
            vec![(
                "Carrier",
                nominal,
                ExportedTypeAccess::Transparent,
                origin.clone(),
            )],
            vec![("Make", ConstructorId::new(nominal, 0), None, origin)],
            vec![],
        );

        let error = resolve_with(importer, &[&summary])
            .expect_err("a resolved non-interface target should fail its sort check");

        assert_eq!(error.reason, ResolveReason::InterfaceKind, "{label}");
    }
}

#[test]
fn local_interface_and_nominal_report_a_duplicate_type() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "type Equal = Equal\n\ninterface Equal<A> {\nequal : A -> Bool\n}\n",
        &[],
    );
    let importer = module_named(&graph, "entry.ash");

    let error = resolve_with(importer, &[])
        .expect_err("a local interface and nominal cannot share a type namespace name");

    assert_eq!(error.reason, ResolveReason::DuplicateType);
}

#[test]
fn local_method_and_global_report_a_duplicate_global() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "interface Equal<A> {\nequal : A -> Bool\n}\n\nequal : Unit -> Bool\nequal () = true\n",
        &[],
    );
    let importer = module_named(&graph, "entry.ash");

    let error = resolve_with(importer, &[])
        .expect_err("a local method and global cannot share a term namespace name");

    assert_eq!(error.reason, ResolveReason::DuplicateGlobal);
}

#[test]
fn a_renamed_imported_type_does_not_conflict_with_a_local_global() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency (Token as token)\n",
            "token : Unit -> Unit\n",
            "token value = value\n",
        ),
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let nominal = NominalTypeId::new(dependency.id(), 0);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture_with_access(
        dependency.id(),
        vec![],
        vec![("Token", nominal, ExportedTypeAccess::Opaque, origin)],
        vec![],
        vec![],
        vec![("<Token>", Origin::Source(dependency.surface().span))],
        vec![],
    );

    resolve_with(importer, &[&summary])
        .expect("the nominal and expression namespaces should remain distinct");
}

#[test]
fn qualified_import_charges_withheld_namespace_retention() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency as Dependency\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary =
        ExportSummary::test_fixture(dependency.id(), vec![], vec![], vec![], vec!["private"]);
    let dependencies = importer
        .dependencies()
        .iter()
        .map(|edge| DependencyExports::new(edge, &summary).expect("matching summary"))
        .collect::<Vec<_>>();
    let mut resolver = Resolver::with_type_work(importer.id(), TypeWorkBudget::with_limit(1));

    let error = resolver
        .install_imports(importer.surface(), &dependencies)
        .expect_err("two withheld namespace entries should exceed one retained unit");

    assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
    assert!(resolver.module_aliases.is_empty());
}

#[test]
fn selecting_a_withheld_private_spelling_reports_unavailable_export() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (secret)\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = ExportSummary::test_fixture_with_access(
        dependency.id(),
        vec![],
        vec![],
        vec![],
        vec!["secret"],
        vec![],
        vec![],
    );

    let error = resolve_with(importer, &[&summary]).expect_err("private export should fail");
    assert_eq!(error.reason, ResolveReason::UnavailableExport);
}

#[test]
fn diamond_consumers_preserve_one_shared_binder_and_nominal_identity() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import left as Left\nimport right as Right\n",
        &[
            (
                "left.ash",
                concat!(
                    "import shared as Shared\n",
                    "left : Shared.Token -> Shared.Token\n",
                    "left value = Shared.identity\n",
                ),
            ),
            (
                "right.ash",
                concat!(
                    "import shared as Shared\n",
                    "right : Shared.Token -> Shared.Token\n",
                    "right value = Shared.identity\n",
                ),
            ),
            ("shared.ash", ""),
        ],
    );
    let shared = module_named(&graph, "shared.ash");
    let left = module_named(&graph, "left.ash");
    let right = module_named(&graph, "right.ash");
    let binder = BinderId::resolved(shared.id(), 4);
    let nominal = NominalTypeId::new(shared.id(), 2);
    let origin = Origin::Source(shared.surface().span);
    let summary = ExportSummary::test_fixture_with_access(
        shared.id(),
        vec![("identity", binder, Type::Unit, origin.clone())],
        vec![("Token", nominal, ExportedTypeAccess::Opaque, origin)],
        vec![],
        vec![],
        vec![("<Token>", Origin::Source(shared.surface().span))],
        vec![],
    );

    let left_resolved = resolve_with(left, &[&summary]).expect("left should resolve");
    let right_resolved = resolve_with(right, &[&summary]).expect("right should resolve");
    let left_definition = equational(&left_resolved, 0);
    let right_definition = equational(&right_resolved, 0);

    assert_eq!(
        nominal_function_parts(&left_definition.interface.annotation.ty),
        (nominal, nominal)
    );
    assert_eq!(
        nominal_function_parts(&right_definition.interface.annotation.ty),
        (nominal, nominal)
    );
    assert!(matches!(
        left_definition.equations[0].body.kind,
        ResolvedExprKind::Occurrence(ref occurrence)
            if occurrence.global_binder() == Some(binder)
    ));
    assert!(matches!(
        right_definition.equations[0].body.kind,
        ResolvedExprKind::Occurrence(ref occurrence)
            if occurrence.global_binder() == Some(binder)
    ));
}

fn opaque_nominal_summary(
    dependency: &LoadedModule,
    nominal_spelling: &str,
    opaque_constructors: Vec<&str>,
) -> ExportSummary {
    let nominal = NominalTypeId::new(dependency.id(), 0);
    let origin = Origin::Source(dependency.surface().span);
    ExportSummary::test_fixture_with_access(
        dependency.id(),
        vec![],
        vec![(
            nominal_spelling,
            nominal,
            ExportedTypeAccess::Opaque,
            origin.clone(),
        )],
        vec![],
        vec![],
        opaque_constructors
            .into_iter()
            .map(|spelling| (spelling, origin.clone()))
            .collect(),
        vec![],
    )
}

#[test]
fn targeted_import_of_an_opaque_constructor_reports_opaque_access() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (Seal)\n",
        &[("dependency.ash", "pub opaque type Token = Seal(Int)\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = opaque_nominal_summary(dependency, "Token", vec!["Seal"]);

    let error = resolve_with(importer, &[&summary])
        .expect_err("an opaque constructor cannot be imported by name");

    assert_eq!(error.reason, ResolveReason::OpaqueConstructor);
}

#[test]
fn qualified_construction_of_an_opaque_type_reports_opaque_access() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency as Dep\n",
            "main : Unit -> Dep.Token\n",
            "main () = Dep.Seal(1)\n",
        ),
        &[("dependency.ash", "pub opaque type Token = Seal(Int)\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = opaque_nominal_summary(dependency, "Token", vec!["Seal"]);

    let error = resolve_with(importer, &[&summary])
        .expect_err("qualified construction must not inspect an opaque type");

    assert_eq!(error.reason, ResolveReason::OpaqueConstructor);
    assert_eq!(error.related.len(), 1);
    assert_eq!(
        error.related[0].span().source(),
        dependency.surface().span.source()
    );
}

#[test]
fn qualified_pattern_on_an_opaque_type_reports_opaque_access() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency as Dep\n",
            "main : Dep.Token -> Unit\n",
            "main Dep.Seal(_) = ()\n",
        ),
        &[("dependency.ash", "pub opaque type Token = Seal(Int)\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = opaque_nominal_summary(dependency, "Token", vec!["Seal"]);

    let error = resolve_with(importer, &[&summary])
        .expect_err("qualified matching must not inspect an opaque type");

    assert_eq!(error.reason, ResolveReason::OpaqueConstructor);
}

#[test]
fn a_private_type_name_remains_unavailable_to_a_qualified_importer() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency as Dep\n",
            "main : Dep.Hidden -> Unit\n",
            "main _ = ()\n",
        ),
        &[("dependency.ash", "type Hidden = Hidden(Int)\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary =
        ExportSummary::test_fixture(dependency.id(), vec![], vec![], vec![], vec!["Hidden"]);

    let error = resolve_with(importer, &[&summary])
        .expect_err("a private type name must not enter the qualified namespace");

    assert_eq!(error.reason, ResolveReason::UnavailableExport);
}

#[test]
fn a_public_opaque_type_name_is_available_to_a_qualified_importer() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency as Dep\n",
            "main : Dep.Token -> Dep.Token\n",
            "main value = value\n",
        ),
        &[("dependency.ash", "pub opaque type Token = Seal(Int)\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let nominal = NominalTypeId::new(dependency.id(), 0);
    let summary = opaque_nominal_summary(dependency, "Token", vec!["Seal"]);

    let resolved =
        resolve_with(importer, &[&summary]).expect("an opaque nominal name should be usable");

    assert_eq!(
        nominal_function_parts(&equational(&resolved, 0).interface.annotation.ty),
        (nominal, nominal)
    );
}

#[test]
fn a_public_transparent_constructor_is_available_in_terms_and_patterns() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency as Dep\n",
            "main : Dep.Token -> Dep.Token\n",
            "main Dep.Seal(value) = Dep.Seal(value)\n",
        ),
        &[("dependency.ash", "pub type Token = Seal(Int)\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let nominal = NominalTypeId::new(dependency.id(), 0);
    let constructor = ConstructorId::new(nominal, 0);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![],
        vec![(
            "Token",
            nominal,
            ExportedTypeAccess::Transparent,
            origin.clone(),
        )],
        vec![("Seal", constructor, Some(Type::Int), origin)],
        vec![],
    );

    let resolved = resolve_with(importer, &[&summary])
        .expect("a transparent constructor should resolve in terms and patterns");
    let definition = equational(&resolved, 0);

    assert!(matches!(
        definition.equations[0].patterns[0].kind,
        ResolvedPatternKind::Constructor {
            constructor: found,
            ..
        } if found == constructor
    ));
    let ResolvedExprKind::Apply(application) = &definition.equations[0].body.kind else {
        panic!("expected a constructor application");
    };
    assert!(matches!(
        application.function.kind,
        ResolvedExprKind::Constructor(ref occurrence) if occurrence.constructor == constructor
    ));
}

#[test]
fn targeting_only_a_transparent_constructor_retains_its_owner_metadata() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency (Seal)\n",
            "main : Unit -> Unit\n",
            "main () = Seal(1)\n",
        ),
        &[("dependency.ash", "pub type Token = Seal(Int)\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let nominal = NominalTypeId::new(dependency.id(), 0);
    let constructor = ConstructorId::new(nominal, 0);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![],
        vec![(
            "Token",
            nominal,
            ExportedTypeAccess::Transparent,
            origin.clone(),
        )],
        vec![("Seal", constructor, Some(Type::Int), origin)],
        vec![],
    );

    let resolved = resolve_with(importer, &[&summary])
        .expect("a targeted constructor should retain its semantic owner");

    assert!(resolved.imported_facts().nominal(nominal).is_some());
    assert!(resolved.imported_facts().constructor(constructor).is_some());
}

#[test]
fn same_spelled_opaque_type_imports_but_its_constructor_remains_inaccessible() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency (Token)\n",
            "main : Unit -> Token\n",
            "main () = Token\n",
        ),
        &[("dependency.ash", "pub opaque type Token = Token\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let nominal = NominalTypeId::new(dependency.id(), 0);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture_with_access(
        dependency.id(),
        vec![],
        vec![("Token", nominal, ExportedTypeAccess::Opaque, origin.clone())],
        vec![],
        vec![],
        vec![("Token", origin)],
        vec![],
    );

    let error = resolve_with(importer, &[&summary])
        .expect_err("the selector imports the type but not its opaque constructor");

    assert_eq!(error.reason, ResolveReason::OpaqueConstructor);
}

fn hidden_scheme_summary(
    dependency: &LoadedModule,
    term_spelling: &str,
    hidden_spelling: &str,
    declaration: u32,
) -> (ExportSummary, NominalTypeId) {
    let hidden = NominalTypeId::new(dependency.id(), declaration);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture_with_access(
        dependency.id(),
        vec![(
            term_spelling,
            BinderId::resolved(dependency.id(), declaration),
            Type::Function(Box::new(Type::Unit), Box::new(Type::Nominal(hidden))),
            origin.clone(),
        )],
        vec![],
        vec![],
        vec![hidden_spelling],
        vec![],
        vec![(hidden_spelling, hidden, 0, true, origin)],
    );
    (summary, hidden)
}

#[test]
fn a_hidden_nominal_in_a_public_scheme_is_retained_without_becoming_nameable() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency (make)\n",
            "main : Unit -> Unit\n",
            "main () = make\n",
        ),
        &[(
            "dependency.ash",
            concat!(
                "type Hidden = Hidden(Int)\n",
                "pub make : Unit -> Hidden\n",
                "make () = Hidden(1)\n",
            ),
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let (summary, hidden) = hidden_scheme_summary(dependency, "make", "Hidden", 0);

    let resolved = resolve_with(importer, &[&summary])
        .expect("the public term should carry its hidden nominal identity");

    let hidden_fact = resolved
        .imported_facts()
        .nominal(hidden)
        .expect("the hidden identity should remain available to checking");
    assert_eq!(
        hidden_fact.display_name("Dependency"),
        "Dependency.<private Hidden>"
    );
    assert!(summary.nominal("Hidden").is_none());

    let naming_tree = TempTree::create();
    let naming_graph = load(
        &naming_tree,
        concat!(
            "import dependency as Dep\n",
            "name_hidden : Dep.Hidden -> Unit\n",
            "name_hidden _ = ()\n",
        ),
        &[(
            "dependency.ash",
            concat!(
                "type Hidden = Hidden(Int)\n",
                "pub make : Unit -> Hidden\n",
                "make () = Hidden(1)\n",
            ),
        )],
    );
    let naming_dependency = module_named(&naming_graph, "dependency.ash");
    let naming_importer = module_named(&naming_graph, "entry.ash");
    let (naming_summary, _) = hidden_scheme_summary(naming_dependency, "make", "Hidden", 0);
    let error = resolve_with(naming_importer, &[&naming_summary])
        .expect_err("hidden metadata must not add a source type binding");

    assert_eq!(error.reason, ResolveReason::UnavailableExport);
}

#[test]
fn a_public_transparent_nominal_in_a_targeted_term_scheme_is_hidden() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (make)\nmain : Unit -> Unit\nmain () = ()\n",
        &[(
            "dependency.ash",
            "pub type Choice =\nFirst\n| Second\npub make : Unit -> Choice\nmake () = First\n",
        )],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let choice = NominalTypeId::new(dependency.id(), 0);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![(
            "make",
            BinderId::resolved(dependency.id(), 0),
            Type::Function(Box::new(Type::Unit), Box::new(Type::Nominal(choice))),
            origin.clone(),
        )],
        vec![(
            "Choice",
            choice,
            ExportedTypeAccess::Transparent,
            origin.clone(),
        )],
        vec![
            ("First", ConstructorId::new(choice, 0), None, origin.clone()),
            ("Second", ConstructorId::new(choice, 1), None, origin),
        ],
        vec![],
    );

    let resolved = resolve_with(importer, &[&summary])
        .expect("a targeted term should retain its transparent nominal identity");
    let fact = resolved
        .imported_facts()
        .nominal(choice)
        .expect("the scheme nominal should be retained");

    assert_eq!(fact.access, ImportedTypeAccess::Hidden);
    assert!(fact.constructors.is_empty());
}

#[test]
fn scheme_only_nominal_retention_charges_only_hidden_metadata() {
    let tree = TempTree::create();
    let graph = load(&tree, "", &[]);
    let module = module_named(&graph, "entry.ash");
    let nominal = NominalTypeId::new(module.id(), 0);
    let constructors = (0..32)
        .map(|index| ConstructorId::new(nominal, index))
        .collect::<Vec<_>>();
    let origin = Origin::Source(module.surface().span);
    // A payload-free hidden nominal authenticates one defining-count mirror
    // and retains one source-order record; its unretained family adds no work.
    let mut exact = Resolver::with_type_work(module.id(), TypeWorkBudget::with_limit(2));

    exact
        .retain_scheme_nominal_fact(
            ImportedNominalFactRef {
                declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                representation: None,
                representation_provenance: None,
                id: nominal,
                parameter_count: 0,
                constructor_count: constructors.len(),
                parameters: &[],
                constructors: &constructors,
                access: ImportedTypeAccess::Transparent,
                display_spelling: Some("Wide"),
                display_is_private: false,
                origin: &origin,
            },
            module.surface().span,
        )
        .expect("unretained constructors must not consume hidden-metadata work");
    assert!(
        exact
            .imported
            .nominal(nominal)
            .is_some_and(|fact| fact.constructors.is_empty())
    );

    let parameter = ResolvedTypeVariable {
        id: TypeVariableId::resolved(module.id(), 0),
        spelling: "A".to_owned(),
        kind: crate::types::Kind::Type,
        origin: origin.clone(),
    };
    // One kinded parameter adds one binder record and one Kind node, for
    // 1 count mirror + 1 order record + 1 binder record + 1 Kind node = 4.
    let mut short = Resolver::with_type_work(module.id(), TypeWorkBudget::with_limit(3));
    let error = short
        .retain_scheme_nominal_fact(
            ImportedNominalFactRef {
                declaration_kind: crate::resolved::ResolvedNominalDeclarationKind::Data,
                representation: None,
                representation_provenance: None,
                id: nominal,
                parameter_count: 1,
                constructor_count: constructors.len(),
                parameters: std::slice::from_ref(&parameter),
                constructors: &constructors,
                access: ImportedTypeAccess::Transparent,
                display_spelling: Some("Wide"),
                display_is_private: false,
                origin: &origin,
            },
            module.surface().span,
        )
        .expect_err("one retained kinded parameter needs the third metadata unit");

    assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
}

#[test]
fn hidden_nominals_from_distinct_dependencies_retain_distinct_identities() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import first as First\nimport second as Second\n",
        &[
            (
                "first.ash",
                "type Hidden = Hidden\npub make : Unit -> Hidden\nmake () = Hidden\n",
            ),
            (
                "second.ash",
                "type Hidden = Hidden\npub make : Unit -> Hidden\nmake () = Hidden\n",
            ),
        ],
    );
    let importer = module_named(&graph, "entry.ash");
    let first = module_named(&graph, "first.ash");
    let second = module_named(&graph, "second.ash");
    let (first_summary, first_hidden) = hidden_scheme_summary(first, "make", "Hidden", 0);
    let (second_summary, second_hidden) = hidden_scheme_summary(second, "make", "Hidden", 0);

    let resolved = resolve_with(importer, &[&first_summary, &second_summary])
        .expect("both hidden nominal facts should survive import installation");

    assert_ne!(first_hidden, second_hidden);
    assert!(resolved.imported_facts().nominal(first_hidden).is_some());
    assert!(resolved.imported_facts().nominal(second_hidden).is_some());
}

#[test]
fn direct_nominal_access_upgrades_the_same_identity_reached_hidden_in_either_import_order() {
    for entry_text in [
        "import carrier as Carrier\nimport owner as Owner\n",
        "import owner as Owner\nimport carrier as Carrier\n",
    ] {
        let tree = TempTree::create();
        let graph = load(
            &tree,
            entry_text,
            &[
                ("carrier.ash", "import owner as Owner\n"),
                ("owner.ash", "pub type Token = Token\n"),
            ],
        );
        let importer = module_named(&graph, "entry.ash");
        let carrier = module_named(&graph, "carrier.ash");
        let owner = module_named(&graph, "owner.ash");
        let token = NominalTypeId::new(owner.id(), 0);
        let owner_origin = Origin::Source(owner.surface().span);
        let carrier_summary = ExportSummary::test_fixture_with_access(
            carrier.id(),
            vec![(
                "carry",
                BinderId::resolved(carrier.id(), 0),
                Type::Function(
                    Box::new(Type::Nominal(token)),
                    Box::new(Type::Nominal(token)),
                ),
                Origin::Source(carrier.surface().span),
            )],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![("Token", token, 0, false, owner_origin.clone())],
        );
        let owner_summary = ExportSummary::test_fixture(
            owner.id(),
            vec![],
            vec![(
                "Token",
                token,
                ExportedTypeAccess::Transparent,
                owner_origin.clone(),
            )],
            vec![("Token", ConstructorId::new(token, 0), None, owner_origin)],
            vec![],
        );
        let summaries = if entry_text.starts_with("import carrier") {
            vec![&carrier_summary, &owner_summary]
        } else {
            vec![&owner_summary, &carrier_summary]
        };

        let resolved = resolve_with(importer, &summaries)
            .expect("access should merge by identity rather than first route");
        let fact = resolved
            .imported_facts()
            .nominal(token)
            .expect("the shared identity should be retained");

        assert_eq!(fact.access, ImportedTypeAccess::Transparent);
        assert_eq!(fact.display_spelling.as_deref(), Some("Token"));
    }
}

#[test]
fn withheld_type_and_constructor_facts_with_one_spelling_keep_their_namespaces() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency as Dep\nmain : Dep.Foo -> Unit\nmain _ = ()\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let owner = NominalTypeId::new(dependency.id(), 0);
    let owner_origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture_with_access(
        dependency.id(),
        vec![],
        vec![(
            "Token",
            owner,
            ExportedTypeAccess::Opaque,
            owner_origin.clone(),
        )],
        vec![],
        vec!["Foo"],
        vec![("Foo", owner_origin)],
        vec![],
    );

    let type_error = resolve_with(importer, &[&summary])
        .expect_err("the private nominal must remain unavailable");
    assert_eq!(type_error.reason, ResolveReason::UnavailableExport);

    let expression_tree = TempTree::create();
    let expression_graph = load(
        &expression_tree,
        "import dependency as Dep\nmain : Unit -> Unit\nmain () = Dep.Foo\n",
        &[("dependency.ash", "")],
    );
    let expression_dependency = module_named(&expression_graph, "dependency.ash");
    let expression_importer = module_named(&expression_graph, "entry.ash");
    let expression_owner = NominalTypeId::new(expression_dependency.id(), 0);
    let expression_origin = Origin::Source(expression_dependency.surface().span);
    let expression_summary = ExportSummary::test_fixture_with_access(
        expression_dependency.id(),
        vec![],
        vec![(
            "Token",
            expression_owner,
            ExportedTypeAccess::Opaque,
            expression_origin.clone(),
        )],
        vec![],
        vec!["Foo"],
        vec![("Foo", expression_origin)],
        vec![],
    );

    let constructor_error = resolve_with(expression_importer, &[&expression_summary])
        .expect_err("the opaque constructor must retain its own denial");
    assert_eq!(constructor_error.reason, ResolveReason::OpaqueConstructor);
}

#[test]
fn a_local_constructor_wins_over_a_targeted_opaque_marker_with_the_same_spelling() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        concat!(
            "import dependency (Token as Clash)\n",
            "type Local = Clash\n",
            "main : Local -> Local\n",
            "main Clash = Clash\n",
        ),
        &[("dependency.ash", "pub opaque type Token = Token\n")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let summary = opaque_nominal_summary(dependency, "Token", vec!["Token"]);

    resolve_with(importer, &[&summary])
        .expect("an accessible local constructor must take precedence over a denial marker");
}

#[test]
fn targeted_public_constructor_does_not_block_a_same_spelled_type_parameter() {
    let tree = TempTree::create();
    let graph = load(
        &tree,
        "import dependency (Foo)\nmain : Foo -> Unit\nmain _ = ()\n",
        &[("dependency.ash", "")],
    );
    let dependency = module_named(&graph, "dependency.ash");
    let importer = module_named(&graph, "entry.ash");
    let owner = NominalTypeId::new(dependency.id(), 1);
    let constructor = ConstructorId::new(owner, 0);
    let origin = Origin::Source(dependency.surface().span);
    let summary = ExportSummary::test_fixture(
        dependency.id(),
        vec![],
        vec![(
            "Bar",
            owner,
            ExportedTypeAccess::Transparent,
            origin.clone(),
        )],
        vec![("Foo", constructor, None, origin)],
        vec!["Foo"],
    );

    let resolved = resolve_with(importer, &[&summary])
        .expect("withheld diagnostic metadata must not bind the type namespace");
    let definition = equational(&resolved, 0);

    assert_eq!(definition.interface.type_parameters.len(), 1);
    assert!(matches!(
        definition.interface.annotation.ty,
        Type::Function(ref domain, _) if matches!(domain.as_ref(), Type::Variable(_))
    ));
}
