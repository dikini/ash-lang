use ash::{
    driver::{PipelineFailure, RunConfiguration, run_path},
    elaborate::{ElaborationFailure, TypeError, check_module},
    foreign::{ForeignRegistrations, provider_manifest, sqlite_manifest},
    lexer::lex,
    module::{ForeignRegistrationId, ModuleRoots, load_module_graph},
    parser::{ProjectionError, ResourceFailure, STRUCTURAL_DEPTH_LIMIT, parse, project_module},
    resolve::{DependencyExports, resolve_module},
    resolved::{CheckedModule, ResolvedDefinitionKind, ResolvedExprKind},
    source::SourceFile,
};
use std::{fs, path::PathBuf};

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/provider-experiments/sqlite-copying")
        .join(name)
}

#[test]
fn copying_sqlite_public_driver_stops_at_pending_resource_admission() {
    let roots = ModuleRoots::empty().with_foreign_registrations(
        ForeignRegistrations::new([
            provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
            sqlite_manifest(ForeignRegistrationId::new(2)).unwrap(),
        ])
        .unwrap(),
    );
    // Declaration checking is covered separately below. The client still reaches
    // the pending resource-instance admission boundary; S-01 runtime is pending.
    let graph = load_module_graph(&fixture("entry.ash"), &roots).unwrap();
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
        let resolved = resolve_module(loaded, &dependencies).unwrap();
        if loaded.id() == graph.entry() {
            let main = resolved
                .definitions()
                .iter()
                .find_map(|definition| {
                    let ResolvedDefinitionKind::Equational(global) = &definition.kind else {
                        return None;
                    };
                    (global.interface.name.spelling == "main").then_some(global)
                })
                .unwrap();
            assert!(matches!(
                main.equations[0].body.kind,
                ResolvedExprKind::ProviderResource(_)
            ));
            assert!(matches!(
                check_module(resolved),
                Err(TypeError::Internal(ElaborationFailure::InvalidState))
            ));
        } else {
            checked.push(check_module(resolved).unwrap());
        }
    }
    let failure = run_path(RunConfiguration {
        entry: fixture("entry.ash"),
        roots,
    })
    .expect_err("resource-instance admission and native execution remain pending");
    assert_eq!(failure.reason_code(), "type.internal");
    assert!(!failure.is_source_rejection());
    assert!(
        matches!(
            failure.pipeline_failure(),
            Some(PipelineFailure::Typing(TypeError::Internal(
                ElaborationFailure::InvalidState
            )))
        ),
        "expected the pending resource-instance checker guard: {failure:?}"
    );
}

#[test]
fn sqlite_library_declarations_check_against_registered_dependencies() {
    let roots = ModuleRoots::empty().with_foreign_registrations(
        ForeignRegistrations::new([
            provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
            sqlite_manifest(ForeignRegistrationId::new(2)).unwrap(),
        ])
        .unwrap(),
    );
    let graph = load_module_graph(&fixture("sqlite.ash"), &roots).unwrap();
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
        let resolved = resolve_module(loaded, &dependencies).unwrap();
        if loaded.canonical_path() == fixture("sqlite.ash").canonicalize().unwrap() {
            assert_eq!(resolved.resources().len(), 2);
            assert_eq!(resolved.resources()[0].handlers.len(), 1);
            assert_eq!(resolved.resources()[1].handlers.len(), 3);
            for resource in resolved.resources() {
                assert!(checked.iter().any(|module| {
                    module
                        .registry()
                        .foreign_effect(resource.interpreted.instance.effect())
                }));
                let ResolvedExprKind::Perform(finish) = &resource.finish.kind else {
                    panic!("selected finisher must request its registered native operation")
                };
                assert!(checked.iter().any(|module| {
                    module
                        .registry()
                        .foreign_operation(finish.operation)
                        .is_some()
                }));
            }
            let helpers = resolved
                .definitions()
                .iter()
                .map(|definition| {
                    let ResolvedDefinitionKind::Equational(global) = &definition.kind else {
                        panic!("pure configuration helpers use equational globals")
                    };
                    assert_eq!(global.equations[0].patterns.len(), 1);
                    global.interface.name.spelling.as_str()
                })
                .collect::<Vec<_>>();
            assert_eq!(helpers, ["memory", "select_parameter"]);
            let checked_library = check_module(resolved).unwrap();
            assert_eq!(
                checked_library
                    .exports()
                    .resource_types()
                    .map(|(name, _)| name)
                    .collect::<Vec<_>>(),
                ["Connection", "Statement"]
            );
            return;
        }
        checked.push(check_module(resolved).unwrap());
    }
    panic!("loaded graph must contain the source SQLite library")
}

#[test]
fn first_copying_sqlite_source_bundle_parses_with_the_ordinary_frontend() {
    for name in ["provider.ash", "sqlite.ash", "entry.ash"] {
        let path = fixture(name);
        let source = SourceFile::new(
            path.display().to_string(),
            fs::read_to_string(&path).unwrap(),
        )
        .unwrap();
        let tree = parse(lex(&source).unwrap());
        assert!(
            tree.parse_diagnostics().is_empty(),
            "{name}: {:?}",
            tree.parse_diagnostics()
        );
        project_module(&source, &tree).unwrap_or_else(|error| panic!("{name}: {error:?}"));
    }
}

#[test]
fn original_four_match_client_exhausts_projection_depth_before_provider_checking() {
    let path = fixture("entry-deep.ash");
    let source = SourceFile::new(
        path.display().to_string(),
        fs::read_to_string(path).unwrap(),
    )
    .unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(tree.parse_diagnostics().is_empty());
    assert_eq!(
        project_module(&source, &tree),
        Err(ProjectionError::ResourceLimit(
            ResourceFailure::StructuralDepth {
                limit: STRUCTURAL_DEPTH_LIMIT
            }
        ))
    );
}
