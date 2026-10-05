use ash::{
    driver::{PipelineFailure, RunConfiguration, run_path},
    elaborate::check_module,
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
fn copying_sqlite_session_executes_through_public_foreign_runtime() {
    assert_copying_sqlite_session("entry.ash");
}

#[test]
fn local_resource_definitions_execute_through_public_foreign_runtime() {
    assert_copying_sqlite_session("local-entry.ash");
}

fn assert_copying_sqlite_session(name: &str) {
    use ash::driver::run_path_with_foreign_runtime;
    use ash::foreign::runtime::ForeignRuntime;
    use ash_foreign_adapter::{Event, Observations, sqlite_binding};
    use std::sync::Arc;

    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
        sqlite_manifest(ForeignRegistrationId::new(2)).unwrap(),
    ])
    .unwrap();
    let observations = Observations::default();
    let binding = sqlite_binding(
        Arc::clone(registrations.get("@foreign.sqlite").unwrap()),
        observations.clone(),
    )
    .unwrap();
    let mut runtime = ForeignRuntime::new(vec![binding]).unwrap();
    let result = run_path_with_foreign_runtime(
        RunConfiguration {
            entry: fixture(name),
            roots: ModuleRoots::empty().with_foreign_registrations(registrations),
        },
        &mut runtime,
    )
    .unwrap_or_else(|failure| panic!("{name}: {failure:?}"));
    assert_eq!(
        result.value_display(),
        "Completed(Completed(Ok(42), Closed), Closed)"
    );
    for (operation, count) in [
        ("open", 1),
        ("prepare", 1),
        ("bind_int64", 1),
        ("step", 2),
        ("column_int64", 1),
        ("finalize", 1),
        ("close", 1),
    ] {
        assert_eq!(
            observations.calls(operation),
            count,
            "native call count for {operation}"
        );
    }
    let events = observations.events();
    assert!(
        !events
            .iter()
            .any(|event| matches!(event, Event::FaultInjected { .. }))
    );
    let position = |name| {
        events
            .iter()
            .position(|event| {
                matches!(
                    event, Event::Call { operation, code: 0 } if *operation == name,
                )
            })
            .unwrap()
    };
    assert!(position("finalize") < position("close"));
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn repeated_and_simultaneous_sqlite_scopes_resolve_their_actual_activations() {
    use ash::driver::run_path_with_foreign_runtime;
    use ash::foreign::runtime::ForeignRuntime;
    use ash_foreign_adapter::{Event, Observations, sqlite_binding};
    use std::sync::Arc;

    let completed = "Completed(Completed(Ok(42), Closed), Closed)";
    for (name, expected, opens) in [
        (
            "repeated-entry.ash",
            format!("({completed}, {completed})"),
            2,
        ),
        ("simultaneous-entry.ash", completed.to_owned(), 1),
    ] {
        let registrations = ForeignRegistrations::new([
            provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
            sqlite_manifest(ForeignRegistrationId::new(2)).unwrap(),
        ])
        .unwrap();
        let observations = Observations::default();
        let binding = sqlite_binding(
            Arc::clone(registrations.get("@foreign.sqlite").unwrap()),
            observations.clone(),
        )
        .unwrap();
        let mut runtime = ForeignRuntime::new(vec![binding]).unwrap();
        let result = run_path_with_foreign_runtime(
            RunConfiguration {
                entry: fixture(name),
                roots: ModuleRoots::empty().with_foreign_registrations(registrations),
            },
            &mut runtime,
        )
        .unwrap_or_else(|failure| panic!("{name}: {failure:?}"));
        assert_eq!(result.value_display(), expected, "{name}");
        assert_eq!(observations.calls("open"), opens, "{name}");
        assert_eq!(observations.calls("close"), opens, "{name}");
        for operation in ["prepare", "bind_int64", "finalize"] {
            assert_eq!(observations.calls(operation), 2, "{name}: {operation}");
        }
        assert_eq!(observations.calls("step"), 4, "{name}");
        assert_eq!(observations.calls("column_int64"), 2, "{name}");
        assert!(
            !observations
                .events()
                .iter()
                .any(|event| matches!(event, Event::FaultInjected { .. }))
        );
        assert_eq!(runtime.retained_owner_count(), 0, "{name}");
    }
}

#[test]
fn refused_statement_acquisition_executes_no_statement_body_or_finish() {
    use ash::driver::run_path_with_foreign_runtime;
    use ash::foreign::runtime::ForeignRuntime;
    use ash_foreign_adapter::{Event, Observations, sqlite_binding};
    use std::sync::Arc;
    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
        sqlite_manifest(ForeignRegistrationId::new(2)).unwrap(),
    ])
    .unwrap();
    let observations = Observations::default();
    let binding = sqlite_binding(
        Arc::clone(registrations.get("@foreign.sqlite").unwrap()),
        observations.clone(),
    )
    .unwrap();
    let mut runtime = ForeignRuntime::new(vec![binding]).unwrap();
    let result = run_path_with_foreign_runtime(
        RunConfiguration {
            entry: fixture("refused-entry.ash"),
            roots: ModuleRoots::empty().with_foreign_registrations(registrations),
        },
        &mut runtime,
    )
    .unwrap();
    assert_eq!(
        result.value_display(),
        "Completed(NotAcquired(EmptySql), Closed)"
    );
    assert_eq!(observations.calls("open"), 1);
    assert_eq!(observations.calls("prepare"), 1);
    assert_eq!(observations.calls("bind_int64"), 0);
    assert_eq!(observations.calls("finalize"), 0);
    assert_eq!(observations.calls("close"), 1);
    assert!(
        !observations
            .events()
            .iter()
            .any(|event| matches!(event, Event::FaultInjected { .. }))
    );
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn resource_initializer_executes_once_in_the_preceding_scope() {
    use ash::driver::run_path_with_foreign_runtime;
    use ash::foreign::runtime::ForeignRuntime;
    use ash_foreign_adapter::{Observations, sqlite_binding};
    use std::sync::Arc;
    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
        sqlite_manifest(ForeignRegistrationId::new(2)).unwrap(),
    ])
    .unwrap();
    let observations = Observations::default();
    let binding = sqlite_binding(
        Arc::clone(registrations.get("@foreign.sqlite").unwrap()),
        observations.clone(),
    )
    .unwrap();
    let mut runtime = ForeignRuntime::new(vec![binding]).unwrap();
    let result = run_path_with_foreign_runtime(
        RunConfiguration {
            entry: fixture("initializer-once-entry.ash"),
            roots: ModuleRoots::empty().with_foreign_registrations(registrations),
        },
        &mut runtime,
    )
    .unwrap();
    assert_eq!(result.value_display(), "(Completed(42, Closed), 1)");
    assert_eq!(observations.calls("open"), 1);
    assert_eq!(observations.calls("close"), 1);
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn imported_resource_report_dependencies_do_not_require_a_client_type_annotation() {
    use ash::driver::run_path_with_foreign_runtime;
    use ash::foreign::runtime::ForeignRuntime;
    use ash_foreign_adapter::{Observations, sqlite_binding};
    use std::sync::Arc;
    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
        sqlite_manifest(ForeignRegistrationId::new(2)).unwrap(),
    ])
    .unwrap();
    let observations = Observations::default();
    let binding = sqlite_binding(
        Arc::clone(registrations.get("@foreign.sqlite").unwrap()),
        observations.clone(),
    )
    .unwrap();
    let mut runtime = ForeignRuntime::new(vec![binding]).unwrap();
    let result = run_path_with_foreign_runtime(
        RunConfiguration {
            entry: fixture("hidden-report-entry.ash"),
            roots: ModuleRoots::empty().with_foreign_registrations(registrations),
        },
        &mut runtime,
    )
    .unwrap();
    assert_eq!(result.value_display(), "42");
    assert_eq!(observations.calls("open"), 1);
    assert_eq!(observations.calls("close"), 1);
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn static_foreign_registration_does_not_authorize_native_execution() {
    let roots = ModuleRoots::empty().with_foreign_registrations(
        ForeignRegistrations::new([
            provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
            sqlite_manifest(ForeignRegistrationId::new(2)).unwrap(),
        ])
        .unwrap(),
    );
    let failure = run_path(RunConfiguration {
        entry: fixture("entry.ash"),
        roots,
    })
    .expect_err("an executable binding is required before native acquisition");
    assert!(!failure.is_source_rejection());
    assert!(
        matches!(
            failure.pipeline_failure(),
            Some(PipelineFailure::Runtime(
                ash::eval::RuntimeFailure::ForeignBinding
            ))
        ),
        "missing executable authority must reject before acquisition: {failure:?}"
    );

    use ash::driver::run_path_with_foreign_runtime;
    use ash::foreign::runtime::ForeignRuntime;
    use ash_foreign_adapter::{Observations, sqlite_binding};
    use std::sync::Arc;
    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
        sqlite_manifest(ForeignRegistrationId::new(2)).unwrap(),
    ])
    .unwrap();
    // Equal schema, registration coordinates and spelling do not authenticate
    // a separately authored allocation as the original source registration.
    let substitute = Arc::new(sqlite_manifest(ForeignRegistrationId::new(2)).unwrap());
    assert_eq!(
        substitute.as_ref(),
        registrations.get("@foreign.sqlite").unwrap().as_ref()
    );
    let observations = Observations::default();
    let binding = sqlite_binding(substitute, observations.clone()).unwrap();
    let mut runtime = ForeignRuntime::new(vec![binding]).unwrap();
    let failure = run_path_with_foreign_runtime(
        RunConfiguration {
            entry: fixture("entry.ash"),
            roots: ModuleRoots::empty().with_foreign_registrations(registrations),
        },
        &mut runtime,
    )
    .expect_err("equal names and schemas cannot substitute executable authority");
    assert!(
        matches!(
            failure.pipeline_failure(),
            Some(PipelineFailure::Runtime(
                ash::eval::RuntimeFailure::ForeignBinding
            ))
        ),
        "{failure:?}"
    );
    assert_eq!(observations.calls("open"), 0);
    assert_eq!(runtime.retained_owner_count(), 0);
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
