use ash::module::{ModuleRoots, load_module_graph};
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
#[test]
fn missing_foreign_registration_rejects_without_filesystem_fallback() {
    let tree = Tree::new();
    tree.write("sqlite.ash", "pub type Bytes = Forged\n");
    let entry = tree.write(
        "entry.ash",
        "import @foreign.sqlite as Native\nmain : Unit -> Unit\nmain () = ()\n",
    );
    let failure = load_module_graph(&entry, &ModuleRoots::empty()).unwrap_err();
    assert!(
        format!("{failure:?}").contains("UnknownForeign"),
        "{failure:?}"
    );
}
use ash::{
    elaborate::check_module,
    foreign::*,
    module::ForeignRegistrationId,
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
};
fn mock_schema() -> ForeignManifestSchema {
    let ty = |name: &str, params: &[&str], opaque, cases: &[(&str, Option<&str>)]| {
        ForeignTypeDeclaration {
            name: name.into(),
            parameters: params.iter().map(|s| s.to_string()).collect(),
            category: if opaque {
                ForeignTypeCategory::State
            } else {
                ForeignTypeCategory::Data
            },
            constructors: cases
                .iter()
                .map(|(name, payload)| ForeignConstructorDeclaration {
                    name: name.to_string(),
                    payload: payload.map(str::to_owned),
                })
                .collect(),
        }
    };
    ForeignManifestSchema {
        types: vec![
            ty("Token", &["R"], true, &[]),
            ty("Fault", &[], false, &[("Oops", None)]),
            ty(
                "Start",
                &["State", "E"],
                false,
                &[("Started", Some("State")), ("Denied", Some("E"))],
            ),
            ty(
                "Stop",
                &["State", "E"],
                false,
                &[
                    ("Stopped", None),
                    ("StopFailed", Some("E")),
                    ("Kept", Some("State, E")),
                ],
            ),
        ],
        effects: vec![ForeignEffectDeclaration {
            name: "Requests".into(),
            parameters: vec!["R".into()],
            operations: vec![
                ForeignOperationDeclaration {
                    name: "begin".into(),
                    signature: "Int -> Start<Token<R>, Fault>".into(),
                    role: ash::module::ForeignOperationRole::Acquire,
                    owned_identity_position: 0,
                    state_operands: vec![],
                    retained_arguments: vec![],
                    result: ForeignResultRelation::Acquire {
                        state: "Token".into(),
                        error: "Fault".into(),
                        report: "Start".into(),
                        retained_parameters: vec![],
                    },
                },
                ForeignOperationDeclaration {
                    name: "read".into(),
                    signature: "Token<R> -> Int".into(),
                    role: ash::module::ForeignOperationRole::Borrow,
                    owned_identity_position: 0,
                    state_operands: vec![vec![]],
                    retained_arguments: vec![],
                    result: ForeignResultRelation::Independent,
                },
                ForeignOperationDeclaration {
                    name: "end".into(),
                    signature: "Token<R> -> Stop<Token<R>, Fault>".into(),
                    role: ash::module::ForeignOperationRole::Finish,
                    owned_identity_position: 0,
                    state_operands: vec![vec![]],
                    retained_arguments: vec![],
                    result: ForeignResultRelation::Finish {
                        state: "Token".into(),
                        error: "Fault".into(),
                        report: "Stop".into(),
                    },
                },
            ],
        }],
        state_access: None,
        foundation: None,
    }
}
fn mock() -> ForeignManifest {
    ForeignManifest::new(
        "@foreign.mock.renamed",
        ForeignRegistrationId::new(101),
        mock_schema(),
    )
    .unwrap()
}
fn roots(manifest: ForeignManifest) -> ModuleRoots {
    ModuleRoots::empty().with_foreign_registrations(ForeignRegistrations::new([manifest]).unwrap())
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
#[test]
fn renamed_registration_is_passive_and_keeps_defining_authority_through_facades() {
    let tree = Tree::new();
    tree.write(
        "facade.ash",
        "pub import @foreign.mock.renamed (Token, Requests, Fault, Oops)\n",
    );
    let entry=tree.write("entry.ash","import facade as Facade\nimport @foreign.mock.renamed as Alias\nmain : Unit -> Facade.Fault\nmain () = Alias.Oops\n");
    let roots = roots(mock());
    let graph = load_module_graph(&entry, &roots).unwrap();
    assert_eq!(graph.modules().len(), 3);
    let native = graph
        .modules()
        .iter()
        .find(|module| module.foreign_admission().is_some())
        .unwrap();
    let checked = check_graph(&graph);
    let defining = checked
        .iter()
        .find(|module| module.module() == native.id())
        .unwrap();
    let registration = defining.registry().foreign_modules().next().unwrap();
    assert_eq!(registration.states.len(), 1);
    assert_eq!(registration.operations.len(), 3);
    for module in &checked {
        let exported = module.exports().foreign_modules().next().unwrap();
        assert_eq!(exported, registration);
    }
    let observation =
        ash::driver::run_path(ash::driver::RunConfiguration { entry, roots }).unwrap();
    assert_eq!(observation.value_display(), "Oops");
}
#[test]
fn duplicate_paths_and_registration_ids_reject_atomically() {
    assert!(ForeignRegistrations::new([mock(), mock()]).is_err());
    let other = ForeignManifest::new(
        "@foreign.other",
        ForeignRegistrationId::new(101),
        mock_schema(),
    )
    .unwrap();
    assert!(ForeignRegistrations::new([mock(), other]).is_err());
}
#[test]
fn invalid_paths_roles_and_source_injection_reject() {
    assert!(ForeignManifest::new("sqlite", ForeignRegistrationId::new(1), mock_schema()).is_err());
    let mut schema = mock_schema();
    schema.effects[0].operations[0].role = ash::module::ForeignOperationRole::Borrow;
    assert!(ForeignManifest::new("@foreign.bad", ForeignRegistrationId::new(1), schema).is_err());
    let mut schema = mock_schema();
    schema.effects[0].operations[0].signature = "Int -> Int\nmain () = 42".into();
    assert!(ForeignManifest::new("@foreign.bad", ForeignRegistrationId::new(1), schema).is_err());
}
#[test]
fn source_copy_has_no_registration_authority() {
    let tree = Tree::new();
    let entry = tree.write("entry.ash", mock().source());
    let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    assert!(graph.modules()[0].foreign_admission().is_none());
    let checked = check_graph(&graph);
    assert_eq!(checked[0].registry().foreign_modules().count(), 0);
    assert_eq!(checked[0].exports().foreign_modules().count(), 0);
}
#[test]
fn metadata_changes_alter_digest_and_identical_manifests_are_deterministic() {
    assert_eq!(mock().digest(), mock().digest());
    let mut schema = mock_schema();
    schema.effects[0].operations[1].retained_arguments.push(0);
    let changed = ForeignManifest::new(
        "@foreign.mock.renamed",
        ForeignRegistrationId::new(101),
        schema,
    )
    .unwrap();
    assert_ne!(changed.digest(), mock().digest());
}
#[test]
fn wrong_native_lifecycle_signature_and_owned_identity_reject_admission() {
    for change in [0, 1] {
        let tree = Tree::new();
        let entry = tree.write(
            "entry.ash",
            "import @foreign.bad as Bad\nmain : Unit -> Unit\nmain () = ()\n",
        );
        let mut schema = mock_schema();
        if change == 0 {
            schema.effects[0].operations[0].signature = "Int -> Fault".into();
        } else {
            schema.effects[0].operations[0].result = ForeignResultRelation::Acquire {
                state: "Token".into(),
                error: "Fault".into(),
                report: "Start".into(),
                retained_parameters: vec![0],
            };
        }
        let manifest =
            ForeignManifest::new("@foreign.bad", ForeignRegistrationId::new(1), schema).unwrap();
        let graph = load_module_graph(&entry, &roots(manifest)).unwrap();
        assert!(resolve_module(&graph.modules()[0], &[]).is_err());
    }
}
#[test]
fn sqlite_and_provider_passive_imports_check_and_construct_canonical_configuration() {
    let tree = Tree::new();
    tree.write(
        "provider.ash",
        "pub import @foreign.provider (StateAccess, state_of)\n",
    );
    let entry=tree.write("entry.ash","import provider as Provider\nimport @foreign.sqlite as Native\nimport @builtin.string as TextOps\nmain : Unit -> Native.OpenConfig\nmain () = Native.File (TextOps.to_utf8 \"A\")\n");
    let roots = ModuleRoots::empty().with_foreign_registrations(
        ForeignRegistrations::new([
            sqlite_manifest(ForeignRegistrationId::new(1)).unwrap(),
            provider_manifest(ForeignRegistrationId::new(2)).unwrap(),
        ])
        .unwrap(),
    );
    let graph = load_module_graph(&entry, &roots).unwrap();
    let checked = check_graph(&graph);
    let sqlite = checked
        .iter()
        .find(|module| {
            module
                .registry()
                .foreign_modules()
                .any(|fact| fact.operations.len() == 12)
        })
        .unwrap();
    let fact = sqlite.registry().foreign_modules().next().unwrap();
    assert_eq!(fact.states.len(), 2);
    assert_eq!(fact.effects.len(), 2);
    let observation =
        ash::driver::run_path(ash::driver::RunConfiguration { entry, roots }).unwrap();
    assert!(observation.value_display().contains("File"));
}
#[test]
fn ordinary_clients_cannot_call_or_interpret_registered_native_effects() {
    for (body, effects) in [
        (
            "perform Native.Requests<Int>.begin 42",
            " ! {Native.Requests<Int>}",
        ),
        (
            "handle (Native.Denied Native.Oops) with Native.Requests<Int> {\nbegin ignored => resume (Native.Denied Native.Oops)\nread ignored => resume 0\nend ignored => resume Native.Stopped\n}",
            "",
        ),
    ] {
        let tree = Tree::new();
        let entry=tree.write("entry.ash",&format!("import @foreign.mock.renamed as Native\nmain : Unit -> Native.Start<Native.Token<Int>, Native.Fault>{effects}\nmain () = {body}\n"));
        let failure = ash::driver::run_path(ash::driver::RunConfiguration {
            entry,
            roots: roots(mock()),
        })
        .unwrap_err();
        assert!(
            format!("{failure:?}").contains("ForeignPrivilegeUnavailable"),
            "{failure:?}"
        );
    }
}
#[test]
fn sealed_state_access_identity_survives_aliases_and_rejects_source_impl() {
    let tree = Tree::new();
    tree.write(
        "facade.ash",
        "pub import @foreign.provider (StateAccess as Relation, state_of as reveal)\n",
    );
    let entry=tree.write("entry.ash","import facade as Provider\nimpl Provider.Relation<Int, Int> {\nreveal value = value\n}\nmain : Unit -> Unit\nmain () = ()\n");
    let roots = roots(provider_manifest(ForeignRegistrationId::new(22)).unwrap());
    let failure =
        ash::driver::run_path(ash::driver::RunConfiguration { entry, roots }).unwrap_err();
    assert!(
        format!("{failure:?}").contains("SealedProvider"),
        "{failure:?}"
    );
}
#[test]
fn borrowed_independent_results_cannot_hide_native_states_in_data() {
    for hidden_payload in [true, false] {
        let mut schema = mock_schema();
        if hidden_payload {
            schema.types[1].constructors[0].payload = Some("Token<Int>".into());
            schema.effects[0].operations[1].signature = "Token<R> -> Fault".into();
        } else {
            schema.types.push(ForeignTypeDeclaration {
                name: "Wrapped".into(),
                parameters: vec!["T".into()],
                category: ForeignTypeCategory::Data,
                constructors: vec![ForeignConstructorDeclaration {
                    name: "Wrap".into(),
                    payload: Some("T".into()),
                }],
            });
            schema.effects[0].operations[1].signature =
                "Token<R> -> Wrapped<Wrapped<Token<R>>>".into();
        }
        let manifest =
            ForeignManifest::new("@foreign.bad", ForeignRegistrationId::new(1), schema).unwrap();
        let tree = Tree::new();
        let entry = tree.write("entry.ash", "import @foreign.bad as Bad\n");
        let graph = load_module_graph(&entry, &roots(manifest)).unwrap();
        assert!(resolve_module(&graph.modules()[0], &[]).is_err());
    }
}
#[test]
fn copied_results_and_lifecycle_errors_cannot_carry_owner_identity() {
    for lifecycle in [false, true] {
        let mut schema = mock_schema();
        if lifecycle {
            schema.types[1].constructors[0].payload = Some("Token<Int>".into());
        } else {
            schema.effects[0].operations[1].signature = "Token<R> -> R".into();
        }
        let manifest =
            ForeignManifest::new("@foreign.bad", ForeignRegistrationId::new(1), schema).unwrap();
        let tree = Tree::new();
        let entry = tree.write("entry.ash", "import @foreign.bad as Bad\n");
        let graph = load_module_graph(&entry, &roots(manifest)).unwrap();
        assert!(resolve_module(&graph.modules()[0], &[]).is_err());
    }
}
#[test]
fn ordinary_effect_facades_keep_hidden_report_kinds_without_exporting_names() {
    let tree = Tree::new();
    tree.write("native.ash", mock().source());
    tree.write("facade.ash", "pub import native (Requests)\n");
    let entry = tree.write(
        "entry.ash",
        "import facade as Facade\nmain : Unit -> Unit\nmain () = ()\n",
    );
    let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    let checked = check_graph(&graph);
    let facade = checked
        .iter()
        .find(|module| {
            graph
                .module(module.module())
                .unwrap()
                .source()
                .display_path()
                .ends_with("facade.ash")
        })
        .unwrap();
    assert!(facade.exports().effect("Requests").is_some());
    ash::driver::run_path(ash::driver::RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .unwrap();
}
#[test]
fn state_access_calls_remain_unavailable_in_ordinary_helpers_and_closures() {
    for body in [
        "Provider.reveal value",
        "{\nlet retained : Unit -> State = fn(ignored) {\nProvider.reveal value\n}\nretained ()\n}",
    ] {
        let tree = Tree::new();
        tree.write(
            "facade.ash",
            "pub import @foreign.provider (StateAccess as Relation, state_of as reveal)\n",
        );
        let entry=tree.write("entry.ash",&format!("import facade as Provider\nleak<Q, State> : Q -> State where Provider.Relation<Q, State>\nleak value = {body}\nmain : Unit -> Unit\nmain () = ()\n"));
        let failure = ash::driver::run_path(ash::driver::RunConfiguration {
            entry,
            roots: roots(provider_manifest(ForeignRegistrationId::new(22)).unwrap()),
        })
        .unwrap_err();
        let Some(ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(
            diagnostic,
        ))) = failure.pipeline_failure()
        else {
            panic!("expected a controlled-state source rejection: {failure:?}");
        };
        assert_eq!(diagnostic.reason, ash::elaborate::TypeReason::Argument);
        assert_eq!(
            diagnostic.primary.message(),
            "controlled native state is unavailable in ordinary callable types or captures"
        );
        assert!(failure.is_source_rejection());
    }
}
#[test]
fn state_access_method_values_remain_unavailable_in_ordinary_helpers() {
    let tree = Tree::new();
    tree.write(
        "facade.ash",
        "pub import @foreign.provider (StateAccess as Relation, state_of as reveal)\n",
    );
    let entry = tree.write(
        "entry.ash",
        "import facade as Provider\nleak<Q, State> : Q -> State where Provider.Relation<Q, State>\nleak value = {\nlet retained : Q -> State = Provider.reveal\nretained value\n}\nmain : Unit -> Unit\nmain () = ()\n",
    );
    let failure = ash::driver::run_path(ash::driver::RunConfiguration {
        entry,
        roots: roots(provider_manifest(ForeignRegistrationId::new(22)).unwrap()),
    })
    .unwrap_err();
    assert!(
        matches!(
            failure.pipeline_failure(),
            Some(ash::driver::PipelineFailure::Typing(
                ash::elaborate::TypeError::Internal(
                    ash::elaborate::ElaborationFailure::ForeignPrivilegeUnavailable
                )
            ))
        ),
        "{failure:?}"
    );
}
#[test]
fn source_cannot_supply_registered_state_access_with_lexical_evidence() {
    let tree = Tree::new();
    let entry=tree.write("entry.ash","import @foreign.provider as Provider\nmain : Unit -> Unit\nmain () = {\nwith Provider.StateAccess<Int, Int> {\nstate_of value = value\n}\n()\n}\n");
    let failure = ash::driver::run_path(ash::driver::RunConfiguration {
        entry,
        roots: roots(provider_manifest(ForeignRegistrationId::new(22)).unwrap()),
    })
    .unwrap_err();
    assert!(
        format!("{failure:?}").contains("SealedProvider"),
        "{failure:?}"
    );
}
#[test]
fn foreign_root_is_reserved_before_filesystem_inspection() {
    assert_eq!(
        ModuleRoots::new([("foreign", std::path::Path::new("/does/not/exist"))])
            .unwrap_err()
            .reason(),
        ash::module::ModuleReason::ReservedRoot
    );
}
#[test]
fn effect_signature_closure_does_not_export_hidden_names_or_constructors() {
    let tree = Tree::new();
    tree.write("native.ash", mock().source());
    tree.write("facade.ash", "pub import native (Requests)\n");
    for name in ["Start", "Stop", "Started", "HiddenNativeToken"] {
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
            format!("{failure:?}").contains("UnavailableExport"),
            "{failure:?}"
        );
    }
}
#[test]
fn native_state_must_have_an_owner_parameter_and_every_domain_state_is_declared() {
    for zero_owner in [false, true] {
        let mut schema = mock_schema();
        if zero_owner {
            schema.types[0].parameters.clear();
            schema.effects[0].operations = vec![ForeignOperationDeclaration {
                signature: "Token -> Int".into(),
                ..schema.effects[0].operations[1].clone()
            }];
        } else {
            schema.effects[0].operations[1].signature = "(Token<R>, Token<R>) -> Int".into();
            schema.effects[0].operations[1].state_operands = vec![vec![0]];
        }
        let manifest = ForeignManifest::new("@foreign.bad", ForeignRegistrationId::new(1), schema);
        if let Ok(manifest) = manifest {
            let tree = Tree::new();
            let entry = tree.write("entry.ash", "import @foreign.bad as Bad\n");
            let graph = load_module_graph(&entry, &roots(manifest)).unwrap();
            assert!(resolve_module(&graph.modules()[0], &[]).is_err());
        }
    }
}
#[test]
fn acquisition_cannot_omit_native_parent_lineage_from_its_retained_result() {
    for retained_parameters in [vec![], vec![0], vec![0, 1]] {
        let mut schema = mock_schema();
        schema.types[0].parameters.push("C".into());
        schema.types.push(ForeignTypeDeclaration {
            name: "Parent".into(),
            parameters: vec!["C".into()],
            category: ForeignTypeCategory::State,
            constructors: vec![],
        });
        schema.effects[0].parameters.push("C".into());
        schema.effects[0].operations = vec![ForeignOperationDeclaration {
            name: "begin".into(),
            signature: "Parent<C> -> Start<Token<R, C>, Fault>".into(),
            role: ash::module::ForeignOperationRole::Acquire,
            owned_identity_position: 0,
            state_operands: vec![vec![]],
            retained_arguments: vec![],
            result: ForeignResultRelation::Acquire {
                state: "Token".into(),
                error: "Fault".into(),
                report: "Start".into(),
                retained_parameters,
            },
        }];
        let manifest =
            ForeignManifest::new("@foreign.bad", ForeignRegistrationId::new(1), schema).unwrap();
        let tree = Tree::new();
        let entry = tree.write("entry.ash", "import @foreign.bad as Bad\n");
        let graph = load_module_graph(&entry, &roots(manifest)).unwrap();
        assert!(resolve_module(&graph.modules()[0], &[]).is_err());
    }
}

// These descriptions are passive admission preparation. Reaching the final
// refusal below does not expose Layout evidence or executable storage authority.
fn foundation_schema() -> ForeignManifestSchema {
    let mut schema = mock_schema();
    schema.types.extend([
        ForeignTypeDeclaration {
            name: "Measured".into(),
            parameters: vec!["Payload".into()],
            category: ForeignTypeCategory::LayoutWitness {
                payload_parameter: 0,
            },
            constructors: vec![],
        },
        ForeignTypeDeclaration {
            name: "Handle".into(),
            parameters: vec!["Region".into(), "Payload".into()],
            category: ForeignTypeCategory::Reference {
                owner_parameter: 0,
                payload_parameter: 1,
            },
            constructors: vec![],
        },
        ForeignTypeDeclaration {
            name: "Outcome".into(),
            parameters: vec!["Value".into()],
            category: ForeignTypeCategory::Data,
            constructors: vec![
                ForeignConstructorDeclaration {
                    name: "Reserved".into(),
                    payload: Some("Value".into()),
                },
                ForeignConstructorDeclaration {
                    name: "RejectedStorage".into(),
                    payload: Some("Fault".into()),
                },
            ],
        },
    ]);
    schema.foundation = Some(ForeignFoundationDeclaration {
        layout: ForeignLayoutDeclaration {
            name: "Metric".into(),
            parameter: "Payload".into(),
            witness: "Measured".into(),
            method: ForeignFoundationOperationDeclaration {
                name: "measure".into(),
                signature: "Unit -> Measured<Payload>".into(),
            },
        },
        storage: ForeignStorageDeclaration {
            name: "StorageRequests".into(),
            parameters: vec!["Region".into(), "Payload".into()],
            owner_parameter: 0,
            payload_parameter: 1,
            state: "Token".into(),
            reference: "Handle".into(),
            allocation_result: "Outcome".into(),
            allocation_error: "Fault".into(),
            allocated_constructor: "Reserved".into(),
            refused_constructor: "RejectedStorage".into(),
            store: ForeignFoundationOperationDeclaration {
                name: "put".into(),
                signature: "(Token<Region>, Measured<Payload>, Int, Payload) -> Outcome<Handle<Region, Payload>>".into(),
            },
            load: ForeignFoundationOperationDeclaration {
                name: "get".into(),
                signature: "(Token<Region>, Measured<Payload>, Handle<Region, Payload>) -> Payload".into(),
            },
        },
    });
    schema
}

const STORAGE_NOT_EXECUTABLE: &str =
    "typed foreign storage is not executable in this admission phase";

fn foundation_rejection(schema: ForeignManifestSchema, malformed: bool) -> String {
    let manifest = match ForeignManifest::new(
        "@foreign.mock.renamed",
        ForeignRegistrationId::new(101),
        schema,
    ) {
        Ok(manifest) => manifest,
        Err(error) => {
            assert!(
                malformed,
                "valid foundation failed manifest construction: {error}"
            );
            return error.to_string();
        }
    };
    let tree = Tree::new();
    let entry = tree.write("entry.ash", "import @foreign.mock.renamed as Native\n");
    let graph = load_module_graph(&entry, &roots(manifest)).unwrap();
    let native = graph
        .modules()
        .iter()
        .find(|module| module.foreign_admission().is_some())
        .unwrap();
    let failure = resolve_module(native, &[]).unwrap_err();
    let ash::resolve::ResolveModuleError::Resolution(diagnostic) = failure else {
        panic!("expected foreign contract admission refusal: {failure:?}");
    };
    assert_ne!(
        diagnostic.reason,
        ash::resolve::ResolveReason::TypeResourceExhausted
    );
    diagnostic.primary.message().to_owned()
}

#[test]
fn renamed_typed_foundation_validates_then_refuses_executable_admission() {
    let schema = foundation_schema();
    assert_eq!(schema.effects[0].operations.len(), 3);
    assert!(matches!(
        schema.effects[0].operations[1].result,
        ForeignResultRelation::Independent
    ));
    assert_eq!(foundation_rejection(schema, false), STORAGE_NOT_EXECUTABLE);
}

#[test]
fn malformed_typed_foundation_contracts_reject_before_execution_boundary() {
    let mutations: [(&str, fn(&mut ForeignManifestSchema)); 10] = [
        ("witness coordinate", |schema| {
            schema.types[4].category = ForeignTypeCategory::LayoutWitness {
                payload_parameter: 1,
            };
        }),
        ("reference coordinates", |schema| {
            schema.types[5].category = ForeignTypeCategory::Reference {
                owner_parameter: 0,
                payload_parameter: 0,
            };
        }),
        ("storage coordinates", |schema| {
            schema
                .foundation
                .as_mut()
                .unwrap()
                .storage
                .payload_parameter = 0;
        }),
        ("success branch", |schema| {
            schema.types[6].constructors[0].payload = Some("Fault".into());
        }),
        ("refusal independence", |schema| {
            schema.types[6].constructors[1].payload = Some("Token<Int>".into());
        }),
        ("unsaturated error payload", |schema| {
            schema.types[1].constructors[0].payload = Some("Box".into());
            schema.types.push(ForeignTypeDeclaration {
                name: "Box".into(),
                parameters: vec!["T".into()],
                category: ForeignTypeCategory::Data,
                constructors: vec![ForeignConstructorDeclaration {
                    name: "Boxed".into(),
                    payload: Some("T".into()),
                }],
            });
        }),
        ("layout method", |schema| {
            schema.foundation.as_mut().unwrap().layout.method.signature = "Unit -> Int".into();
        }),
        ("store witness", |schema| {
            schema.foundation.as_mut().unwrap().storage.store.signature =
                "(Token<Region>, Measured<Region>, Int, Payload) -> Outcome<Handle<Region, Payload>>".into();
        }),
        ("store reference", |schema| {
            schema.foundation.as_mut().unwrap().storage.store.signature =
                "(Token<Region>, Measured<Payload>, Int, Payload) -> Outcome<Handle<Payload, Region>>".into();
        }),
        ("load payload", |schema| {
            schema.foundation.as_mut().unwrap().storage.load.signature =
                "(Token<Region>, Measured<Payload>, Handle<Region, Payload>) -> Int".into();
        }),
    ];
    for (label, mutate) in mutations {
        let mut schema = foundation_schema();
        mutate(&mut schema);
        let message = foundation_rejection(schema, true);
        assert_ne!(message, STORAGE_NOT_EXECUTABLE, "{label}");
        assert!(!message.contains("budget exhausted"), "{label}: {message}");
    }
}

#[test]
fn typed_foundation_parameter_coordinates_are_independent() {
    for reverse_storage in [true, false] {
        let mut schema = foundation_schema();
        if reverse_storage {
            let storage = &mut schema.foundation.as_mut().unwrap().storage;
            storage.parameters.swap(0, 1);
            storage.owner_parameter = 1;
            storage.payload_parameter = 0;
        } else {
            let reference = &mut schema.types[5];
            reference.parameters.swap(0, 1);
            reference.category = ForeignTypeCategory::Reference {
                owner_parameter: 1,
                payload_parameter: 0,
            };
            let storage = &mut schema.foundation.as_mut().unwrap().storage;
            storage.store.signature =
                "(Token<Region>, Measured<Payload>, Int, Payload) -> Outcome<Handle<Payload, Region>>".into();
            storage.load.signature =
                "(Token<Region>, Measured<Payload>, Handle<Payload, Region>) -> Payload".into();
        }
        assert_eq!(
            foundation_rejection(schema, false),
            STORAGE_NOT_EXECUTABLE,
            "reverse_storage={reverse_storage}"
        );
    }
}
