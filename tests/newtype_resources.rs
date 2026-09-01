//! Cross-stage resource evidence for module newtypes.
//!
//! Exact private formulas stay beside their owning operations. This target
//! keeps their closed public manifest without exposing budget injection as API.

use std::{
    collections::HashSet,
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{PureComputation, PureExprKind, ValidatedProgram, validate_modules},
    driver::{RunConfiguration, run_path},
    elaborate::{Elaborator, check_module, link_modules},
    eval::{Value, evaluate},
    evidence_validation::validate_interface_evidence,
    module::{ModuleRoots, load_module_graph},
    render,
    resolve::resolve_module,
};

const PARSER: &str = include_str!("../src/parser/grammar.rs");
const RESOLVE: &str = include_str!("../src/resolve.rs");
const RESOLVED: &str = include_str!("../src/resolved.rs");
const ELABORATE: &str = include_str!("../src/elaborate.rs");
const CORE_DIALECT: &str = include_str!("../src/core/dialect.rs");
const CORE_TRANSFORM: &str = include_str!("../src/core/transform.rs");
const CORE_VALIDATE: &str = include_str!("../src/core/validate.rs");
const EVAL_MACHINE: &str = include_str!("../src/eval/machine.rs");

struct OwnerEvidence {
    category: &'static str,
    ledger: &'static str,
    source: &'static str,
    exact_probe: &'static str,
    boundary_markers: &'static [&'static str],
    feature_probe: Option<&'static str>,
}

const OWNERS: &[OwnerEvidence] = &[
    OwnerEvidence {
        category: "syntax event",
        ledger: "syntax",
        source: PARSER,
        exact_probe: "fn newtype_declaration_consumes_exact_cumulative_syntax_work_and_retries_cleanly()",
        boundary_markers: &[
            "const EXACT_WORK: usize = TOKEN_WORK + EVENT_WORK;",
            "let one_short_limit = exact_work - 1;",
            "let retry = parse_newtype_with_limit(&source, exact_work);",
        ],
        feature_probe: None,
    },
    OwnerEvidence {
        category: "declaration and constructor record",
        ledger: "module type work",
        source: RESOLVE,
        exact_probe: "fn shared_foreign_nominal_constructor_family_transaction_is_exact_atomic_and_reusable()",
        boundary_markers: &[
            "const FIRST_TYPE_WORK: usize = 20;",
            "one missing family cell must leave the route cache and facts empty",
            "the exact first route should retain the complete family",
        ],
        feature_probe: Some(
            "fn opaque_newtype_value_scheme_retains_canonical_closure_without_constructor_access()",
        ),
    },
    OwnerEvidence {
        category: "identity and canonical fact",
        ledger: "module type work",
        source: RESOLVED,
        exact_probe: "fn opaque_canonical_representation_retention_is_retryable_and_authenticated()",
        boundary_markers: &[
            "const EXACT_WORK: usize = REPRESENTATION_SLOT_WORK + REPRESENTATION_TYPE_WORK;",
            "TypeWorkBudget::with_limit(exact_work - 1)",
            "a fresh exact retry should retain the canonical representation",
        ],
        feature_probe: None,
    },
    OwnerEvidence {
        category: "representation type and substitution",
        ledger: "module type work",
        source: ELABORATE,
        exact_probe: "fn wide_newtype_constructor_fresh_substitution_is_additive_and_retryable()",
        boundary_markers: &[
            "const EXACT_WORK: usize = 4 * PARAMETER_COUNT + 3;",
            "TypeWorkBudget::with_limit(EXACT_WORK - 1)",
            "exact additive attempt {attempt} should fit",
        ],
        feature_probe: None,
    },
    OwnerEvidence {
        category: "representation graph entry",
        ledger: "module type work",
        source: ELABORATE,
        exact_probe: "fn newtype_representation_graph_has_an_isolated_retryable_type_work_boundary()",
        boundary_markers: &[
            "const EXACT_WORK: usize = VERTEX_INDEX_WORK + ADJACENCY_WORK + TYPE_WALK_WORK + DFS_WORK;",
            "TypeWorkBudget::with_limit(exact_work - 1)",
            "the exact isolated graph budget should be retryable",
        ],
        feature_probe: None,
    },
    OwnerEvidence {
        category: "summary and link fact",
        ledger: "interface constraint (independent zero)",
        source: RESOLVED,
        exact_probe: "fn opaque_canonical_representation_retention_is_retryable_and_authenticated()",
        boundary_markers: &[
            "const EXACT_WORK: usize = REPRESENTATION_SLOT_WORK + REPRESENTATION_TYPE_WORK;",
            "assert_eq!(measured_constraints.used(), 0);",
            "let mut short_constraints = crate::interface::InterfaceConstraintBudget::default();",
            "let mut exact_constraints = crate::interface::InterfaceConstraintBudget::default();",
        ],
        feature_probe: Some(
            "fn transparent_newtype_summary_fixture_authenticates_before_tampering()",
        ),
    },
    OwnerEvidence {
        category: "conversion node",
        ledger: "Core construction",
        source: CORE_DIALECT,
        exact_probe: "fn newtype_conversion_admission_has_an_exact_atomic_retry_boundary()",
        boundary_markers: &[
            "const EXACT_CONVERSION_WORK: usize = RESULT_TYPE_WORK;",
            "conversion_work - 1",
            "for _ in 0..2",
        ],
        feature_probe: None,
    },
    OwnerEvidence {
        category: "generated binder and function",
        ledger: "Core construction",
        source: ELABORATE,
        exact_probe: "fn wide_parameterized_newtype_constructor_lowering_is_exact_atomic_and_retryable()",
        boundary_markers: &[
            "const EXACT_WORK: usize = 18 * PARAMETER_COUNT + 9;",
            "TypeWorkBudget::with_limit(EXACT_WORK - 1)",
            "the exact fresh whole-constructor budget should retry",
        ],
        feature_probe: Some(
            "fn parameterized_newtype_constructor_generated_binder_registration_retries_same_identity()",
        ),
    },
    OwnerEvidence {
        category: "transform copy",
        ledger: "Core construction",
        source: CORE_TRANSFORM,
        exact_probe: "fn transforms_rebuild_validated_newtype_conversions()",
        boundary_markers: &[
            "const EXACT_WORK: usize = REMAP_WORK + CHILD_COPY_WORK + CONVERSION_COPY_WORK;",
            "one-short newtype transform must reject",
            "exact newtype transform should retry",
        ],
        feature_probe: None,
    },
    OwnerEvidence {
        category: "Core validation fact",
        ledger: "Core validation",
        source: CORE_VALIDATE,
        exact_probe: "fn parameterized_newtype_validation_is_exact_atomic_and_retryable()",
        boundary_markers: &[
            "const EXACT_WORK: usize = VALIDATION_ENVELOPE_WORK + NEWTYPE_PARAMETER_WORK;",
            "let one_short = attempt(CORE_VALIDATION_TYPE_WORK_LIMIT - (exact_work - 1));",
            "let retry = attempt(CORE_VALIDATION_TYPE_WORK_LIMIT - exact_work);",
        ],
        feature_probe: None,
    },
];

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new(text: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir()
                .join(format!("ash-newtype-resource-{}-{id}", std::process::id()));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let entry = directory.join("entry.ash");
                    fs::write(&entry, text).expect("resource fixture should be writable");
                    return Self(entry);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("resource fixture should be creatable: {error}"),
            }
        }
    }

    fn run(&self) -> ash::driver::Observation {
        run_path(RunConfiguration {
            entry: self.0.clone(),
            roots: ModuleRoots::empty(),
        })
        .expect("public resource fixture should run")
    }

    fn core(&self) -> ValidatedProgram {
        let graph =
            load_module_graph(&self.0, &ModuleRoots::empty()).expect("resource graph should load");
        let module = graph
            .module(graph.entry())
            .expect("entry should remain loaded");
        let checked = check_module(resolve_module(module, &[]).expect("fixture should resolve"))
            .expect("fixture should check");
        let linked = link_modules(vec![checked], graph.entry()).expect("fixture should link");
        let linked =
            validate_interface_evidence(linked).expect("linked evidence should authenticate");
        let mut elaborator =
            Elaborator::for_module_program(&linked).expect("Core namespace should fit");
        let typed = elaborator
            .synthesize_module_program(&linked)
            .expect("fixture should elaborate");
        let unchecked = elaborator.finish(typed.node).expect("Core should finish");
        let sources = graph
            .modules()
            .iter()
            .map(|module| module.source())
            .collect::<Vec<_>>();
        let module_sources = graph
            .modules()
            .iter()
            .map(|module| (module.id(), module.source().id()))
            .collect::<Vec<_>>();
        validate_modules(unchecked, &sources, &module_sources)
            .expect("Core should independently validate")
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        if let Some(directory) = self.0.parent() {
            let _ = fs::remove_dir_all(directory);
        }
    }
}

fn conversion_count(program: &ValidatedProgram) -> usize {
    let mut pending = vec![program.root()];
    let mut visited = HashSet::new();
    let mut conversions = 0;
    while let Some(id) = pending.pop() {
        if !visited.insert(id) {
            continue;
        }
        let node = program
            .node(id)
            .expect("reachable validated node should exist");
        pending.extend((0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)));
        conversions += usize::from(matches!(
            node.kind,
            PureExprKind::Computation(PureComputation::NewtypeConversion(_))
        ));
    }
    conversions
}

#[test]
fn module_newtype_resource_matrix_accounts_all_new_carriers() {
    let expected = [
        "syntax event",
        "declaration and constructor record",
        "identity and canonical fact",
        "representation type and substitution",
        "representation graph entry",
        "summary and link fact",
        "conversion node",
        "generated binder and function",
        "transform copy",
        "Core validation fact",
    ];
    assert_eq!(OWNERS.len(), expected.len());
    for category in expected {
        assert_eq!(
            OWNERS
                .iter()
                .filter(|owner| owner.category == category)
                .count(),
            1
        );
    }
    for ledger in [
        "syntax",
        "module type work",
        "interface constraint (independent zero)",
        "Core construction",
        "Core validation",
    ] {
        assert!(OWNERS.iter().any(|owner| owner.ledger == ledger));
    }
    for owner in OWNERS {
        assert!(
            owner.source.contains(owner.exact_probe),
            "{}",
            owner.category
        );
        for marker in owner.boundary_markers {
            assert!(
                owner.source.contains(marker),
                "{}: {marker}",
                owner.category
            );
        }
        if let Some(feature_probe) = owner.feature_probe {
            assert!(owner.source.contains(feature_probe), "{}", owner.category);
        }
    }

    let wrapped = Fixture::new(concat!(
        "newtype Box<A> = Box(A)\n",
        "main : Unit -> Box<Int>\n",
        "main () = Box(42)\n",
    ));
    let wrapped_core = wrapped.core();
    assert_eq!(conversion_count(&wrapped_core), 1);
    let first = evaluate(&wrapped_core).expect("newtype Core should evaluate");
    let retry = evaluate(&wrapped_core).expect("immutable newtype Core should retry");
    assert_eq!(first.value.to_string(), "42");
    assert_eq!(first.trace, retry.trace);
    let observation = wrapped.run();
    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Box<Int>");
    assert_eq!(render::observation(&observation), "42 : Box<Int>\n");

    let predecessor = Fixture::new("main : Unit -> Int\nmain () = 42\n");
    let predecessor_core = predecessor.core();
    assert_eq!(predecessor_core.node_count(), 8);
    assert_eq!(conversion_count(&predecessor_core), 0);
    let before = evaluate(&predecessor_core).expect("predecessor Core should evaluate");
    let after = evaluate(&predecessor_core).expect("predecessor Core should remain reusable");
    assert!(matches!(before.value, Value::Integer(_)));
    assert_eq!(before.value.to_string(), "42");
    assert_eq!(before.trace, after.trace);
    assert_eq!(before.trace.len(), 7);
    assert_eq!(before.max_frame_depth, after.max_frame_depth);
    let observation = predecessor.run();
    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");
    assert_eq!(render::observation(&observation), "42 : Int\n");

    assert!(
        EVAL_MACHINE.contains(
            "fn type_erasure_enters_each_explicit_operation_once_without_runtime_state()"
        )
    );
    assert!(EVAL_MACHINE.contains("fn module_newtype_wrapper_allocates_no_constructor_cell()"));
    assert!(EVAL_MACHINE.contains("assert_eq!(evaluation.heap.cell_count(), 0);"));
    assert!(ELABORATE.contains("ordinary data must not allocate a newtype representation graph"));
    assert!(ELABORATE.contains("assert_eq!(ordinary_work.used(), 0);"));
    assert!(
        CORE_DIALECT
            .contains("fn canonical_application_core_admission_has_an_exact_cell_boundary()")
    );
}
