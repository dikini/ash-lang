//! Product-level resource and disposal evidence for method-local type parameters.

use std::{
    fmt::Write as _,
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{
        ValidatedEffectProgram, ValidationReason,
        transform::{fold_effect_literal_primitives, identity_effect_traversal},
        validate_effect_modules,
    },
    driver::{FileFailure, RunConfiguration, run_path},
    elaborate::{EffectElaborator, check_module, link_modules},
    evidence_validation::validate_interface_evidence,
    lexer::lex,
    module::{ModuleGraph, ModuleRoots, load_module_graph},
    parser::{parse, project_module},
    resolve::{DependencyExports, resolve_module},
    source::SourceFile,
};

const STACK_SIZE: usize = 256 * 1024;

const RESOLVE_SOURCE: &str = include_str!("../src/resolve.rs");
const RESOLVED_SOURCE: &str = include_str!("../src/resolved.rs");
const EVIDENCE_SOURCE: &str = include_str!("../src/evidence.rs");
const EVIDENCE_VALIDATION_SOURCE: &str = include_str!("../src/evidence_validation.rs");
const ELABORATE_SOURCE: &str = include_str!("../src/elaborate.rs");
const CORE_DIALECT_SOURCE: &str = include_str!("../src/core/dialect.rs");
const CORE_VALIDATE_SOURCE: &str = include_str!("../src/core/validate.rs");
const CORE_TRANSFORM_SOURCE: &str = include_str!("../src/core/transform.rs");

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct InlineFixture(PathBuf);

impl InlineFixture {
    fn create(source: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir().join(format!(
                "ash-method-parameter-resource-{}-{id}",
                std::process::id(),
            ));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let entry = directory.join("entry.ash");
                    fs::write(&entry, source).expect("the inline fixture should be writable");
                    return Self(entry);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("the inline fixture directory should be creatable: {error}"),
            }
        }
    }

    fn run(&self) -> Result<ash::driver::Observation, FileFailure> {
        run_path(RunConfiguration {
            entry: self.0.clone(),
            roots: ModuleRoots::empty(),
        })
    }

    fn validated_core(&self) -> (ValidatedEffectProgram, ModuleGraph) {
        let graph = load_module_graph(&self.0, &ModuleRoots::empty())
            .expect("the inline adapter graph should load");
        let mut checked = Vec::<ash::resolved::CheckedModule>::new();
        for module in graph.modules() {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    let target = checked
                        .iter()
                        .find(|checked| checked.module() == edge.target())
                        .expect("dependencies precede their importer");
                    DependencyExports::new(edge, target.exports())
                        .expect("the actual target authenticates its edge")
                })
                .collect::<Vec<_>>();
            let resolved =
                resolve_module(module, &dependencies).expect("the inline adapter resolves");
            checked.push(check_module(resolved).expect("the inline adapter checks"));
        }
        let linked = link_modules(checked, graph.entry()).expect("the complete graph links");
        let linked = validate_interface_evidence(linked)
            .expect("the inline adapter evidence should authenticate");
        let mut elaborator = EffectElaborator::for_module_program(&linked)
            .expect("the inline adapter Core namespace should fit");
        let typed = elaborator
            .synthesize_effect_module_program(&linked)
            .expect("the inline adapter should elaborate");
        let unchecked = elaborator
            .finish(typed.node)
            .expect("the inline adapter Core should finish");
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
        let program = validate_effect_modules(unchecked, &sources, &module_sources)
            .expect("the inline adapter Core should validate independently");
        (program, graph)
    }
}

impl Drop for InlineFixture {
    fn drop(&mut self) {
        if let Some(directory) = self.0.parent() {
            let _ = fs::remove_dir_all(directory);
        }
    }
}

fn method_syntax_source(parameter_count: usize) -> String {
    assert!(parameter_count > 0);
    let parameters = (0..parameter_count)
        .map(|index| format!("T{index}"))
        .collect::<Vec<_>>();
    format!(
        "interface Carry<I> {{\ncarry<{}> : ({}, I) -> I\n}}\n",
        parameters.join(", "),
        parameters.join(", "),
    )
}

fn syntax_work(parameter_count: usize) -> usize {
    let text = method_syntax_source(parameter_count);
    let source = SourceFile::new("method-syntax-work.ash", text)
        .expect("the method syntax source should fit");
    let tree = parse(lex(&source).expect("the method syntax source should lex"));
    assert_eq!(tree.resource_failure(), None);
    project_module(&source, &tree).expect("the method syntax source should project");
    tree.tokens().len() + tree.events().len()
}

fn deep_method_source(depth: usize, leaf: &str) -> String {
    let mut method_type = String::new();
    for _ in 0..depth {
        method_type.push_str("I -> ");
    }
    method_type.push_str(leaf);
    format!(
        "interface Deep<I> {{\ndeep<T> : {method_type}\n}}\n\n\
         main : Unit -> Int\nmain () = 42\n",
    )
}

fn wide_method_source(width: usize, duplicate_last: bool) -> String {
    assert!(width > 0);
    let parameters = (0..width)
        .map(|index| format!("T{index}"))
        .collect::<Vec<_>>();
    let mut written = parameters.clone();
    if duplicate_last {
        written.push(String::from("T0"));
    }
    format!(
        "interface Wide<I> {{\nwide<{}> : (I, {}) -> I\n}}\n\n\
         main : Unit -> Int\nmain () = 42\n",
        written.join(", "),
        parameters.join(", "),
    )
}

fn adapter_heavy_source(width: usize, reject_last: bool) -> String {
    assert!(width >= 2);
    let mut source = String::from(
        "interface Adapt<I> {\nadapt<T> : (I, T) -> I\n}\n\n\
         impl Adapt<Int> {\nadapt (value, ignored) = value\n}\n\nmain : Unit -> (",
    );
    for index in 0..width {
        if index > 0 {
            source.push_str(", ");
        }
        if reject_last && index + 1 == width {
            source.push_str("Bool");
        } else {
            source.push_str("Int");
        }
    }
    source.push_str(")\nmain () = (");
    for index in 0..width {
        if index > 0 {
            source.push_str(", ");
        }
        if reject_last && index + 1 == width {
            source.push_str("adapt((true, false))");
        } else {
            let argument = match index % 3 {
                0 => "true",
                1 => "()",
                _ => "42",
            };
            write!(source, "adapt(({}, {argument}))", index + 1)
                .expect("writing into a String should not fail");
        }
    }
    source.push_str(")\n");
    source
}

#[test]
fn syntax_method_binders_have_an_exact_additive_token_and_event_formula() {
    const FIXED_INTERFACE_AND_METHOD_WORK: usize = 68;
    const WORK_PER_METHOD_PARAMETER: usize = 14;

    for parameter_count in [1, 2, 3, 512] {
        assert_eq!(
            syntax_work(parameter_count),
            FIXED_INTERFACE_AND_METHOD_WORK + WORK_PER_METHOD_PARAMETER * parameter_count,
        );
    }
}

#[test]
fn exact_unit_formulas_remain_attached_to_their_owning_probes() {
    // Local tariffs retain their derived expressions. Complete catalog/authority
    // boundaries now retain measured successful owner totals and exact/short/retry
    // checks beside the owning probe, rather than obsolete predecessor subtotals.
    let probes = [
        (
            "resolution binder validation",
            RESOLVE_SOURCE,
            "fn method_parameter_validation_is_exact_atomic_and_retryable()",
            "const COMPLETE_WORK: usize = 2 + OWNER_AND_BINDER_SET_VISITS + 6 + 2 * 2;",
        ),
        (
            "imported method-binder Kind authentication",
            RESOLVE_SOURCE,
            "fn imported_method_binder_kind_authentication_is_exact()",
            "const EXACT_WORK: usize = 4;",
        ),
        (
            "hidden interface import constraint ledger",
            RESOLVE_SOURCE,
            "fn hidden_interface_import_route_uses_its_exact_constraint_budget()",
            "const EXACT_CONSTRAINT_WORK: usize = 1 + 2 + 1 + 1 + 14 + 3 + 3;",
        ),
        (
            "hidden interface import type ledger",
            RESOLVE_SOURCE,
            "fn hidden_interface_import_route_uses_its_exact_constraint_budget()",
            "const EXACT_TYPE_WORK: usize = 6 + 41 + 19 + 1 + 1 + 1;",
        ),
        (
            "summary private binder authority graph ledger",
            RESOLVED_SOURCE,
            "fn method_binder_authority_retention_has_exact_independent_ledgers()",
            "const EXACT_CONSTRAINT_WORK: usize = 1;",
        ),
        (
            "summary private binder authority",
            RESOLVED_SOURCE,
            "fn method_binder_authority_retention_has_exact_independent_ledgers()",
            "const EXACT_TYPE_WORK: usize = 1;",
        ),
        (
            "selector method-scheme ingress",
            EVIDENCE_SOURCE,
            "fn interface_selector_method_scheme_has_exact_atomic_dual_boundaries()",
            "const EXACT_CONSTRAINT_WORK: usize = 10 + 5;",
        ),
        (
            "selector scheme ingress",
            EVIDENCE_SOURCE,
            "fn wide_method_scheme_ingress_charges_retained_and_duplicate_indexes()",
            "const EXACT_CONSTRAINT_WORK: usize = WIDTH * 5 + 7;",
        ),
        (
            "selector scheme ingress type ledger",
            EVIDENCE_SOURCE,
            "fn wide_method_scheme_ingress_charges_retained_and_duplicate_indexes()",
            "const EXACT_TYPE_WORK: usize = WIDTH * 3 + 6;",
        ),
        (
            "occurrence publication",
            EVIDENCE_SOURCE,
            "fn pending_method_arguments_have_exact_atomic_publication_boundaries()",
            "const EXACT_CONSTRAINT_WORK: usize = 2 + 1 + 1 + 2 + 2;",
        ),
        (
            "occurrence publication type ledger",
            EVIDENCE_SOURCE,
            "fn pending_method_arguments_have_exact_atomic_publication_boundaries()",
            "const EXACT_TYPE_WORK: usize = 1 + 2;",
        ),
        (
            "selected method rigidity",
            EVIDENCE_SOURCE,
            "fn isolated_method_rigidity_close_has_exact_atomic_retry_boundaries()",
            "const EXACT_CONSTRAINT_WORK: usize = 25 + 3 + 6;",
        ),
        (
            "selected method rigidity type ledger",
            EVIDENCE_SOURCE,
            "fn isolated_method_rigidity_close_has_exact_atomic_retry_boundaries()",
            "const EXACT_TYPE_WORK: usize = 3 + 4;",
        ),
        (
            "shifted method rigidity",
            EVIDENCE_SOURCE,
            "fn isolated_method_rigidity_close_charges_the_exact_removal_shift()",
            "const EXACT_CONSTRAINT_WORK: usize = 27 + 3 + 6;",
        ),
        (
            "shifted method rigidity type ledger",
            EVIDENCE_SOURCE,
            "fn isolated_method_rigidity_close_charges_the_exact_removal_shift()",
            "const EXACT_TYPE_WORK: usize = 3 + 4;",
        ),
        (
            "conditional rigidity ingress constraint ledger",
            EVIDENCE_SOURCE,
            "fn conditional_method_rigidity_ingress_has_exact_atomic_retry_boundaries()",
            "const EXACT_CONSTRAINT_WORK: usize = 8 + 3 + 1;",
        ),
        (
            "conditional rigidity ingress type ledger",
            EVIDENCE_SOURCE,
            "fn conditional_method_rigidity_ingress_has_exact_atomic_retry_boundaries()",
            "const EXACT_TYPE_WORK: usize = 1 + 1;",
        ),
        (
            "wide conditional rigidity ingress constraint ledger",
            EVIDENCE_SOURCE,
            "fn wide_conditional_method_rigidity_ingress_is_exact_and_atomic()",
            "const EXACT_CONSTRAINT_WORK: usize = WIDTH * 4 + 8;",
        ),
        (
            "wide conditional rigidity ingress type ledger",
            EVIDENCE_SOURCE,
            "fn wide_conditional_method_rigidity_ingress_is_exact_and_atomic()",
            "const EXACT_TYPE_WORK: usize = 1 + 1;",
        ),
        (
            "method occurrence Kind copies",
            ELABORATE_SOURCE,
            "fn method_occurrence_parameter_copies_are_exact_atomic_and_stack_safe()",
            "const EXACT_WORK: usize = 2 + KIND_NODES + 1 + 1 + 2 + KIND_NODES + 1;",
        ),
        (
            "Core evidence-scope carriers",
            ELABORATE_SOURCE,
            "fn evidence_scope_entry_has_an_exact_carrier_boundary_and_fresh_retry()",
            "const EXACT_WORK: usize = 1 + 3 + 1 + 2;",
        ),
        (
            "selected rigidity traversal",
            ELABORATE_SOURCE,
            "fn selected_method_rigidity_has_exact_retryable_traversal_boundary()",
            "const EXACT_TYPE_WORK: usize = 1 + 2;",
        ),
        (
            "linked catalog constraint ledger",
            EVIDENCE_VALIDATION_SOURCE,
            "fn linked_method_evidence_catalog_has_exact_independent_ledgers()",
            "let constraint_work = measured_constraint.used();",
        ),
        (
            "generic implementation validation without discarded head buffer",
            EVIDENCE_VALIDATION_SOURCE,
            "fn generic_implementation_validation_excludes_discarded_head_scope_buffer_work()",
            "const EXACT_WORK_WITHOUT_UNUSED_HEAD_BUFFER: usize = 6;",
        ),
        (
            "linked catalog type ledger",
            EVIDENCE_VALIDATION_SOURCE,
            "fn linked_method_evidence_catalog_has_exact_independent_ledgers()",
            "let type_work = measured_type.used();",
        ),
        (
            "abstract producer catalog",
            EVIDENCE_VALIDATION_SOURCE,
            "fn widened_abstract_producer_lookup_has_an_exact_retry_boundary()",
            "let constraint_work = measured_constraint.used();",
        ),
        (
            "abstract producer type ledger",
            EVIDENCE_VALIDATION_SOURCE,
            "fn widened_abstract_producer_lookup_has_an_exact_retry_boundary()",
            "let type_work = measured_type.used();",
        ),
        (
            "concrete source catalog",
            EVIDENCE_VALIDATION_SOURCE,
            "fn concrete_adapter_source_catalog_has_an_exact_retry_boundary()",
            "let constraint_work = measured_constraint.used();",
        ),
        (
            "concrete source paid-prefix retention",
            EVIDENCE_VALIDATION_SOURCE,
            "fn concrete_adapter_source_catalog_has_an_exact_retry_boundary()",
            "for prefix in [0usize, 17] {",
        ),
        (
            "concrete source type ledger",
            EVIDENCE_VALIDATION_SOURCE,
            "fn concrete_adapter_source_catalog_has_an_exact_retry_boundary()",
            "let type_work = measured_type.used();",
        ),
        (
            "Core Builder carriers",
            CORE_DIALECT_SOURCE,
            "fn method_evidence_builder_constructor_precharges_both_exact_carriers()",
            "const EXACT_WORK: usize = 6 * EXPECTATIONS;",
        ),
        (
            "Core Builder anchor publication",
            CORE_DIALECT_SOURCE,
            "fn one_method_evidence_anchor_and_finish_have_an_exact_retry_boundary()",
            "let authenticate_and_finish_work =",
        ),
        (
            "concrete Core validation",
            CORE_VALIDATE_SOURCE,
            "fn concrete_monomorphic_source_validation_has_an_exact_retry_boundary()",
            "let exact_work = measured.type_work.get();",
        ),
        (
            "wide-prerequisite Core validation",
            CORE_VALIDATE_SOURCE,
            "fn concrete_source_with_wide_abstract_prerequisite_has_an_exact_retry_boundary()",
            "let exact_work = measured.type_work.get();",
        ),
        (
            "monomorphic adapter producer validation",
            CORE_VALIDATE_SOURCE,
            "fn monomorphic_adapter_edge_identity_has_an_exact_validation_boundary()",
            "let exact_work = measured.type_work.get();",
        ),
        (
            "independent Core validation",
            CORE_VALIDATE_SOURCE,
            "fn independent_method_evidence_authority_has_an_exact_retry_boundary()",
            "let exact_work = measured.type_work.get();",
        ),
        (
            "lowered requirement-row and replacement-entry owners",
            ELABORATE_SOURCE,
            "fn lowered_requirement_rows_and_replacements_have_an_exact_retryable_type_boundary()",
            "const EXACT_TYPE_WORK: usize = 1 + 1 + 1 + 1 + 1 + 1 + 2 + 1 + 1 + 1 + 2;",
        ),
        (
            "checked type worklist",
            ELABORATE_SOURCE,
            "fn checked_type_worklist_capacity_has_an_exact_boundary_and_fresh_retry()",
            "const EXACT_WORK: usize = 5;",
        ),
        (
            "Core transform replay",
            CORE_TRANSFORM_SOURCE,
            "fn linked_method_transforms_have_exact_anchor_remap_and_arc_lifecycle_boundaries()",
            "const CORE_WORK: usize = EFFECT_RECONSTRUCTION_AND_COPY_WORK\n            + COMPLETE_APPLICATION_WORK\n            + ALL_METHOD_CATALOG_LOOKUP_WORK\n            + CONCRETE_SOURCE_LOOKUP_WORK;",
        ),
        (
            "Core transform second Builder carrier",
            CORE_TRANSFORM_SOURCE,
            "fn linked_method_transforms_have_exact_anchor_remap_and_arc_lifecycle_boundaries()",
            "const CONSTRUCTOR_SECOND_CARRIER_WORK: usize = 4;",
        ),
        (
            "Core transform indexed Builder admission",
            CORE_TRANSFORM_SOURCE,
            "fn linked_method_transforms_have_exact_anchor_remap_and_arc_lifecycle_boundaries()",
            "const CONSTRUCTOR_INDEX_WORK: usize = 4 * ANCHOR_REPLAY_WORK;",
        ),
        (
            "Core transform exact shortlisted original positions",
            CORE_TRANSFORM_SOURCE,
            "fn linked_method_transforms_have_exact_anchor_remap_and_arc_lifecycle_boundaries()",
            "expectations[..=anchor.expectation]",
        ),
        (
            "rejected pending occurrence teardown",
            EVIDENCE_SOURCE,
            "fn pending_method_payload_zonk_failure_discards_staged_types_on_a_small_stack()",
            "const DEPTH: usize = 32_768;",
        ),
    ];

    for required_probe in [
        "fn imported_method_binder_kind_authentication_is_exact()",
        "fn hidden_interface_import_route_uses_its_exact_constraint_budget()",
        "fn interface_selector_method_scheme_has_exact_atomic_dual_boundaries()",
        "fn conditional_method_rigidity_ingress_has_exact_atomic_retry_boundaries()",
        "fn wide_conditional_method_rigidity_ingress_is_exact_and_atomic()",
        "fn evidence_scope_entry_has_an_exact_carrier_boundary_and_fresh_retry()",
        "fn selected_method_rigidity_has_exact_retryable_traversal_boundary()",
        "fn lowered_requirement_rows_and_replacements_have_an_exact_retryable_type_boundary()",
        "fn monomorphic_adapter_edge_identity_has_an_exact_validation_boundary()",
        "fn generic_implementation_validation_excludes_discarded_head_scope_buffer_work()",
        "fn pending_method_payload_zonk_failure_discards_staged_types_on_a_small_stack()",
    ] {
        assert!(
            probes
                .iter()
                .any(|(_, _, probe, _)| *probe == required_probe),
            "the retained owner manifest omits {required_probe}",
        );
    }

    let mut drift = Vec::new();
    for (stage, source, probe, formula) in probes {
        let Some((_, body)) = source.split_once(probe) else {
            drift.push(format!("missing exact unit probe for {stage}: {probe}"));
            continue;
        };
        // A matching formula in another test must not satisfy this owner.
        let probe_section = body.split("#[test]").next().unwrap_or(body);
        if !probe_section.contains(formula) {
            drift.push(format!(
                "the exact additive formula drifted for {stage}: {formula}",
            ));
        }
    }
    assert!(
        drift.is_empty(),
        "exact unit probe drift:\n{}",
        drift.join("\n"),
    );

    assert_eq!(10 + 5, 15);
    assert_eq!(5 * 1_024 + 7, 5_127);
    assert_eq!(3 * 1_024 + 6, 3_078);
    assert_eq!(1 + 2 + 1 + 1 + 14 + 3 + 3, 25);
    assert_eq!(6 + 41 + 19 + 1 + 1 + 1, 69);
    assert_eq!(8 + 3 + 1, 12);
    assert_eq!(4 * 1_024 + 8, 4_104);
    assert_eq!(4 + 2, 6);
    assert_eq!(1 + 2, 3);
    assert_eq!(1 + 1 + 1 + 1 + 1 + 1 + 2 + 1 + 1 + 1 + 2, 13);
    assert_eq!(7 - 1, 6);
    // The non-local Effect reconstruction subtotal is fixed by the complete
    // restored probe; explicit anchor, producer, payload and index terms remain.
    assert_eq!(
        1_946 + (4 + 4 + 3 + 5) + 8 + 4 + (4 + 4 + 2) + 4 + 1 + 4 + 1 + 20 + 16 + 12 + 5 - 6 - 16,
        2_025
    );
}

#[test]
fn deep_and_wide_method_carriers_accept_and_reject_on_a_256_kib_stack() {
    std::thread::Builder::new()
        .name(String::from("method-carrier-disposal"))
        .stack_size(STACK_SIZE)
        .spawn(|| {
            let accepted_deep = InlineFixture::create(&deep_method_source(96, "T"));
            assert_eq!(
                accepted_deep
                    .run()
                    .expect("the deep method scheme should complete")
                    .value_display(),
                "42",
            );

            let rejected_deep = InlineFixture::create(&deep_method_source(96, "(T, Missing)"));
            assert_eq!(
                rejected_deep
                    .run()
                    .expect_err("the deep method scheme with an unbound leaf should reject")
                    .reason_code(),
                "resolve.unknown-type",
            );

            let accepted_wide = InlineFixture::create(&wide_method_source(128, false));
            assert_eq!(
                accepted_wide
                    .run()
                    .expect("the wide method scheme should complete")
                    .value_display(),
                "42",
            );

            let rejected_wide = InlineFixture::create(&wide_method_source(128, true));
            assert_eq!(
                rejected_wide
                    .run()
                    .expect_err("the late duplicate in a wide binder list should reject")
                    .reason_code(),
                "resolve.duplicate-type-parameter",
            );
        })
        .expect("the method-carrier disposal thread should spawn")
        .join()
        .expect("accepted and rejected deep/wide carriers should dismantle on the small stack");
}

#[test]
fn adapter_heavy_core_and_rejected_occurrences_dispose_on_a_256_kib_stack() {
    const WIDTH: usize = 64;
    let accepted = InlineFixture::create(&adapter_heavy_source(WIDTH, false));
    let (program, graph) = accepted.validated_core();
    let rejected_core = identity_effect_traversal(&program)
        .expect("the adapter-bearing rejection candidate should build on the normal stack");
    let rejected = InlineFixture::create(&adapter_heavy_source(WIDTH, true));
    let failure = rejected
        .run()
        .expect_err("the late unmatched occurrence should reject atomically");
    assert_eq!(failure.reason_code(), "constraint.unsatisfied");

    std::thread::Builder::new()
        .name(String::from("method-adapter-core-disposal"))
        .stack_size(STACK_SIZE)
        .spawn(move || {
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
            let identity = validate_effect_modules(
                identity_effect_traversal(&program).expect("adapter identity replay should build"),
                &sources,
                &module_sources,
            )
            .expect("adapter identity replay should freshly validate");
            let folded = validate_effect_modules(
                fold_effect_literal_primitives(&program).expect("adapter fold replay should build"),
                &sources,
                &module_sources,
            )
            .expect("adapter fold replay should freshly validate");
            let rejection = validate_effect_modules(rejected_core, &sources, &[])
                .expect_err("the incomplete module/source relation should reject adapter Core");
            assert_eq!(rejection.reason(), ValidationReason::Registry);
            drop(folded);
            drop(identity);
            drop(program);
            drop(sources);
            drop(graph);
            drop(accepted);
            drop(failure);
            drop(rejected);
        })
        .expect("the method-adapter disposal thread should spawn")
        .join()
        .expect("accepted and rejected adapter-heavy states should dismantle on the small stack");
}
