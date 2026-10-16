//! Public observations retain work costs independently of evaluated Ash values.

use ash::{
    compiler_work::{CompilationPhase, WorkAssessment},
    driver::{RunConfiguration, run_path},
    module::{ModuleRoots, load_module_graph},
};
use std::{
    fs,
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);

fn with_source<T>(source: &str, run: impl FnOnce(RunConfiguration) -> T) -> T {
    let path = std::env::temp_dir().join(format!(
        "ash-work-report-{}-{}.ash",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::write(&path, source).unwrap();
    let result = run(RunConfiguration {
        entry: path.clone(),
        roots: ModuleRoots::empty(),
    });
    fs::remove_file(path).unwrap();
    result
}

#[test]
fn ordinary_public_execution_reports_completed_costs_without_changing_the_value() {
    let result = with_source("main : Unit -> Int\nmain () = 42\n", |configuration| {
        run_path(configuration).unwrap()
    });
    assert_eq!(result.value_display(), "42");
    let report = result.compilation_work();
    assert_eq!(
        report.source_checking.unwrap().allowance,
        Some(300 * "main : Unit -> Int\nmain () = 42\n".len())
    );
    assert_eq!(
        report.final_elaboration.unwrap().allowance,
        Some(161 * "main : Unit -> Int\nmain () = 42\n".len())
    );
    assert_eq!(
        report.independent_core.unwrap().allowance,
        Some(345 * "main : Unit -> Int\nmain () = 42\n".len())
    );
    for (cost, phase) in [
        (report.source_checking, CompilationPhase::SourceChecking),
        (report.final_elaboration, CompilationPhase::FinalElaboration),
        (report.independent_core, CompilationPhase::IndependentCore),
    ] {
        let cost = cost.expect("the ordinary public pipeline observes every selected ledger");
        assert_eq!(cost.phase, phase);
        assert!(cost.completed);
        assert!(cost.used > 0);
        assert_eq!(cost.assessment(), WorkAssessment::WithinBudget);
        assert!(!cost.optimization_target());
    }
}

#[test]
fn effect_execution_reports_paid_canonical_totals_without_alias_credit() {
    with_source(
        "import @builtin.cell as Cell\nimport @builtin.cell as Alias\nmain : Unit -> Int\nmain () = resource cell<R> value = 42 {\n    Cell.read value\n}\n",
        |configuration| {
            let graph = load_module_graph(&configuration.entry, &configuration.roots).unwrap();
            assert_eq!(graph.modules().len(), 2);
            let bytes: usize = graph
                .modules()
                .iter()
                .map(|module| module.source().text().len())
                .sum();
            let result = run_path(configuration).unwrap();
            assert_eq!(result.value_display(), "42");
            let report = result.compilation_work();
            for (cost, coefficient) in [
                (report.source_checking.unwrap(), 300),
                (report.final_elaboration.unwrap(), 161),
                (report.independent_core.unwrap(), 345),
            ] {
                assert!(cost.completed);
                assert_eq!(cost.allowance, Some(coefficient * bytes));
                assert_eq!(cost.assessment(), WorkAssessment::WithinBudget);
            }
        },
    );
}

#[test]
fn source_rejection_preserves_its_reason_and_partial_phase_measurement() {
    let failure = with_source("main : Unit -> Int\nmain () = true\n", |configuration| {
        run_path(configuration).unwrap_err()
    });
    assert!(failure.is_source_rejection());
    let report = failure
        .compilation_work()
        .expect("a source phase failure retains its work report");
    let cost = report
        .source_checking
        .expect("source checking was attempted");
    assert!(!cost.completed);
    assert!(cost.used > 0);
    assert!(report.final_elaboration.is_none());
    assert!(report.independent_core.is_none());
}

#[test]
fn entry_rejection_retains_observed_checking_without_fabricated_later_costs() {
    let failure = with_source("main : Int -> Int\nmain value = value\n", |configuration| {
        run_path(configuration).unwrap_err()
    });
    assert_eq!(failure.reason_code(), "entry.main-domain");
    let report = failure.compilation_work().unwrap();
    let source = report
        .source_checking
        .expect("checking completed before the entry rejection");
    assert!(source.used > 0);
    assert!(
        !source.completed,
        "the entry portion of source checking was rejected"
    );
    assert!(report.final_elaboration.is_none());
    assert!(report.independent_core.is_none());
}

#[test]
fn constrained_entry_rejection_reports_source_work_after_its_closure_walk() {
    let failure = with_source(
        "interface Marker<A> {\nmarker : A -> Bool\n}\nmain : Unit -> Int where Marker<Int>\nmain () = 42\n",
        |configuration| run_path(configuration).unwrap_err(),
    );
    assert_eq!(failure.reason_code(), "entry.main-constrained");
    let report = failure.compilation_work().unwrap();
    let source = report.source_checking.unwrap();
    assert!(!source.completed);
    assert!(source.used > 0);
    assert!(report.final_elaboration.is_none());
    assert!(report.independent_core.is_none());
}
