//! Public observations retain work costs independently of evaluated Ash values.

use ash::{
    compiler_work::{CompilationPhase, WorkAssessment},
    driver::{RunConfiguration, run_path},
    module::{ModuleRoots, load_module_graph},
};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);

#[test]
fn composed_frames_execute_through_independent_core() {
    let fixture =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/frame-composition");
    let configuration = RunConfiguration {
        entry: fixture.join("main.ash"),
        roots: ModuleRoots::new([
            ("buffers", fixture.join("buffers")),
            ("frames", fixture.join("frames")),
        ])
        .unwrap(),
    };
    let graph = load_module_graph(&configuration.entry, &configuration.roots).unwrap();
    let bytes: usize = graph
        .modules()
        .iter()
        .map(|module| module.source().text().len())
        .sum();
    let result = run_path(configuration)
        .unwrap_or_else(|failure| panic!("frame composition refused: {}", failure.reason_code()));
    assert_eq!(
        result.value_display(),
        concat!(
            "(Success(Success(Decoded(Ping))), ",
            "Success(Success(Decoded(Reading(0)))), ",
            "Success(Success(Decoded(Reading(255)))), ",
            "Success(Success(Decoded(Pair(0, 255)))), ",
            "Success(Success(Decoded(Pair(255, 0)))))"
        )
    );
    let work = result.compilation_work();
    eprintln!("frame composition compilation work: {work:?}");
    for (cost, coefficient) in [
        (work.source_checking.unwrap(), 10000),
        (work.final_elaboration.unwrap(), 800),
        (work.independent_core.unwrap(), 25000),
    ] {
        assert!(cost.completed);
        assert_eq!(cost.allowance, Some(coefficient * bytes));
        assert!(cost.used <= cost.allowance.unwrap());
    }
}

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
    let (result, bytes) = with_source("main : Unit -> Int\nmain () = 42\n", |configuration| {
        let graph = load_module_graph(&configuration.entry, &configuration.roots).unwrap();
        let bytes: usize = graph
            .modules()
            .iter()
            .map(|module| module.source().text().len())
            .sum();
        (run_path(configuration).unwrap(), bytes)
    });
    assert_eq!(result.value_display(), "42");
    let report = result.compilation_work();
    assert_eq!(
        report.source_checking.unwrap().allowance,
        Some(10000 * bytes)
    );
    assert_eq!(
        report.final_elaboration.unwrap().allowance,
        Some(800 * bytes)
    );
    assert_eq!(
        report.independent_core.unwrap().allowance,
        Some(25000 * bytes)
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
            assert_eq!(
                graph
                    .modules()
                    .iter()
                    .filter(|module| module.source().display_path() == "@builtin.cell")
                    .count(),
                1
            );
            let bytes: usize = graph
                .modules()
                .iter()
                .map(|module| module.source().text().len())
                .sum();
            let result = run_path(configuration).unwrap();
            assert_eq!(result.value_display(), "42");
            let report = result.compilation_work();
            for (cost, coefficient) in [
                (report.source_checking.unwrap(), 10000),
                (report.final_elaboration.unwrap(), 800),
                (report.independent_core.unwrap(), 25000),
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
