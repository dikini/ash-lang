//! Process-level regression coverage for the experimental observer's limits.
#![cfg(feature = "resource-calibration")]

use std::{path::Path, process::Command};

use ash::compiler_work::CompilationPhase;
use serde_json::Value;

fn run(entry: &Path, observe: bool, diagnostic_base: Option<usize>) -> std::process::Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_ash"));
    command
        .arg(entry)
        .env_remove("ASH_CALIBRATION_LIMIT")
        .env("ASH_CALIBRATION_OBSERVE", if observe { "1" } else { "0" });
    if let Some(base) = diagnostic_base {
        command.env("ASH_CALIBRATION_LIMIT", base.to_string());
    }
    command.output().unwrap()
}

fn records(output: &std::process::Output) -> Vec<Value> {
    String::from_utf8_lossy(&output.stderr)
        .lines()
        .filter_map(|line| line.strip_prefix("ASH_CALIBRATION "))
        .map(|json| serde_json::from_str(json).unwrap())
        .collect()
}

#[test]
fn pure_and_effect_observation_preserve_results_and_report_selected_capacities_once() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for fixture in [
        "tests/fixtures/first-stratum/valid/v001-precedence.ash",
        "tests/fixtures/effects/valid/effect-kernel-combined.ash",
    ] {
        for base in [None, Some(2_000_000)] {
            let entry = root.join(fixture);
            let off = run(&entry, false, base);
            let on = run(&entry, true, base);
            assert!(off.status.success(), "{fixture}: {:?}", off.stderr);
            assert_eq!(on.status.code(), off.status.code());
            assert_eq!(on.stdout, off.stdout);
            assert!(records(&off).is_empty());
            let observed = records(&on);
            for (phase, normal, multiplier) in [
                ("resolution", ash::types::TYPE_WORK_LIMIT, 1),
                (
                    "source-checking",
                    CompilationPhase::SourceChecking.hard_limit(),
                    1,
                ),
                ("module-linking", ash::types::TYPE_WORK_LIMIT, 1),
                ("linked-interface", ash::types::TYPE_WORK_LIMIT, 1),
                (
                    "final-elaboration",
                    CompilationPhase::FinalElaboration.hard_limit(),
                    1,
                ),
                (
                    "independent-effect-core",
                    CompilationPhase::IndependentCore.hard_limit(),
                    3,
                ),
            ] {
                let endpoints = observed
                    .iter()
                    .filter(|record| record["event"] == "work" && record["phase"] == phase)
                    .collect::<Vec<_>>();
                assert_eq!(endpoints.len(), 1, "{fixture}: {phase}");
                let endpoint = endpoints[0];
                assert_eq!(endpoint["completed"], true);
                assert_eq!(endpoint["normal_limit"], normal);
                assert_eq!(
                    endpoint["diagnostic_limit"],
                    base.map_or(normal, |value| value * multiplier)
                );
                assert!(endpoint["work_cumulative"].as_u64().unwrap() > 0);
            }
            for phase in [
                "loading",
                "resolution",
                "source-checking",
                "module-linking",
                "linked-interface",
                "final-elaboration",
                "independent-effect-core",
                "evaluation",
                "pipeline",
            ] {
                assert!(
                    observed.iter().any(|record| {
                        record["event"] == "phase"
                            && record["phase"] == phase
                            && record["completed"] == true
                    }),
                    "{fixture}: missing completed {phase}"
                );
            }
            assert!(
                observed
                    .iter()
                    .all(|record| { record["event"] != "phase" || record["completed"] == true })
            );
        }
    }
}

#[test]
fn rejected_source_retains_incomplete_phase_without_completed_later_owners() {
    let entry = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/first-stratum/type/binding-initializer.ash");
    let output = run(&entry, true, None);
    assert_eq!(output.status.code(), Some(1));
    let observed = records(&output);
    assert!(observed.iter().any(|record| {
        record["event"] == "phase"
            && record["phase"] == "source-checking"
            && record["completed"] == false
    }));
    assert!(observed.iter().all(|record| {
        record["event"] != "work"
            || !matches!(
                record["phase"].as_str(),
                Some("source-checking" | "final-elaboration" | "independent-effect-core")
            )
    }));
}
