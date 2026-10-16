//! Process-level regression coverage for the experimental observer's limits.
#![cfg(feature = "resource-calibration")]

use std::{
    io::Write,
    path::Path,
    process::{Command, Stdio},
};

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

fn consume_calibration_logs(output: &std::process::Output) -> Value {
    let mut child = Command::new("python3")
        .arg("-B")
        .arg("-c")
        .arg(
            r#"
import json, pathlib, sys, tempfile
sys.path.insert(0, str(pathlib.Path(sys.argv[1]) / 'tools'))
import resource_calibration as calibration
logs = json.load(sys.stdin)
with tempfile.TemporaryDirectory() as directory:
    stdout, stderr = (pathlib.Path(directory) / name for name in ('stdout', 'stderr'))
    stdout.write_text(logs['stdout'])
    stderr.write_text(logs['stderr'])
    current = calibration.records_from_logs(stdout, stderr, True, calibration.PHASES)
    legacy_lines = []
    for line in logs['stderr'].splitlines():
        position = line.find(calibration.PREFIX)
        if position >= 0:
            record = json.loads(line[position + len(calibration.PREFIX):])
            if record.get('phase') == 'compilation':
                continue
        legacy_lines.append(line)
    stderr.write_text('\n'.join(legacy_lines))
    legacy = calibration.records_from_logs(stdout, stderr, True, calibration.PHASES)
    print(json.dumps({'current': current, 'legacy': legacy}))
"#,
        )
        .arg(env!("CARGO_MANIFEST_DIR"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("the calibration consumer requires Python 3");
    let input = serde_json::to_vec(&serde_json::json!({
        "stdout": String::from_utf8_lossy(&output.stdout),
        "stderr": String::from_utf8_lossy(&output.stderr),
    }))
    .unwrap();
    child.stdin.take().unwrap().write_all(&input).unwrap();
    let result = child.wait_with_output().unwrap();
    assert!(result.status.success(), "{:?}", result.stderr);
    serde_json::from_slice(&result.stdout).unwrap()
}

#[test]
fn pure_and_effect_observation_preserve_results_and_report_selected_capacities_once() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    for fixture in [
        "tests/fixtures/first-stratum/valid/v001-precedence.ash",
        "tests/fixtures/effects/valid/effect-kernel-combined.ash",
    ] {
        let graph =
            ash::module::load_module_graph(&root.join(fixture), &ash::module::ModuleRoots::empty())
                .unwrap();
        let source_bytes = graph
            .modules()
            .iter()
            .map(|module| module.source().text().len())
            .sum::<usize>();
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
                ("source-checking", 800 * source_bytes, 1),
                ("module-linking", ash::types::TYPE_WORK_LIMIT, 1),
                ("linked-interface", ash::types::TYPE_WORK_LIMIT, 1),
                ("final-elaboration", 800 * source_bytes, 1),
                ("independent-effect-core", 345 * source_bytes, 3),
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
                "compilation",
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
            if base.is_none() {
                let consumed = consume_calibration_logs(&on);
                let current = &consumed["current"];
                assert_eq!(current["complete"], true, "{}", current["errors"]);
                assert_eq!(current["phases"]["compilation"]["endpoint_count"], 1);
                assert_eq!(current["phases"]["compilation"]["completed_count"], 1);
                let work = current["work"].as_object().unwrap();
                assert_eq!(work.len(), 6);
                assert!(!work.contains_key("compilation"));
                // Historical traces precede the containing compilation timer.
                let legacy = &consumed["legacy"];
                assert_eq!(legacy["complete"], true, "{}", legacy["errors"]);
                assert!(legacy["phases"].get("compilation").is_none());
                assert_eq!(legacy["work"], current["work"]);
            }
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
