//! Workspace verification with explicit, exact-input local stage reuse.

mod receipt;

use std::{
    env,
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::{Command, ExitCode, Stdio},
    time::{Instant, SystemTime, UNIX_EPOCH},
};

use serde::Serialize;

use receipt::{Inputs, StageReceipt, digest, snapshot};

#[derive(Debug)]
struct VerificationStep {
    label: &'static str,
    arguments: &'static [&'static str],
    rustdoc_flags: Option<&'static str>,
}

const STEPS: &[VerificationStep] = &[
    VerificationStep {
        label: "format",
        arguments: &["fmt", "--all", "--check"],
        rustdoc_flags: None,
    },
    VerificationStep {
        label: "metadata",
        arguments: &["metadata", "--format-version", "1", "--locked", "--no-deps"],
        rustdoc_flags: None,
    },
    VerificationStep {
        label: "check",
        arguments: &["check", "--workspace", "--all-targets", "--locked"],
        rustdoc_flags: None,
    },
    VerificationStep {
        label: "build",
        arguments: &[
            "build",
            "--workspace",
            "--lib",
            "--bins",
            "--examples",
            "--locked",
        ],
        rustdoc_flags: None,
    },
    VerificationStep {
        label: "clippy",
        arguments: &[
            "clippy",
            "--workspace",
            "--all-targets",
            "--all-features",
            "--locked",
            "--",
            "-D",
            "warnings",
        ],
        rustdoc_flags: None,
    },
    VerificationStep {
        label: "test",
        arguments: &[
            "test",
            "--workspace",
            "--all-targets",
            "--all-features",
            "--locked",
        ],
        rustdoc_flags: None,
    },
    VerificationStep {
        label: "documentation",
        arguments: &["doc", "--workspace", "--no-deps", "--locked"],
        rustdoc_flags: Some("-D warnings"),
    },
];

#[derive(Debug, Default)]
struct Options {
    inputs_only: bool,
    stages: Vec<String>,
    reuse: bool,
    receipts: Option<PathBuf>,
    external_inputs: Vec<PathBuf>,
}

fn options() -> Result<Options, String> {
    let mut args = env::args_os().skip(1);
    let mut result = Options::default();
    match args.next().as_deref().and_then(|arg| arg.to_str()) {
        Some("verify") => {}
        Some("inputs") => result.inputs_only = true,
        _ => return Err("expected verify or inputs".into()),
    }
    while let Some(arg) = args.next() {
        match arg.to_str() {
            Some("--reuse") if !result.inputs_only && !result.reuse => result.reuse = true,
            Some("--step") if !result.inputs_only => {
                let label = args
                    .next()
                    .and_then(|s| s.into_string().ok())
                    .ok_or("--step requires a stage name")?;
                if !STEPS.iter().any(|step| step.label == label) || result.stages.contains(&label) {
                    return Err(format!("unknown or duplicate stage: {label}"));
                }
                result.stages.push(label);
            }
            Some("--receipt-dir") if !result.inputs_only && result.receipts.is_none() => {
                result.receipts = Some(args.next().ok_or("--receipt-dir requires a path")?.into());
            }
            Some("--input") => {
                result
                    .external_inputs
                    .push(args.next().ok_or("--input requires a file path")?.into());
            }
            _ => {
                return Err(format!(
                    "unknown or duplicate argument: {}",
                    arg.to_string_lossy()
                ));
            }
        }
    }
    Ok(result)
}

#[derive(Serialize)]
struct StageResult {
    label: &'static str,
    key: String,
    reused: bool,
    success: bool,
    seconds: f64,
    receipt: Option<PathBuf>,
    log: Option<PathBuf>,
}

#[derive(Serialize)]
struct RunSummary {
    schema: u32,
    complete_gate: bool,
    success: bool,
    seconds: f64,
    stages: Vec<StageResult>,
}

fn save_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let temporary = path.with_extension(format!("{}.tmp", std::process::id()));
    let bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    fs::write(&temporary, bytes).map_err(|error| format!("{}: {error}", temporary.display()))?;
    fs::rename(&temporary, path).map_err(|error| format!("{}: {error}", path.display()))
}

fn stage_key(step: &VerificationStep, inputs: &Inputs) -> Result<String, String> {
    let bytes = serde_json::to_vec(&(
        receipt::SCHEMA,
        step.label,
        step.arguments,
        step.rustdoc_flags,
        inputs,
    ))
    .map_err(|error| error.to_string())?;
    Ok(digest(&bytes))
}

fn execute_stage(
    step: &'static VerificationStep,
    options: &Options,
    root: &Path,
    directory: &Path,
    run_id: &str,
    initial: &Inputs,
    stages: &mut Vec<StageResult>,
) -> Result<(), String> {
    let before = snapshot(root, &options.external_inputs)?;
    if &before != initial {
        return Err("inputs changed between verification stages; no gate established".into());
    }
    let key = stage_key(step, &before)?;
    let receipt_path = directory
        .join("stages")
        .join(format!("{}-{key}.json", step.label));
    if options.reuse
        && let Some(previous) = StageReceipt::load_matching(
            &receipt_path,
            &key,
            &before,
            step.arguments,
            step.rustdoc_flags,
        )
    {
        eprintln!(
            "reused {} check ({:.2}s originally)",
            step.label, previous.seconds
        );
        stages.push(StageResult {
            label: step.label,
            key,
            reused: true,
            success: true,
            seconds: 0.0,
            receipt: Some(receipt_path),
            log: Some(previous.log),
        });
        return Ok(());
    }

    // A fresh failure disproves an earlier success for these exact inputs.
    match fs::remove_file(&receipt_path) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(error.to_string()),
    }

    let log_path = directory
        .join("logs")
        .join(format!("{run_id}-{}.log", step.label));
    let log =
        fs::File::create(&log_path).map_err(|error| format!("{}: {error}", log_path.display()))?;
    let stderr = log.try_clone().map_err(|error| error.to_string())?;
    eprintln!("running {} check; log: {}", step.label, log_path.display());
    let started = Instant::now();
    let cargo = env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo"));
    let mut command = Command::new(cargo);
    command
        .current_dir(root)
        .args(step.arguments)
        .env("CARGO_BUILD_JOBS", "1")
        .stdout(Stdio::from(log))
        .stderr(Stdio::from(stderr));
    if let Some(flags) = step.rustdoc_flags {
        command.env("RUSTDOCFLAGS", flags);
    }
    stages.push(StageResult {
        label: step.label,
        key: key.clone(),
        reused: false,
        success: false,
        seconds: 0.0,
        receipt: None,
        log: Some(log_path.clone()),
    });
    let attempted = command.status();
    let seconds = started.elapsed().as_secs_f64();
    let result = stages.last_mut().ok_or("missing stage report")?;
    result.seconds = seconds;
    let status = attempted.map_err(|error| format!("could not run {}: {error}", step.label))?;
    if !status.success() {
        if let Ok(log) = fs::read_to_string(&log_path) {
            eprint!("{log}");
        }
        return Err(format!(
            "{} check exited with {status}; log: {}",
            step.label,
            log_path.display()
        ));
    }
    let after = snapshot(root, &options.external_inputs)?;
    if before != after {
        return Err(format!(
            "inputs changed during {} check; no reusable success recorded",
            step.label
        ));
    }
    let log_sha256 = digest(&fs::read(&log_path).map_err(|error| error.to_string())?);
    let record = StageReceipt {
        schema: receipt::SCHEMA,
        key: key.clone(),
        arguments: step.arguments.iter().map(|s| (*s).to_owned()).collect(),
        rustdoc_flags: step.rustdoc_flags.map(str::to_owned),
        inputs: before,
        exit_code: 0,
        seconds,
        log: log_path,
        log_sha256,
    };
    save_json(&receipt_path, &record)?;
    eprintln!("{} check passed in {seconds:.2}s", step.label);
    result.success = true;
    result.receipt = Some(receipt_path);
    Ok(())
}

fn verify(options: &Options) -> Result<(), String> {
    let root = env::current_dir().map_err(|error| error.to_string())?;
    receipt::require_repository_root(&root)?;
    let directory = std::path::absolute(
        options
            .receipts
            .as_deref()
            .unwrap_or_else(|| Path::new("target/verification")),
    )
    .map_err(|error| error.to_string())?;
    for name in ["stages", "logs"] {
        fs::create_dir_all(directory.join(name)).map_err(|error| error.to_string())?;
    }
    receipt::require_ignored_output(&root, &directory)?;
    let run_id = format!(
        "{}-{}",
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|error| error.to_string())?
            .as_nanos(),
        std::process::id()
    );
    let started = Instant::now();
    let mut summary = RunSummary {
        schema: receipt::SCHEMA,
        complete_gate: options.stages.is_empty() || options.stages.len() == STEPS.len(),
        success: false,
        seconds: 0.0,
        stages: Vec::new(),
    };
    save_json(&directory.join("latest.json"), &summary)?;
    let result = (|| {
        let initial = snapshot(&root, &options.external_inputs)?;
        for step in STEPS {
            if options.stages.is_empty() || options.stages.iter().any(|label| label == step.label) {
                execute_stage(
                    step,
                    options,
                    &root,
                    &directory,
                    &run_id,
                    &initial,
                    &mut summary.stages,
                )?;
            }
        }
        if initial != snapshot(&root, &options.external_inputs)? {
            return Err("inputs changed across verification stages; no gate established".into());
        }
        for result in &summary.stages {
            let step = STEPS
                .iter()
                .find(|step| step.label == result.label)
                .ok_or("unknown recorded verification stage")?;
            if StageReceipt::load_matching(
                result
                    .receipt
                    .as_deref()
                    .ok_or("missing successful receipt")?,
                &result.key,
                &initial,
                step.arguments,
                step.rustdoc_flags,
            )
            .is_none()
            {
                return Err(format!(
                    "{} receipt or log changed during verification",
                    result.label
                ));
            }
        }
        Ok(())
    })();
    summary.seconds = started.elapsed().as_secs_f64();
    summary.success = result.is_ok();
    save_json(&directory.join(format!("run-{run_id}.json")), &summary)?;
    save_json(&directory.join("latest.json"), &summary)?;
    let reused = summary.stages.iter().filter(|stage| stage.reused).count();
    eprintln!(
        "{} {}: {} executed, {reused} reused, {:.2}s; summary: {}",
        if summary.complete_gate {
            "complete gate"
        } else {
            "partial verification"
        },
        if summary.success { "passed" } else { "failed" },
        summary.stages.len() - reused,
        summary.seconds,
        directory.join("latest.json").display()
    );
    result
}

fn main() -> ExitCode {
    let options = match options() {
        Ok(options) => options,
        Err(error) => {
            eprintln!(
                "{error}\nusage: cargo xtask verify [--step STAGE]... [--reuse] [--receipt-dir DIR] [--input FILE]...\n       cargo xtask inputs [--input FILE]..."
            );
            return ExitCode::from(2);
        }
    };
    let result = if options.inputs_only {
        (|| {
            let root = env::current_dir().map_err(|error| error.to_string())?;
            receipt::require_repository_root(&root)?;
            let pins = snapshot(&root, &options.external_inputs)?;
            println!(
                "{}",
                serde_json::to_string_pretty(&pins).map_err(|error| error.to_string())?
            );
            Ok(())
        })()
    } else {
        verify(&options)
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}
