use std::{
    env,
    ffi::OsStr,
    process::{Command, ExitCode},
};

#[derive(Debug, Eq, PartialEq)]
struct VerificationStep {
    label: &'static str,
    arguments: &'static [&'static str],
    rustdoc_flags: Option<&'static str>,
}

const VERIFICATION_STEPS: &[VerificationStep] = &[
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
        label: "build",
        arguments: &["build", "--workspace", "--all-targets", "--locked"],
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

fn verification_steps() -> &'static [VerificationStep] {
    VERIFICATION_STEPS
}

fn verify() -> ExitCode {
    for step in verification_steps() {
        eprintln!("running {} check", step.label);

        let mut command = Command::new("cargo");
        command.args(step.arguments);
        if let Some(flags) = step.rustdoc_flags {
            command.env("RUSTDOCFLAGS", flags);
        }

        match command.status() {
            Ok(status) if status.success() => {}
            Ok(status) => {
                eprintln!("{} check exited with {status}", step.label);
                return ExitCode::FAILURE;
            }
            Err(error) => {
                eprintln!("could not run {} check: {error}", step.label);
                return ExitCode::FAILURE;
            }
        }
    }

    ExitCode::SUCCESS
}

fn main() -> ExitCode {
    let mut arguments = env::args_os();
    let _ = arguments.next();
    let command = arguments.next();
    let extra = arguments.next();

    if command.as_deref() == Some(OsStr::new("verify")) && extra.is_none() {
        verify()
    } else {
        eprintln!("usage: cargo xtask verify");
        ExitCode::from(2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verification_includes_every_required_check() {
        let labels: Vec<_> = verification_steps().iter().map(|step| step.label).collect();

        assert_eq!(
            labels,
            [
                "format",
                "metadata",
                "build",
                "clippy",
                "test",
                "documentation"
            ]
        );
    }
}
