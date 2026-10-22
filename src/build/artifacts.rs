use std::{
    fs::{self, OpenOptions},
    io::{self, Write},
    path::Path,
    process::{Command, Stdio},
};

pub(super) struct GeneratedArtifacts<'a> {
    pub project: &'a Path,
    pub target_directory: &'a Path,
    pub package_name: &'a str,
    pub target: &'a str,
    pub profile: &'a str,
    pub private_target: bool,
}

#[derive(Debug)]
pub(super) enum ArtifactFailure {
    Io(io::Error),
    Cleanup,
}

impl GeneratedArtifacts<'_> {
    // Copy out before cleanup; publish only after cleanup succeeds. Failure also
    // retires partial root artifacts, retaining source and diagnostics separately.
    #[cfg(test)]
    pub fn finish(
        &self,
        succeeded: bool,
        output: &Path,
        log: &Path,
    ) -> Result<(), ArtifactFailure> {
        self.finish_with_observation(succeeded, output, log, |_| Ok(()))
    }

    // Optional producer observation occurs on the copied staging object after
    // cleanup and before publication. It grants no immutable-execution promise.
    pub(super) fn finish_with_observation(
        &self,
        succeeded: bool,
        output: &Path,
        log: &Path,
        observe: impl FnOnce(&Path) -> io::Result<()>,
    ) -> Result<(), ArtifactFailure> {
        let linked = self.project.join("linked-program");
        let copied = if succeeded {
            fs::copy(
                self.target_directory
                    .join(self.target)
                    .join(if self.profile == "dev" {
                        "debug"
                    } else {
                        self.profile
                    })
                    .join(self.package_name),
                &linked,
            )
            .map(|_| ())
        } else {
            Ok(())
        };
        let cleaned = self.clean(log);
        let failure = match (copied, cleaned) {
            (Err(error), _) => Some(ArtifactFailure::Io(error)),
            (Ok(()), Err(_)) => Some(ArtifactFailure::Cleanup),
            (Ok(()), Ok(())) => None,
        };
        if let Some(failure) = failure {
            self.remove_staging(&linked, log)?;
            return Err(failure);
        }
        if succeeded && let Err(error) = observe(&linked) {
            self.remove_staging(&linked, log)?;
            return Err(ArtifactFailure::Io(error));
        }
        if succeeded && let Err(error) = fs::rename(&linked, output) {
            self.remove_staging(&linked, log)?;
            return Err(ArtifactFailure::Io(error));
        }
        Ok(())
    }

    fn clean(&self, log: &Path) -> io::Result<()> {
        let result = self.clean_inner(log);
        if let Err(error) = &result {
            record_cleanup_failure(log, error);
        }
        result
    }

    fn clean_inner(&self, log: &Path) -> io::Result<()> {
        let mut file = OpenOptions::new().append(true).open(log)?;
        writeln!(
            file,
            "\nCleaning generated Cargo package {}",
            self.package_name
        )?;
        let errors = file.try_clone()?;
        // Cargo owns its fingerprint, incremental and executable-alias layout.
        // Selecting this unique root package retains every shared dependency.
        let status = Command::new("cargo")
            .current_dir(self.project)
            .args([
                "clean",
                "--offline",
                "--locked",
                "--package",
                self.package_name,
                "--target",
                self.target,
                "--profile",
                self.profile,
            ])
            .arg("--target-dir")
            .arg(self.target_directory)
            .env("CARGO_BUILD_JOBS", "1")
            .env_remove("CARGO_BUILD_TARGET")
            .stdout(Stdio::from(file))
            .stderr(Stdio::from(errors))
            .status()?;
        if status.success() {
            if self.private_target {
                remove_if_present(self.target_directory)
            } else {
                Ok(())
            }
        } else {
            Err(io::Error::other("generated Cargo package cleanup failed"))
        }
    }

    fn remove_staging(&self, linked: &Path, log: &Path) -> Result<(), ArtifactFailure> {
        match fs::remove_file(linked) {
            Ok(()) => Ok(()),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
            Err(error) => {
                record_cleanup_failure(log, &error);
                Err(ArtifactFailure::Cleanup)
            }
        }
    }
}

fn remove_if_present(directory: &Path) -> io::Result<()> {
    match fs::remove_dir_all(directory) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error),
    }
}

fn record_cleanup_failure(log: &Path, error: &io::Error) {
    if let Ok(mut file) = OpenOptions::new().append(true).open(log) {
        let _ = writeln!(file, "generated artifact cleanup failed: {error}");
    }
}

#[cfg(all(test, target_arch = "x86_64", target_os = "linux", target_env = "gnu"))]
#[path = "artifacts_tests.rs"]
mod tests;
