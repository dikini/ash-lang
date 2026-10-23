//! Fixed-context applicability, sealed images and fixed one-shot FD launch.
//! This crate has no selected provider/foreign-adapter dependency. Producer data
//! and low-level sealed bytes are not protected approval.
#![cfg(all(target_os = "linux", target_arch = "x86_64", target_env = "gnu"))]
mod bootstrap_association;
mod linux;
mod protected;
mod outcome;
pub use outcome::OutcomeFrameKind;
mod running;
mod sealed;
pub use protected::{LaunchOutcome, PreparedImage, VerifiedRunning, launch_fixed, prepare, verify_running};
pub use sealed::{PreparationLimits, SealedData};

/// A refusal before any candidate startup. No variant permits fallback.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Refusal {
    /// Explicit byte/work/record bound exhausted.
    Resource,
    /// A file/syscall/required kernel facility was unavailable.
    Input,
    /// Malformed or unknown versioned input.
    Malformed,
    /// Exact expected data or object identity differs.
    Association,
    /// Administrator-established installation association is absent.
    MissingDeployment,
    /// Actual credentials/context/store are outside the fixed installation.
    Context,
    /// Required closure or reviewed premise applicability is incomplete.
    Incomplete,
    /// Immutable executable-object structural policy refused.
    Image,
}
#[derive(Debug)]
struct Budget {
    remaining: usize,
}
impl Budget {
    fn new(n: usize) -> Self {
        Self { remaining: n }
    }
    fn pay(&mut self, n: usize) -> Result<(), Refusal> {
        self.remaining = self.remaining.checked_sub(n).ok_or(Refusal::Resource)?;
        Ok(())
    }
}
fn io<T>(r: std::io::Result<T>) -> Result<T, Refusal> {
    r.map_err(|_| Refusal::Input)
}

#[cfg(test)]
fn test_directory(label: &str) -> std::path::PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let time = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    for _ in 0..32 {
        let path = std::env::temp_dir().join(format!(
            "ash-data-{label}-{}-{time}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        match std::fs::create_dir(&path) {
            Ok(()) => return path,
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(e) => panic!("exclusive data fixture: {e}"),
        }
    }
    panic!("fresh data fixture collision bound")
}
