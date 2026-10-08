//! Experimental phase observation. Feature-off builds retain ordinary policy.

#[cfg(feature = "resource-calibration")]
use std::{sync::OnceLock, time::Instant};

/// The diagnostic base applies once to structural owners and three times to Core.
#[derive(Clone, Copy, Debug)]
pub(crate) enum DiagnosticOwner {
    Structural,
    Core,
}

/// Apply an explicit finite allowance for the owner, otherwise retain normal policy.
#[inline]
pub(crate) fn limit(normal: usize, _owner: DiagnosticOwner) -> usize {
    #[cfg(feature = "resource-calibration")]
    {
        static BASE: OnceLock<Option<usize>> = OnceLock::new();
        let base = BASE.get_or_init(|| {
            std::env::var("ASH_CALIBRATION_LIMIT").ok().map(|value| {
                value
                    .parse::<usize>()
                    .ok()
                    .filter(|v| (1..=268_435_456).contains(v))
                    .expect("ASH_CALIBRATION_LIMIT must be between 1 and 268435456")
            })
        });
        if let Some(base) = base {
            return match _owner {
                DiagnosticOwner::Structural => *base,
                DiagnosticOwner::Core => base.saturating_mul(3),
            };
        }
    }
    normal
}

#[cfg(feature = "resource-calibration")]
#[inline]
pub(crate) fn observing() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("ASH_CALIBRATION_OBSERVE").is_ok_and(|v| v == "1"))
}

#[cfg(feature = "resource-calibration")]
fn memory() -> (Option<usize>, Option<usize>) {
    let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    let field = |key| {
        status.lines().find_map(|line| {
            line.strip_prefix(key)?
                .split_whitespace()
                .next()?
                .parse()
                .ok()
        })
    };
    (field("VmRSS:"), field("VmHWM:"))
}

#[cfg(feature = "resource-calibration")]
fn emit(value: serde_json::Value) {
    eprintln!("ASH_CALIBRATION {value}");
}

/// A phase ends explicitly on success; early exits produce incomplete records.
pub(crate) struct Phase {
    #[cfg(feature = "resource-calibration")]
    state: Option<(&'static str, Instant, Option<usize>)>,
}

impl Phase {
    #[inline]
    pub(crate) fn start(_phase: &'static str) -> Self {
        Self {
            #[cfg(feature = "resource-calibration")]
            state: observing().then(|| (_phase, Instant::now(), memory().0)),
        }
    }

    /// Report the ledger's supplied capacities; zero denotes a nonledger phase.
    #[inline]
    pub(crate) fn finish(mut self, _work: Option<usize>, _normal: usize, _effective: usize) {
        #[cfg(feature = "resource-calibration")]
        if let Some((phase, start, rss_start)) = self.state.take() {
            let wall_ns = start.elapsed().as_nanos();
            let (rss_end, peak) = memory();
            emit(serde_json::json!({
                "event": "phase", "phase": phase, "completed": true,
                "wall_ns": wall_ns, "rss_start_kib": rss_start,
                "rss_end_kib": rss_end, "process_peak_rss_kib": peak,
                "work_cumulative": _work,
                "normal_limit": (_normal != 0).then_some(_normal),
                "diagnostic_limit": (_effective != 0).then_some(_effective),
            }));
        }
        // Keep the same zero-cost interface in feature-off builds.
        #[cfg(not(feature = "resource-calibration"))]
        let _ = &mut self;
    }
}

#[cfg(feature = "resource-calibration")]
impl Drop for Phase {
    fn drop(&mut self) {
        if let Some((phase, start, rss_start)) = self.state.take() {
            let wall_ns = start.elapsed().as_nanos();
            let (rss_end, peak) = memory();
            emit(serde_json::json!({
                "event": "phase", "phase": phase, "completed": false,
                "wall_ns": wall_ns, "rss_start_kib": rss_start,
                "rss_end_kib": rss_end, "process_peak_rss_kib": peak,
            }));
        }
    }
}

/// Report supplied ledger capacities without consulting the diagnostic override.
#[inline]
pub(crate) fn work(
    _phase: &'static str,
    _used: usize,
    _normal: usize,
    _effective: usize,
    _completed: bool,
) {
    #[cfg(feature = "resource-calibration")]
    if observing() {
        emit(serde_json::json!({
            "event": "work", "phase": _phase, "work_cumulative": _used,
            "normal_limit": (_normal != 0).then_some(_normal),
            "diagnostic_limit": (_effective != 0).then_some(_effective),
            "completed": _completed,
        }));
    }
}
