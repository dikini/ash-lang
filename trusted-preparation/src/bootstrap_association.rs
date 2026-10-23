//! Fixed administrator-established trusted-consumer source association.
//!
//! Configured deployments replace this literal as part of their independently
//! reviewed trusted-consumer build. The canonical source inventory binds these
//! exact bytes into both producer and generated-root identities. This is never
//! selected by request DATA, Cargo features, project arguments or environment.
//! Changing it requires a fresh whole-image artifact and protected approval.

pub(crate) struct Association {
    pub(crate) path: &'static str,
    pub(crate) sha256: &'static str,
}

/// The ordinary build has no installed administrator association.
pub(crate) static INSTALLED: Option<Association> = None;
