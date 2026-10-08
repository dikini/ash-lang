//! Generated native resource workloads for the isolated calibration study.
#![cfg(feature = "resource-calibration")]

#[path = "support/sqlite_copying.rs"]
mod sqlite_copying;

#[test]
#[ignore = "explicit calibration measurement requires a generated fixture and session count"]
fn generated_resource_sessions_close_every_connection() {
    let entry = std::env::var_os("ASH_CALIBRATION_ENTRY")
        .expect("generated calibration source path is required");
    let sessions: usize = std::env::var("ASH_CALIBRATION_SESSIONS")
        .expect("generated session count is required")
        .parse()
        .expect("session count must be an integer");
    assert!((1..=64).contains(&sessions));
    let fixture = sqlite_copying::Fixture::new();
    std::fs::copy(entry, fixture.path("calibration-entry.ash")).unwrap();
    let (value, observations) = fixture.run("calibration-entry.ash");
    assert_eq!(value, "42");
    assert_eq!(observations.calls("open"), sessions);
    assert_eq!(observations.calls("close"), sessions);
    sqlite_copying::assert_finish_dispatches(&observations, 0, sessions);
}
