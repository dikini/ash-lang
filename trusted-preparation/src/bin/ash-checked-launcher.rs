//! Fixed installed launcher. No caller pathname, approval bit or environment
//! option selects authority; unsupported deployment refuses before child entry.
fn main() -> std::process::ExitCode {
    match ash_trusted_preparation::launch_fixed() {
        Ok(outcome) if outcome.child_succeeded() && outcome.stream_complete() => std::process::ExitCode::SUCCESS,
        _ => std::process::ExitCode::FAILURE,
    }
}
