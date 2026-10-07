//! Minimum body-free memory registration for the scoped arena lifecycle.
//! Typed allocation, Layout, references and storage families are separate work.
use super::*;

/// Builds the minimal arena acquisition/usage/completion registration.
/// # Errors
/// Returns an error if the authored schema is invalid.
pub fn arena_manifest(
    id: ForeignRegistrationId,
) -> Result<ForeignManifest, ForeignRegistrationError> {
    ForeignManifest::new(
        "@foreign.memory",
        id,
        ForeignManifestSchema {
            types: vec![
                state("ArenaState", &["R"]),
                data("ArenaConfig", &[], &[("ArenaConfig", Some("Int, Int"))]),
                data(
                    "ArenaInitError",
                    &[],
                    &[
                        ("InvalidArenaConfig", None),
                        ("ArenaAllocationFailed", None),
                    ],
                ),
                data("ArenaFinishError", &[], &[("ArenaFinishInvariant", None)]),
                data(
                    "Acquire",
                    &["State", "E"],
                    &[("Acquired", Some("State")), ("Refused", Some("E"))],
                ),
                data(
                    "Finish",
                    &["State", "E"],
                    &[
                        ("Consumed", None),
                        ("ConsumedFailure", Some("E")),
                        ("Retained", Some("State, E")),
                    ],
                ),
            ],
            effects: vec![ForeignEffectDeclaration {
                name: "Arena".into(),
                parameters: vec!["R".into()],
                operations: vec![
                    operation(
                        "acquire",
                        "ArenaConfig -> Acquire<ArenaState<R>, ArenaInitError>",
                        ForeignOperationRole::Acquire,
                        vec![],
                        ForeignResultRelation::Acquire {
                            state: "ArenaState".into(),
                            error: "ArenaInitError".into(),
                            report: "Acquire".into(),
                            retained_parameters: vec![],
                        },
                    ),
                    operation(
                        "usage",
                        "ArenaState<R> -> (Int, Int, Int, Int)",
                        ForeignOperationRole::Borrow,
                        vec![vec![]],
                        ForeignResultRelation::Independent,
                    ),
                    operation(
                        "finish",
                        "ArenaState<R> -> Finish<ArenaState<R>, ArenaFinishError>",
                        ForeignOperationRole::Finish,
                        vec![vec![]],
                        ForeignResultRelation::Finish {
                            state: "ArenaState".into(),
                            error: "ArenaFinishError".into(),
                            report: "Finish".into(),
                        },
                    ),
                ],
            }],
            state_access: None,
            foundation: None,
        },
    )
}
