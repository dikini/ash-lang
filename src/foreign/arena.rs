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

/// Builds the explicit experimental typed-storage registration.
///
/// The lifecycle-only registration remains unchanged. Canonical binding keeps
/// this expanded registration closed until all connected consumers are ready.
/// # Errors
/// Returns an error when the authored schema is invalid.
pub fn typed_arena_manifest(id: ForeignRegistrationId) -> Result<ForeignManifest, ForeignRegistrationError> {
    let mut schema = arena_manifest(id)?.schema;
    schema.types.extend([
        ForeignTypeDeclaration {
            name: "LayoutWitness".into(), parameters: vec!["T".into()],
            category: ForeignTypeCategory::LayoutWitness { payload_parameter: 0 }, constructors: vec![],
        },
        ForeignTypeDeclaration {
            name: "Ref".into(), parameters: vec!["R".into(), "T".into()],
            category: ForeignTypeCategory::Reference { owner_parameter: 0, payload_parameter: 1 }, constructors: vec![],
        },
        data("AllocError", &[], &[("OutOfPayload", None), ("OutOfObjects", None), ("InvalidAlignment", None), ("InvalidPayload", None)]),
        data("AllocResult", &["T"], &[("Allocated", Some("T")), ("AllocationRefused", Some("AllocError"))]),
    ]);
    schema.foundation = Some(ForeignFoundationDeclaration {
        layout: ForeignLayoutDeclaration {
            name: "Layout".into(), parameter: "T".into(), witness: "LayoutWitness".into(),
            method: ForeignFoundationOperationDeclaration { name: "witness".into(), signature: "Unit -> LayoutWitness<T>".into() },
        },
        storage: ForeignStorageDeclaration {
            name: "Storage".into(), parameters: vec!["R".into(), "T".into()],
            owner_parameter: 0, payload_parameter: 1,
            state: "ArenaState".into(), reference: "Ref".into(),
            allocation_result: "AllocResult".into(), allocation_error: "AllocError".into(),
            allocated_constructor: "Allocated".into(), refused_constructor: "AllocationRefused".into(),
            store: ForeignFoundationOperationDeclaration { name: "store".into(), signature: "(ArenaState<R>, LayoutWitness<T>, Int, T) -> AllocResult<Ref<R, T>>".into() },
            load: ForeignFoundationOperationDeclaration { name: "load".into(), signature: "(ArenaState<R>, LayoutWitness<T>, Ref<R, T>) -> T".into() },
        },
    });
    ForeignManifest::new("@foreign.memory", id, schema)
}
