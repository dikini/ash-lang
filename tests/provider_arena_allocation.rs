//! Connected A-0 scalar storage gate using the explicit typed registration.
//! Source range cases cover the maximum signed value and upper overflow. Ash
//! rejects negative literals; minimum/lower-overflow cases remain native codec
//! evidence in foreign-adapter/src/arena_codec.rs, without a new source API.

use ash::{
    driver::{RunConfiguration, run_path_with_foreign_runtime},
    foreign::{
        ForeignRegistrations, provider_manifest, runtime::ForeignRuntime, typed_arena_manifest,
    },
    module::{ForeignRegistrationId, ModuleRoots},
};
use ash_foreign_adapter::{ArenaEvent, ArenaObservations, arena_binding};
use std::{path::PathBuf, sync::Arc};

fn configuration(name: &str) -> (RunConfiguration, ForeignRuntime, ArenaObservations) {
    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
        typed_arena_manifest(ForeignRegistrationId::new(2)).unwrap(),
    ])
    .unwrap();
    let observations = ArenaObservations::default();
    let binding = arena_binding(
        Arc::clone(registrations.get("@foreign.memory").unwrap()),
        observations.clone(),
    )
    .unwrap();
    let runtime = ForeignRuntime::new(vec![binding]).unwrap();
    (
        RunConfiguration {
            entry: PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/provider-experiments/arena-typed")
                .join(name),
            roots: ModuleRoots::empty().with_foreign_registrations(registrations),
        },
        runtime,
        observations,
    )
}
#[test]
fn ash_allocates_and_reads_native_storage_before_arena_completion() {
    require_connected_typed_storage();
}

#[test]
fn typed_capacity_alignment_and_refusal_cases_preserve_actual_usage() {
    for (name, expected, capacity, slots, expected_stores, expected_loads) in [
        (
            "multiple-entry.ash",
            "Completed((41, true, (9, 9, 2, 2)), Closed)",
            9,
            2,
            &[(8, 8, 8), (1, 1, 9)][..],
            &[0, 1][..],
        ),
        (
            "payload-refusal-entry.ash",
            "Completed((OutOfPayload, true, (1, 8, 1, 2)), Closed)",
            8,
            2,
            &[(1, 1, 1)][..],
            &[0][..],
        ),
        (
            "object-refusal-entry.ash",
            "Completed((OutOfObjects, 41, (8, 16, 1, 1)), Closed)",
            16,
            1,
            &[(8, 8, 8)][..],
            &[0][..],
        ),
        (
            "range-refusal-entry.ash",
            "Completed((InvalidPayload, 41, (8, 16, 1, 2)), Closed)",
            16,
            2,
            &[(8, 8, 8)][..],
            &[0][..],
        ),
        (
            "maximum-integer-entry.ash",
            "Completed((9223372036854775807, (8, 8, 1, 1)), Closed)",
            8,
            1,
            &[(8, 8, 8)][..],
            &[0][..],
        ),
        (
            "source-refusal-entry.ash",
            "Completed((InvalidPayload, (0, 8, 0, 1)), Closed)",
            8,
            1,
            &[][..],
            &[][..],
        ),
        (
            "source-load-override-entry.ash",
            "Completed((99, (8, 8, 1, 1)), Closed)",
            8,
            1,
            &[(8, 8, 8)][..],
            &[][..],
        ),
        (
            "source-allocation-reuse-entry.ash",
            "Completed((41, (8, 16, 1, 2)), Closed)",
            16,
            2,
            &[(8, 8, 8)][..],
            &[0][..],
        ),
        (
            "imported-implementation-entry.ash",
            "Completed((Allocated(41), (8, 8, 1, 1)), Closed)",
            8,
            1,
            &[(8, 8, 8)][..],
            &[0][..],
        ),
        (
            "unit-entry.ash",
            "Completed(((), (), (0, 0, 2, 2)), Closed)",
            0,
            2,
            &[(0, 1, 0), (0, 1, 0)][..],
            &[0, 1][..],
        ),
        (
            "aligned-unit-entry.ash",
            "Completed(((), (64, 64, 2, 2)), Closed)",
            64,
            2,
            &[(1, 1, 1), (0, 1, 64)][..],
            &[1][..],
        ),
        (
            "alignment-refusal-entry.ash",
            "Completed((InvalidAlignment, 41, (8, 16, 1, 2)), Closed)",
            16,
            2,
            &[(8, 8, 8)][..],
            &[0][..],
        ),
    ] {
        let (configuration, mut runtime, observations) = configuration(name);
        let result = run_path_with_foreign_runtime(configuration, &mut runtime)
            .unwrap_or_else(|failure| panic!("{name}: {failure:?}"));
        assert_eq!(result.value_display(), expected, "{name}");
        let events = observations.events();
        let Some(ArenaEvent::Acquired {
            activation,
            usage: initial,
        }) = events.first()
        else {
            panic!("expected native acquisition: {name}: {events:?}");
        };
        assert_eq!(initial.used_payload_bytes, 0, "{name}");
        assert_eq!(initial.object_count, 0, "{name}");
        assert_eq!(initial.payload_capacity, capacity, "{name}");
        assert_eq!(initial.object_capacity, slots, "{name}");
        let stores_end = 1 + expected_stores.len();
        let loads_end = stores_end + expected_loads.len();
        assert_eq!(events.len(), loads_end + 2, "{name}: {events:?}");
        assert!(
            events[1..stores_end]
                .iter()
                .all(|event| matches!(event, ArenaEvent::Stored { .. })),
            "stores must precede loads without extra native events: {name}: {events:?}"
        );
        assert!(
            events[stores_end..loads_end]
                .iter()
                .all(|event| matches!(event, ArenaEvent::Loaded { .. })),
            "every expected read must reach native storage: {name}: {events:?}"
        );
        assert!(
            matches!(events[loads_end], ArenaEvent::Usage { .. }),
            "usage must follow the actual stores and loads: {name}: {events:?}"
        );
        assert_eq!(
            events
                .iter()
                .filter(|event| matches!(event, ArenaEvent::Acquired { .. }))
                .count(),
            1,
            "{name}"
        );
        let stored: Vec<_> = events
            .iter()
            .filter_map(|event| {
                if let ArenaEvent::Stored {
                    activation: found,
                    allocation,
                    layout,
                    usage,
                } = event
                {
                    assert_eq!(found, activation, "{name}");
                    Some((*allocation, *layout, *usage))
                } else {
                    None
                }
            })
            .collect();
        assert_eq!(stored.len(), expected_stores.len(), "{name}: {events:?}");
        for (index, ((allocation, layout, usage), &(extent, alignment, used))) in
            stored.iter().zip(expected_stores).enumerate()
        {
            assert_eq!(layout.size(), extent, "{name}");
            assert_eq!(layout.natural_alignment(), alignment, "{name}");
            assert_eq!(usage.used_payload_bytes, used, "{name}");
            assert_eq!(usage.object_count, index + 1, "{name}");
            assert_eq!(usage.payload_capacity, capacity, "{name}");
            assert_eq!(usage.object_capacity, slots, "{name}");
            for (previous, _, _) in &stored[..index] {
                assert_ne!(allocation, previous, "{name}");
                assert_eq!(allocation.owner_id(), previous.owner_id(), "{name}");
            }
        }
        let final_usage = stored.last().map_or(*initial, |(_, _, usage)| *usage);
        let loaded: Vec<_> = events
            .iter()
            .filter_map(|event| {
                if let ArenaEvent::Loaded {
                    activation: found,
                    allocation,
                    layout,
                    bytes_read,
                    usage,
                } = event
                {
                    assert_eq!(found, activation, "{name}");
                    assert_eq!(*usage, final_usage, "loads must preserve counters: {name}");
                    Some((*allocation, *layout, *bytes_read))
                } else {
                    None
                }
            })
            .collect();
        assert_eq!(loaded.len(), expected_loads.len(), "{name}: {events:?}");
        for ((allocation, layout, bytes_read), &stored_index) in loaded.iter().zip(expected_loads) {
            let (published, published_layout, _) = stored[stored_index];
            assert_eq!(*allocation, published, "{name}");
            assert_eq!(*layout, published_layout.tag(), "{name}");
            assert_eq!(*bytes_read, published_layout.size(), "{name}");
        }
        let queried: Vec<_> = events
            .iter()
            .filter_map(|event| {
                if let ArenaEvent::Usage {
                    activation: found,
                    usage,
                } = event
                {
                    assert_eq!(found, activation, "{name}");
                    Some(*usage)
                } else {
                    None
                }
            })
            .collect();
        assert_eq!(
            queried,
            vec![final_usage],
            "refusal/load must preserve actual usage: {name}"
        );
        assert!(
            matches!(events.last(), Some(ArenaEvent::Released {
            activation: found, host_teardown: false,
        }) if found == activation),
            "{name}: {events:?}"
        );
        if name == "unit-entry.ash" {
            let stored: Vec<_> = events
                .iter()
                .filter_map(|event| {
                    if let ArenaEvent::Stored {
                        allocation, usage, ..
                    } = event
                    {
                        assert_eq!(usage.used_payload_bytes, 0);
                        Some(*allocation)
                    } else {
                        None
                    }
                })
                .collect();
            let loaded: Vec<_> = events
                .iter()
                .filter_map(|event| {
                    if let ArenaEvent::Loaded {
                        allocation,
                        bytes_read,
                        ..
                    } = event
                    {
                        assert_eq!(*bytes_read, 0);
                        Some(*allocation)
                    } else {
                        None
                    }
                })
                .collect();
            assert_eq!(stored.len(), 2);
            assert_ne!(stored[0], stored[1]);
            assert_eq!(stored[0].owner_id(), stored[1].owner_id());
            assert_eq!(loaded, stored);
        }
        assert_eq!(
            events
                .iter()
                .filter(|event| matches!(
                    event,
                    ArenaEvent::Released {
                        host_teardown: false,
                        ..
                    }
                ))
                .count(),
            1,
            "{name}"
        );
        assert!(
            !events.iter().any(|event| matches!(
                event,
                ArenaEvent::Released {
                    host_teardown: true,
                    ..
                }
            )),
            "{name}"
        );
        assert_eq!(runtime.retained_owner_count(), 0);
    }
}

#[test]
fn attached_family_preserves_handler_outward_storage_requests() {
    require_connected_typed_storage();
    let (configuration, mut runtime, observations) =
        configuration("outward-family-refusal-entry.ash");
    let failure = run_path_with_foreign_runtime(configuration, &mut runtime)
        .expect_err("body demand must not discharge the handlers' outward Bool request");
    assert!(failure.is_source_rejection(), "{failure:?}");
    let Some(ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(diagnostic))) =
        failure.pipeline_failure()
    else {
        panic!("expected the handlers' outward owner escape after successful imports: {failure:?}");
    };
    assert_eq!(
        diagnostic.reason,
        ash::elaborate::TypeReason::ResourceEscape,
        "{failure:?}"
    );
    let source = failure
        .sources()
        .iter()
        .find(|source| {
            std::path::Path::new(source.display_path())
                .file_name()
                .and_then(|name| name.to_str())
                == Some("outward-family-refusal-entry.ash")
        })
        .expect("the outward-request refusal must retain its entry source");
    assert_eq!(
        source.text(),
        include_str!("fixtures/provider-experiments/arena-typed/outward-family-refusal-entry.ash")
    );
    let start = source.text().find("resource Memory.Arena<R>").unwrap();
    let end = source.text().rfind('}').unwrap() + 1;
    let expected_span = source
        .span(
            ash::source::ByteRange::new(u32::try_from(start).unwrap(), u32::try_from(end).unwrap())
                .unwrap(),
        )
        .unwrap();
    // The outward row retains R. Its escape check labels the resource
    // expression as both the outward computation and its acquisition.
    assert_eq!(diagnostic.primary.span(), expected_span, "{failure:?}");
    assert_eq!(diagnostic.related.len(), 1, "{failure:?}");
    assert_eq!(diagnostic.related[0].span(), expected_span, "{failure:?}");
    assert!(observations.events().is_empty());
    assert_eq!(runtime.retained_owner_count(), 0);
}

/// These refusals count only after this same registration has actually reached
/// native storage; an earlier closed-admission failure cannot satisfy them.
fn require_connected_typed_storage() {
    let (configuration, mut runtime, observations) = configuration("allocation-entry.ash");
    let result = run_path_with_foreign_runtime(configuration, &mut runtime)
        .unwrap_or_else(|failure| panic!("typed arena allocation: {failure:?}"));
    assert_eq!(result.value_display(), "Completed(41, Closed)");
    let work = result.compilation_work();
    for (expected_phase, observed) in [
        (
            ash::compiler_work::CompilationPhase::SourceChecking,
            work.source_checking,
        ),
        (
            ash::compiler_work::CompilationPhase::FinalElaboration,
            work.final_elaboration,
        ),
        (
            ash::compiler_work::CompilationPhase::IndependentCore,
            work.independent_core,
        ),
    ] {
        let cost = observed.expect("connected storage must complete all compilation phases");
        assert_eq!(cost.phase, expected_phase);
        assert!(cost.completed, "{cost:?}");
        assert!(
            !matches!(
                cost.assessment(),
                ash::compiler_work::WorkAssessment::OutsideAllowance { .. }
            ),
            "{cost:?}"
        );
    }
    let events = observations.events();
    let [
        ArenaEvent::Acquired { activation, .. },
        ArenaEvent::Stored {
            activation: stored_activation,
            allocation,
            layout,
            usage,
        },
        ArenaEvent::Loaded {
            activation: loaded_activation,
            allocation: loaded,
            layout: loaded_layout,
            bytes_read,
            usage: loaded_usage,
        },
        ArenaEvent::Released {
            activation: released_activation,
            host_teardown: false,
        },
    ] = events.as_slice()
    else {
        panic!("expected actual native store/read before one completion: {events:?}");
    };
    assert_eq!(stored_activation, activation);
    assert_eq!(loaded_activation, activation);
    assert_eq!(released_activation, activation);
    assert_eq!(loaded, allocation);
    assert_eq!(*loaded_layout, layout.tag());
    assert_eq!(*bytes_read, 8);
    assert_eq!(layout.size(), 8);
    assert_eq!(layout.natural_alignment(), 8);
    assert_eq!(usage.used_payload_bytes, 8);
    assert_eq!(usage.payload_capacity, 8);
    assert_eq!(usage.object_count, 1);
    assert_eq!(usage.object_capacity, 1);
    assert_eq!(loaded_usage, usage);
    assert_eq!(runtime.retained_owner_count(), 0);
}

#[test]
fn references_cannot_escape_or_change_owner_and_numeric_tuples_grant_no_authority() {
    require_connected_typed_storage();
    for (name, reason) in [
        (
            "reference-escape-entry.ash",
            ash::elaborate::TypeReason::ResourceEscape,
        ),
        (
            "wrong-owner-entry.ash",
            ash::elaborate::TypeReason::Argument,
        ),
        (
            "fabricated-layout-entry.ash",
            ash::elaborate::TypeReason::Argument,
        ),
        (
            "fabricated-reference-entry.ash",
            ash::elaborate::TypeReason::Argument,
        ),
    ] {
        let (configuration, mut runtime, observations) = configuration(name);
        let failure = run_path_with_foreign_runtime(configuration, &mut runtime)
            .expect_err("invalid opaque authority must fail before native access");
        let Some(ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(
            diagnostic,
        ))) = failure.pipeline_failure()
        else {
            panic!("expected connected source typing refusal for {name}: {failure:?}");
        };
        assert_eq!(diagnostic.reason, reason, "{name}: {failure:?}");
        assert!(failure.is_source_rejection(), "{name}: {failure:?}");
        assert!(
            observations.events().is_empty(),
            "{name}: {:?}",
            observations.events()
        );
        assert_eq!(runtime.retained_owner_count(), 0, "{name}");
    }
}

#[test]
fn source_cannot_supply_sealed_layout_through_impl_or_lexical_evidence() {
    require_connected_typed_storage();
    for name in [
        "layout-impl-refusal-entry.ash",
        "layout-with-refusal-entry.ash",
    ] {
        let (configuration, mut runtime, observations) = configuration(name);
        let failure = run_path_with_foreign_runtime(configuration, &mut runtime)
            .expect_err("source evidence must not forge the registered Layout interface");
        let Some(ash::driver::PipelineFailure::Resolution(diagnostic)) = failure.pipeline_failure()
        else {
            panic!("expected sealed Layout resolution refusal for {name}: {failure:?}");
        };
        assert_eq!(
            diagnostic.reason,
            ash::resolve::ResolveReason::SealedProvider,
            "{name}: {failure:?}"
        );
        assert!(failure.is_source_rejection(), "{name}: {failure:?}");
        assert!(
            observations.events().is_empty(),
            "{name}: {:?}",
            observations.events()
        );
        assert_eq!(runtime.retained_owner_count(), 0, "{name}");
    }
}

#[test]
fn ordinary_aggregate_and_closure_can_use_a_reference_but_cannot_carry_it_out() {
    require_connected_typed_storage();
    let (positive_configuration, mut runtime, observations) =
        configuration("reference-capture-entry.ash");
    let result = run_path_with_foreign_runtime(positive_configuration, &mut runtime)
        .unwrap_or_else(|failure| {
            panic!("useful scalar reference-capture prerequisite: {failure:?}")
        });
    assert_eq!(
        result.value_display(),
        "Completed((82, (8, 8, 1, 1)), Closed)"
    );
    let events = observations.events();
    let [
        ArenaEvent::Acquired {
            activation,
            usage: initial,
        },
        ArenaEvent::Stored {
            activation: stored_activation,
            allocation,
            layout,
            usage,
        },
        ArenaEvent::Loaded {
            activation: loaded_activation,
            allocation: loaded,
            layout: loaded_layout,
            bytes_read,
            usage: loaded_usage,
        },
        ArenaEvent::Usage {
            activation: queried_activation,
            usage: queried_usage,
        },
        ArenaEvent::Released {
            activation: released_activation,
            host_teardown: false,
        },
    ] = events.as_slice()
    else {
        panic!(
            "the aggregate/closure prerequisite must use real storage and complete once: {events:?}"
        );
    };
    for found in [
        stored_activation,
        loaded_activation,
        queried_activation,
        released_activation,
    ] {
        assert_eq!(found, activation);
    }
    assert_eq!(initial.used_payload_bytes, 0);
    assert_eq!(initial.object_count, 0);
    assert_eq!(initial.payload_capacity, 8);
    assert_eq!(initial.object_capacity, 1);
    assert_eq!(layout.size(), 8);
    assert_eq!(layout.natural_alignment(), 8);
    assert_eq!(loaded, allocation);
    assert_eq!(*loaded_layout, layout.tag());
    assert_eq!(*bytes_read, 8);
    assert_eq!(usage.used_payload_bytes, 8);
    assert_eq!(usage.object_count, 1);
    assert_eq!(usage.payload_capacity, 8);
    assert_eq!(usage.object_capacity, 1);
    assert_eq!(loaded_usage, usage);
    assert_eq!(queried_usage, usage);
    assert_eq!(runtime.retained_owner_count(), 0);

    for name in [
        "reference-aggregate-escape-entry.ash",
        "reference-closure-escape-entry.ash",
    ] {
        let (configuration, mut runtime, observations) = configuration(name);
        let failure = run_path_with_foreign_runtime(configuration, &mut runtime).expect_err(
            "an extracted Ref remains dependent through an ordinary aggregate or closure",
        );
        let Some(ash::driver::PipelineFailure::Typing(ash::elaborate::TypeError::Source(
            diagnostic,
        ))) = failure.pipeline_failure()
        else {
            panic!("expected owner escape typing refusal for {name}: {failure:?}");
        };
        assert_eq!(
            diagnostic.reason,
            ash::elaborate::TypeReason::ResourceEscape,
            "{name}: {failure:?}"
        );
        // The intended owner-escape reason is exact. Pin its source location
        // only after the authorized executable gate establishes that location.
        assert!(failure.is_source_rejection(), "{name}: {failure:?}");
        assert!(
            observations.events().is_empty(),
            "{name}: {:?}",
            observations.events()
        );
        assert_eq!(runtime.retained_owner_count(), 0, "{name}");
    }
}

#[test]
fn grouped_scalar_storage_survives_resume_and_runs_cleanup_before_owned_discard_completion() {
    for (name, expected, expected_loads) in [
        (
            "grouped-resume-entry.ash",
            "Completed((82, true), Closed)",
            &[0, 0, 1, 0][..],
        ),
        ("grouped-discard-entry.ash", "(42, 41)", &[0, 1][..]),
    ] {
        let (configuration, mut runtime, observations) = configuration(name);
        let result = run_path_with_foreign_runtime(configuration, &mut runtime)
            .unwrap_or_else(|failure| panic!("grouped scalar control {name}: {failure:?}"));
        assert_eq!(result.value_display(), expected, "{name}");
        let events = observations.events();
        let Some(ArenaEvent::Acquired {
            activation,
            usage: initial,
        }) = events.first()
        else {
            panic!("grouped control must acquire actual native storage: {name}: {events:?}");
        };
        assert_eq!(initial.used_payload_bytes, 0, "{name}");
        assert_eq!(initial.object_count, 0, "{name}");
        assert_eq!(initial.payload_capacity, 9, "{name}");
        assert_eq!(initial.object_capacity, 2, "{name}");
        // Exact event positions exclude reacquisition, extra publication,
        // abandoned-body reads, host teardown, and completion before cleanup.
        assert_eq!(events.len(), expected_loads.len() + 4, "{name}: {events:?}");
        let mut stored = Vec::new();
        for (index, (extent, alignment, used)) in [(8, 8, 8), (1, 1, 9)].into_iter().enumerate() {
            let ArenaEvent::Stored {
                activation: found,
                allocation,
                layout,
                usage,
            } = &events[index + 1]
            else {
                panic!(
                    "both selected scalar family members must publish before capture: {name}: {events:?}"
                );
            };
            assert_eq!(found, activation, "{name}");
            assert_eq!(layout.size(), extent, "{name}");
            assert_eq!(layout.natural_alignment(), alignment, "{name}");
            assert_eq!(usage.used_payload_bytes, used, "{name}");
            assert_eq!(usage.object_count, index + 1, "{name}");
            assert_eq!(usage.payload_capacity, 9, "{name}");
            assert_eq!(usage.object_capacity, 2, "{name}");
            stored.push((*allocation, *layout, *usage));
        }
        assert_ne!(stored[0].0, stored[1].0, "{name}");
        assert_eq!(stored[0].0.owner_id(), stored[1].0.owner_id(), "{name}");
        for (event, &stored_index) in events[3..events.len() - 1].iter().zip(expected_loads) {
            let ArenaEvent::Loaded {
                activation: found,
                allocation,
                layout,
                bytes_read,
                usage,
            } = event
            else {
                panic!(
                    "every grouped continuation/cleanup operation must be a real native load: {name}: {events:?}"
                );
            };
            let (published, published_layout, _) = stored[stored_index];
            assert_eq!(found, activation, "{name}");
            assert_eq!(*allocation, published, "{name}");
            assert_eq!(*layout, published_layout.tag(), "{name}");
            assert_eq!(*bytes_read, published_layout.size(), "{name}");
            assert_eq!(
                *usage, stored[1].2,
                "reads preserve both published objects: {name}"
            );
        }
        assert!(
            matches!(events.last(), Some(ArenaEvent::Released {
            activation: found, host_teardown: false,
        }) if found == activation),
            "{name}: {events:?}"
        );
        assert_eq!(runtime.retained_owner_count(), 0, "{name}");
    }
}
