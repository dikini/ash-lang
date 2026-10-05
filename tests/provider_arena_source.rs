use ash::{
    driver::{RunConfiguration, run_path_with_foreign_runtime},
    foreign::{ForeignRegistrations, arena_manifest, provider_manifest, runtime::ForeignRuntime},
    module::{ForeignRegistrationId, ModuleRoots},
};
use ash_foreign_adapter::{ArenaEvent, ArenaObservations, arena_binding};
use std::{path::PathBuf, sync::Arc};

fn configuration(name: &str) -> (RunConfiguration, ForeignRuntime, ArenaObservations) {
    let registrations = ForeignRegistrations::new([
        provider_manifest(ForeignRegistrationId::new(1)).unwrap(),
        arena_manifest(ForeignRegistrationId::new(2)).unwrap(),
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
                .join("tests/fixtures/provider-experiments/arena-basic")
                .join(name),
            roots: ModuleRoots::empty().with_foreign_registrations(registrations),
        },
        runtime,
        observations,
    )
}
#[test]
fn arena_acquires_queries_actual_usage_and_releases_through_public_driver() {
    for (name, expected, capacity, slots) in [
        ("entry.ash", "Completed((0, 64, 0, 4), Closed)", 64, 4),
        ("zero-entry.ash", "Completed((0, 0, 0, 0), Closed)", 0, 0),
    ] {
        let (configuration, mut runtime, observations) = configuration(name);
        let result = run_path_with_foreign_runtime(configuration, &mut runtime)
            .unwrap_or_else(|failure| panic!("{name}: {failure:?}"));
        assert_eq!(result.value_display(), expected);
        let events = observations.events();
        assert!(
            matches!(&events[..],[ArenaEvent::Acquired{activation:0,usage:first},ArenaEvent::Usage{activation:0,usage:second},ArenaEvent::Released{activation:0,host_teardown:false}]
            if first==second&&first.used_payload_bytes==0&&first.payload_capacity==capacity&&first.object_count==0&&first.object_capacity==slots)
        );
        assert_eq!(runtime.retained_owner_count(), 0);
    }
}
#[test]
fn repeated_and_nested_arenas_have_unique_native_owners_and_one_release_each() {
    let value = "Completed((0, 64, 0, 4), Closed)";
    for (name, expected, nested) in [
        ("repeated-entry.ash", format!("({value}, {value})"), false),
        (
            "nested-entry.ash",
            "Completed(Completed(((0, 64, 0, 4), (0, 16, 0, 2)), Closed), Closed)".into(),
            true,
        ),
    ] {
        let (configuration, mut runtime, observations) = configuration(name);
        let result = run_path_with_foreign_runtime(configuration, &mut runtime)
            .unwrap_or_else(|failure| panic!("{name}: {failure:?}"));
        assert_eq!(result.value_display(), expected);
        let events = observations.events();
        for activation in [0, 1] {
            assert_eq!(events.iter().filter(|event|matches!(event,ArenaEvent::Acquired{activation:found,..} if *found==activation)).count(),1);
            assert_eq!(events.iter().filter(|event|matches!(event,ArenaEvent::Usage{activation:found,..} if *found==activation)).count(),1);
            assert_eq!(events.iter().filter(|event|matches!(event,ArenaEvent::Released{activation:found,host_teardown:false} if *found==activation)).count(),1);
        }
        assert!(!events.iter().any(|event| matches!(
            event,
            ArenaEvent::Released {
                host_teardown: true,
                ..
            } | ArenaEvent::Refused
        )));
        if nested {
            let position = |activation| {
                events.iter().position(|event|matches!(event,ArenaEvent::Released{activation:found,..} if *found==activation)).unwrap()
            };
            assert!(position(1) < position(0));
        }
        assert_eq!(runtime.retained_owner_count(), 0);
    }
}
#[test]
fn arena_native_configuration_refusal_executes_no_body_or_release() {
    let (configuration, mut runtime, observations) = configuration("refused-entry.ash");
    let result = run_path_with_foreign_runtime(configuration, &mut runtime).unwrap();
    assert_eq!(result.value_display(), "NotAcquired(InvalidArenaConfig)");
    assert_eq!(observations.events(), vec![ArenaEvent::Refused]);
    assert_eq!(runtime.retained_owner_count(), 0);
}
#[test]
fn resource_dependent_arena_access_cannot_escape() {
    let (configuration, mut runtime, observations) = configuration("escape-entry.ash");
    let failure = run_path_with_foreign_runtime(configuration, &mut runtime)
        .expect_err("arena access escapes its scope");
    assert_eq!(failure.reason_code(), "type.resource-escape");
    assert!(failure.is_source_rejection());
    assert!(observations.events().is_empty());
}
