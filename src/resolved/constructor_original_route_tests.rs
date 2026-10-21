//! Actual direct/reexport constructor routes preserve one defining original.

use super::*;

const PRODUCER: &str =
    include_str!("../../tests/fixtures/checked-constructor-closure/producer.ash");

#[derive(Clone, Copy)]
enum RouteControl {
    Canonical,
    MissingFacadeOriginal,
    RemintedFacadeOriginal,
}

fn authenticate_default(summary: &ExportSummary) -> Result<(), ResolvedBuildFailure> {
    summary.authenticate(
        &mut TypeWorkBudget::default(),
        &mut crate::interface::InterfaceConstraintBudget::default(),
    )
}

fn check_routes(control: RouteControl) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-constructor-original-routes-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    std::fs::write(directory.join("native.ash"), PRODUCER).unwrap();
    std::fs::write(
        directory.join("facade.ash"),
        "pub import native (Envelope, make, inspect)\n",
    )
    .unwrap();
    // Both constructor occurrences are intentional: this reaches real duplicate
    // constructor retention instead of comparing only outward global types.
    std::fs::write(directory.join("entry.ash"),
        "import @builtin.foreign as Foreign\nimport native as Native\nimport facade as Facade\nmain : Unit -> Foreign.CheckedCall<Int>\nmain () = match Facade.make 7 {\n    Native.Envelope(leaf) => Facade.inspect (Facade.Envelope leaf)\n}\n").unwrap();
    let graph = crate::module::load_module_graph(
        &directory.join("entry.ash"),
        &crate::module::ModuleRoots::empty(),
    )
    .unwrap();
    std::fs::remove_dir_all(directory).unwrap();
    let module_named = |name: &str| {
        graph
            .modules()
            .iter()
            .find(|loaded| {
                std::path::Path::new(loaded.source().display_path()).file_name()
                    == Some(std::ffi::OsStr::new(name))
            })
            .unwrap()
            .id()
    };
    let native = module_named("native.ash");
    let facade = module_named("facade.ash");
    let mut summaries: Vec<ExportSummary> = Vec::new();
    for loaded in graph.modules() {
        if loaded.id() == graph.entry() {
            let native_index = summaries
                .iter()
                .position(|summary| summary.module == native)
                .unwrap();
            let facade_index = summaries
                .iter()
                .position(|summary| summary.module == facade)
                .unwrap();
            let direct = &summaries[native_index].constructors["Envelope"];
            let forwarded = &summaries[facade_index].constructors["Envelope"];
            assert_eq!(direct.id, forwarded.id);
            assert!(direct.original.is_some());
            assert_eq!(
                direct.original, forwarded.original,
                "facade must forward the exact defining registry reference"
            );
            authenticate_default(&summaries[native_index]).unwrap();
            authenticate_default(&summaries[facade_index]).unwrap();
            let dependencies = loaded
                .dependencies()
                .iter()
                .map(|edge| {
                    crate::resolve::DependencyExports::new(
                        edge,
                        summaries
                            .iter()
                            .find(|summary| summary.module == edge.target())
                            .unwrap(),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>();
            let canonical =
                crate::resolve::resolve_checked_foreign_module(loaded, &dependencies).unwrap();
            crate::elaborate::check_module(canonical).unwrap();
            match control {
                RouteControl::Canonical => return,
                RouteControl::MissingFacadeOriginal => {
                    assert!(
                        summaries[facade_index]
                            .constructors
                            .get_mut("Envelope")
                            .unwrap()
                            .original
                            .take()
                            .is_some()
                    );
                    assert_eq!(
                        authenticate_default(&summaries[facade_index]),
                        Err(ResolvedBuildFailure::InvalidState)
                    );
                }
                RouteControl::RemintedFacadeOriginal => {
                    let reminted = summaries[facade_index].constructors["Envelope"]
                        .original
                        .as_ref()
                        .unwrap()
                        .reminted_for_test();
                    summaries[facade_index]
                        .constructors
                        .get_mut("Envelope")
                        .unwrap()
                        .original = Some(reminted);
                    assert_ne!(
                        summaries[native_index].constructors["Envelope"].original,
                        summaries[facade_index].constructors["Envelope"].original
                    );
                    authenticate_default(&summaries[facade_index]).unwrap();
                }
            }
        }
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                crate::resolve::DependencyExports::new(
                    edge,
                    summaries
                        .iter()
                        .find(|summary| summary.module == edge.target())
                        .unwrap(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let resolved = crate::resolve::resolve_checked_foreign_module(loaded, &dependencies);
        if loaded.id() == graph.entry() {
            let error = match resolved {
                Err(crate::resolve::ResolveModuleError::Resolution(error)) => error,
                other => panic!("expected actual constructor route refusal: {other:?}"),
            };
            assert_eq!(error.reason, crate::resolve::ResolveReason::InternalState);
            match control {
                RouteControl::MissingFacadeOriginal => assert_eq!(
                    error.subject_fact(),
                    Some((
                        "cause",
                        "resolver-internal-cause",
                        "dependency-summary-invalid"
                    ))
                ),
                RouteControl::RemintedFacadeOriginal => assert_eq!(
                    error.work_state_context(),
                    Some(("alternate-constructor-fact", "mismatch"))
                ),
                RouteControl::Canonical => unreachable!(),
            }
            return;
        }
        summaries.push(
            crate::elaborate::check_module(resolved.unwrap())
                .unwrap()
                .into_exports(),
        );
    }
    panic!("entry missing");
}

#[test]
fn constructor_original_routes_share_defining_arc_and_check_cross_route_consumer() {
    check_routes(RouteControl::Canonical);
}

#[test]
fn constructor_original_routes_reject_missing_facade_original() {
    check_routes(RouteControl::MissingFacadeOriginal);
}

#[test]
fn constructor_original_routes_reject_reminted_facade_original() {
    check_routes(RouteControl::RemintedFacadeOriginal);
}
