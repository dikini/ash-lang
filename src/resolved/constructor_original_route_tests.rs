//! Actual direct/reexport constructor routes preserve one defining original.

use super::*;

const PRODUCER: &str = r"type Leaf = Leaf(Int)
type Donor = Donor(Int)
type Spare = Spare(Int)
pub type Envelope = Envelope(Leaf)
pub type Witness = Witness(Donor)
pub make : Int -> Envelope
make value = Envelope (Leaf value)
pub inspect : Envelope -> Int
inspect envelope = match envelope {
    Envelope(Leaf(value)) => value
}
";

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
        "import native as Native\nimport facade as Facade\nmain : Unit -> Int\nmain () = match Facade.make 7 {\n    Native.Envelope(leaf) => Facade.inspect (Facade.Envelope leaf)\n}\n").unwrap();
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
            let canonical = crate::resolve::resolve_module(loaded, &dependencies).unwrap();
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
        let resolved = crate::resolve::resolve_module(loaded, &dependencies);
        if loaded.id() == graph.entry() {
            let error = match resolved {
                Err(crate::resolve::ResolveModuleError::Resolution(error)) => error,
                other => panic!("expected actual constructor route refusal: {other:?}"),
            };
            assert_eq!(error.reason, crate::resolve::ResolveReason::InternalState);
            match control {
                RouteControl::MissingFacadeOriginal | RouteControl::RemintedFacadeOriginal => {
                    assert_eq!(
                        error.work_state_context(),
                        Some(("alternate-constructor-fact", "mismatch"))
                    )
                }
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

// Keep Leaf reachable only through constructor payload metadata. Scalar
// globals make the no-outward/no-capture checks nonvacuous; the separate
// ordinary producer above retains real construction and reexport coverage.
fn constructor_authority_fixture() -> (ExportSummary, ResolvedModule) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-constructor-authority-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let declarations = PRODUCER.split_once("pub make :").unwrap().0;
    std::fs::write(directory.join("producer.ash"), format!(
        "{declarations}pub make : Int -> Int\nmake value = value\npub inspect : Int -> Int\ninspect value = value\n"
    )).unwrap();
    std::fs::write(
        directory.join("entry.ash"),
        "import producer as Producer\nmain : Unit -> Int\nmain () = Producer.inspect (Producer.make 7)\n",
    )
    .unwrap();
    let graph = crate::module::load_module_graph(
        &directory.join("entry.ash"),
        &crate::module::ModuleRoots::empty(),
    )
    .unwrap();
    std::fs::remove_dir_all(directory).unwrap();
    let producer = graph
        .modules()
        .iter()
        .find(|loaded| {
            std::path::Path::new(loaded.source().display_path()).file_name()
                == Some(std::ffi::OsStr::new("producer.ash"))
        })
        .unwrap()
        .id();
    let mut summaries: Vec<ExportSummary> = Vec::new();
    for loaded in graph.modules() {
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
        let resolved = crate::resolve::resolve_module(loaded, &dependencies).unwrap();
        if loaded.id() == graph.entry() {
            drop(dependencies);
            let summary = summaries
                .into_iter()
                .find(|summary| summary.module == producer)
                .unwrap();
            return (summary, resolved);
        }
        summaries.push(
            crate::elaborate::check_module(resolved)
                .unwrap()
                .into_exports(),
        );
    }
    panic!("ordinary constructor consumer missing");
}

fn assert_ordinary_payload_only_leaf(summary: &ExportSummary) -> (NominalTypeId, NominalTypeId) {
    authenticate_default(summary).unwrap();
    let leaf = NominalTypeId::new(summary.module, 0);
    let donor = NominalTypeId::new(summary.module, 1);
    assert_ne!(leaf, donor);
    for (id, spelling) in [(leaf, "Leaf"), (donor, "Donor")] {
        let hidden = summary
            .hidden_nominals
            .get(&id)
            .expect("payload dependency kind metadata");
        assert_eq!(hidden.spelling, spelling);
        assert!(hidden.display_is_private);
        assert_eq!(hidden.access, ImportedTypeAccess::Hidden);
        assert_eq!(hidden.constructor_count, 1);
        assert_eq!(hidden.parameter_count, 0);
        assert!(hidden.parameters.is_empty());
        assert!(hidden.constructors.is_empty());
        assert!(summary.hidden_nominal_order.contains(&id));
        assert!(!summary.nominal_names_by_id.contains_key(&id));
        assert!(!summary.nominals.values().any(|fact| fact.id == id));
        assert!(
            !summary
                .constructors
                .values()
                .any(|fact| fact.id.owner() == id)
        );
        assert!(
            !summary
                .hidden_constructors
                .keys()
                .any(|constructor| constructor.owner() == id)
        );
        assert!(!summary.canonical_representations.contains_key(&id));
    }
    for (name, payload) in [("Envelope", leaf), ("Witness", donor)] {
        let nominal = &summary.nominals[name];
        assert_eq!(nominal.access, ExportedTypeAccess::Transparent);
        assert_eq!(nominal.constructors.len(), 1);
        let constructor = &summary.constructors[name];
        assert_eq!(constructor.id.owner(), nominal.id);
        assert_eq!(nominal.constructors[0], constructor.id);
        assert_eq!(constructor.payload.as_ref(), Some(&Type::Nominal(payload)));
        assert!(constructor.scheme.type_parameters.is_empty());
        assert!(constructor.scheme.requirements.is_empty());
        assert!(matches!(&constructor.scheme.value_type,
            Type::Function(domain, result)
            if domain.as_ref() == &Type::Nominal(payload)
                && result.as_ref() == &Type::Nominal(nominal.id)));
        assert!(!summary.hidden_constructors.contains_key(&constructor.id));
    }
    assert_eq!(summary.terms.len(), 2);
    assert!(summary.terms.contains_key("make") && summary.terms.contains_key("inspect"));
    let mut work = TypeWorkBudget::default();
    for global in summary.terms.values() {
        let mut outward = HashSet::new();
        collect_nominal_identities(&global.scheme.value_type, &mut outward, &mut work).unwrap();
        assert!(
            !outward.contains(&leaf),
            "global outward type must not rescue Leaf"
        );
        assert!(global.scheme.requirements.is_empty());
        let mut captured = HashSet::new();
        for ty in global.capture.types(&mut work).unwrap() {
            collect_capture_external_nominals(ty, &mut captured, &mut work).unwrap();
        }
        assert!(
            !captured.contains(&leaf),
            "fixture must reach Leaf through constructor metadata, not capture.types"
        );
    }
    assert!(summary.implementations.is_empty());
    (leaf, donor)
}

#[test]
fn checked_constructor_closure_original_rejects_missing_donor_stale_and_wrong_owner_kind() {
    let mut projection = constructor_authority_fixture().0;
    let (leaf, donor) = assert_ordinary_payload_only_leaf(&projection);
    let constructor = &projection.constructors["Envelope"];
    let parameters = &projection.nominals["Envelope"].parameters;
    let original = constructor.original.as_ref().unwrap();
    for kind in [
        ResolvedNominalDeclarationKind::Data,
        ResolvedNominalDeclarationKind::Newtype,
    ] {
        assert_eq!(
            original.authenticate(
                constructor.id,
                kind,
                &constructor.spelling,
                constructor.payload.as_ref(),
                &constructor.origin,
                parameters,
                &mut TypeWorkBudget::default(),
                &mut crate::interface::InterfaceConstraintBudget::default()
            ),
            if kind == ResolvedNominalDeclarationKind::Data {
                Ok(())
            } else {
                Err(ResolvedBuildFailure::InvalidState)
            }
        );
    }
    let stale = original.stale_payload_for_test(constructor.id, Type::Nominal(donor));
    projection
        .constructors
        .get_mut("Envelope")
        .unwrap()
        .original = Some(stale);
    assert_eq!(
        authenticate_default(&projection),
        Err(ResolvedBuildFailure::InvalidState)
    );
    projection
        .constructors
        .get_mut("Envelope")
        .unwrap()
        .original = constructor_authority_fixture()
        .0
        .constructors
        .get_mut("Envelope")
        .unwrap()
        .original
        .take();
    assert_eq!(
        authenticate_default(&projection),
        Err(ResolvedBuildFailure::InvalidState)
    );
    projection
        .constructors
        .get_mut("Envelope")
        .unwrap()
        .original = None;
    assert_eq!(
        authenticate_default(&projection),
        Err(ResolvedBuildFailure::InvalidState)
    );
    assert!(
        projection.hidden_nominals.contains_key(&leaf)
            && projection.hidden_nominals.contains_key(&donor)
    );
}

#[test]
fn checked_constructor_closure_resolved_import_keeps_original_and_payload_correspondence() {
    crate::elaborate::check_module(constructor_authority_fixture().1).unwrap();
}
