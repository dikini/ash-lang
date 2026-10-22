//! Genuine checked initialized-owner and view prerequisites; no native execution.

use super::*;
use crate::{
    foreign::source_contract::{
        prepare_checked_foreign_library, CheckedNativeAssumption, PreparedAccessResult,
        PreparedAddressRepresentation, PreparedForeignExtent, PreparedOwnerArgument,
        PreparedOwnerCall,
    },
    resolve::{DependencyExports, ResolveModuleError, ResolveReason},
    resolved::ResolvedModule,
};

const SOURCE: &str = include_str!("../../tests/fixtures/checked-byte-windows/owner.ash");

fn fixture() -> ModuleGraph {
    graph_with_entry(SOURCE, None)
}

fn assert_prepared(graph: &ModuleGraph) {
    let loaded = graph.module(graph.entry()).unwrap();
    let prepared =
        prepare_checked_foreign_library(loaded.id(), &loaded.surface().foreign_libraries[0])
            .expect("genuine checked initialized State/view contracts prepare before binding");
    assert_eq!(prepared.owners().len(), 1);
    let owner = &prepared.owners()[0];
    assert_eq!(owner.name(), "State");
    assert_eq!(owner.representation(), PreparedAddressRepresentation::Bytes);
    assert_eq!(owner.owned_parameter(), 1);
    assert!(owner.retained_parameters().is_empty());
    let contract = prepared.checked_contract().unwrap();
    assert_eq!(contract.owners()[0].host_parameter(), 0);
    let allocate = &prepared.symbols()[0];
    let Some(PreparedOwnerCall::Acquire {
        application,
        initialized_bytes: Some(initialized),
        ..
    }) = allocate.owner_call()
    else {
        panic!("actual acquisition must retain initialized-byte evidence");
    };
    assert_eq!(application.owner(), 0);
    assert_eq!(
        application.arguments(),
        &[
            PreparedOwnerArgument::Type(0),
            PreparedOwnerArgument::Type(1)
        ]
    );
    assert_eq!(initialized.extent(), &[1]);
    assert_eq!(prepared.accesses().len(), 2);
    for (family, name, extent, preserving) in [
        (
            0,
            "ByteView",
            PreparedForeignExtent::Bytes,
            vec!["QueryBytes", "ByteLength"],
        ),
        (1, "NulView", PreparedForeignExtent::Nul, vec!["QueryNul"]),
    ] {
        let access = &prepared.accesses()[family];
        assert_eq!(access.name(), name);
        assert_eq!(access.window_parameter(), 0);
        assert_eq!(access.extent(), extent);
        assert_eq!(
            access
                .parameters()
                .iter()
                .map(|p| p.name())
                .collect::<Vec<_>>(),
            ["W", "H", "R"]
        );
        assert_eq!(access.owner().owner(), 0);
        assert_eq!(
            access.owner().arguments(),
            &[
                PreparedOwnerArgument::Type(1),
                PreparedOwnerArgument::Type(2)
            ]
        );
        assert_eq!(
            access
                .preserving_members()
                .iter()
                .map(|(member, _)| prepared
                    .symbols()
                    .iter()
                    .find(|s| s.member_index() == *member)
                    .unwrap()
                    .name())
                .collect::<Vec<_>>(),
            preserving
        );
    }
    let callee = contract
        .assumptions()
        .iter()
        .find(|a| a.name() == "Callee")
        .unwrap();
    for (index, symbol) in prepared.symbols().iter().enumerate() {
        let selected = &contract.symbols()[index];
        assert_eq!(selected.member_index(), symbol.member_index());
        assert_eq!(selected.host_parameter(), if index < 2 { 0 } else { 1 });
        assert_eq!(selected.assumption_members(), &[callee.member_index()]);
        assert!(selected
            .minimum_assumptions()
            .contains(&CheckedNativeAssumption::NativeOwnerLifetimeAndDisposition));
        if index >= 2 {
            assert_eq!(
                symbol
                    .parameters()
                    .iter()
                    .map(|p| p.name())
                    .collect::<Vec<_>>(),
                ["W", "H", "R"]
            );
        }
    }
    for (name, family) in [("QueryBytes", 0), ("QueryNul", 1)] {
        let symbol = prepared
            .symbols()
            .iter()
            .find(|s| s.name() == name)
            .unwrap();
        let Some(PreparedAccessResult::View {
            application, keys, ..
        }) = symbol.access_result()
        else {
            panic!("actual view result");
        };
        assert_eq!(application.family(), family);
        assert_eq!(
            application.arguments(),
            &[
                PreparedOwnerArgument::Type(0),
                PreparedOwnerArgument::Type(1),
                PreparedOwnerArgument::Type(2)
            ]
        );
        assert_eq!(keys, &[vec![1]]);
    }
    let length = prepared
        .symbols()
        .iter()
        .find(|s| s.name() == "ByteLength")
        .unwrap();
    let Some(PreparedAccessResult::Extent {
        application,
        view,
        keys,
        ..
    }) = length.access_result()
    else {
        panic!("actual extent result");
    };
    assert_eq!(application.family(), 0);
    assert_eq!(
        application.arguments(),
        &[
            PreparedOwnerArgument::Type(0),
            PreparedOwnerArgument::Type(1),
            PreparedOwnerArgument::Type(2)
        ]
    );
    assert_eq!(view, &[2]);
    assert_eq!(keys, &[vec![1]]);
}

// Check genuine dependency modules, then return the root at the precise resolved
// binding boundary. Connected source/summary/Core checks are a separate test set.
fn resolve_entry(
    graph: &ModuleGraph,
    checked_profile: bool,
) -> Result<ResolvedModule, ResolveModuleError> {
    let mut checked = Vec::<CheckedModule>::new();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                DependencyExports::new(
                    edge,
                    checked
                        .iter()
                        .find(|module| module.module() == edge.target())
                        .unwrap()
                        .exports(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let resolved = if checked_profile {
            crate::resolve::resolve_checked_foreign_module(loaded, &dependencies)
        } else {
            crate::resolve::resolve_module(loaded, &dependencies)
        }?;
        if loaded.id() == graph.entry() {
            return Ok(resolved);
        }
        checked.push(
            crate::elaborate::check_module(resolved)
                .expect("actual builtin dependency checks before byte/window binding"),
        );
    }
    unreachable!("loaded graph contains its entry")
}

#[test]
fn checked_byte_window_prepares_initialized_state_and_actual_view_extent_contracts() {
    assert_prepared(&fixture());
}

#[test]
fn checked_byte_window_checked_primitive_inventory_resolves() {
    let graph = fixture();
    assert_prepared(&graph);
    resolve_entry(&graph, true)
        .expect("prepared initialized State and real view/extent contracts must bind before checked primitive source admission");
}

#[test]
fn checked_byte_window_default_profile_refuses() {
    let graph = fixture();
    assert_prepared(&graph);
    match resolve_entry(&graph, false) {
        Err(ResolveModuleError::Resolution(error)) => {
            assert_eq!(error.reason, ResolveReason::ForeignContract)
        }
        other => panic!("default profile must refuse checked initialized State: {other:?}"),
    }
}

// Resolve names using existing builtin spellings ONLY to reach checked owner
// binding. This root is never source-checked: legacy byte/copy functions grant
// no checked State/view permission and cannot stand in for the new identities.
#[test]
fn checked_byte_window_initialized_owner_binding_after_name_isolation() {
    let source = SOURCE
        .replace("Foreign.checked_byte_read", "Foreign.byte_read")
        .replace("Foreign.checked_byte_write", "Foreign.byte_write")
        .replace("Foreign.checked_copy_bytes", "Foreign.copy_bytes")
        .replace("Foreign.checked_copy_nul", "Foreign.copy_nul");
    let graph = graph_with_entry(&source, None);
    assert_prepared(&graph);
    resolve_entry(&graph, true)
        .expect("genuine prepared checked initialized owner/view contracts must bind independently of missing new builtin names");
}

#[test]
fn checked_byte_window_all_four_primitives_check_actual_source_and_summary() {
    let graph = fixture();
    assert_prepared(&graph);
    let checked = check_graph(&graph)
        .expect("all four checked primitives need genuine initialized State and actual lexical view/extent window source admission");
    let producer = checked
        .iter()
        .find(|module| module.module() == graph.entry())
        .unwrap();
    assert!(producer.source_resource_code().is_some());
    let registry = producer.registry();
    for name in ["Allocate", "Free", "QueryBytes", "ByteLength", "QueryNul"] {
        let effect = registry
            .effects()
            .iter()
            .find(|effect| effect.spelling == name)
            .unwrap();
        let original = registry
            .native_symbol(crate::types::OperationId::new(effect.id, 0))
            .unwrap();
        assert!(original.prepared().checked_contract().is_some());
        assert!(original.owner().is_some());
    }
}

const BYTE_CONSUMER: &str = "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<(Foreign.CheckedCall<Int>, Foreign.CheckedCall<Unit>, Producer.CopyProbe, Producer.CopyProbe), Unit, Unit>\nmain () = Producer.run ()\n";

fn assert_connected_byte_core(graph: &ModuleGraph) {
    use crate::core::{
        effect::{EffectExprKind, EffectOperation},
        packed::Intrinsic,
    };
    let checked = check_graph(graph).expect("actual byte/window body-free consumer checks");
    let producer = checked
        .iter()
        .find(|m| m.source_resource_code().is_some())
        .unwrap();
    let code = Arc::clone(producer.source_resource_code().unwrap());
    let header = Arc::clone(code.headers().next().unwrap());
    assert_eq!(header.original.host.unwrap().position, 0);
    assert_eq!(header.original.owned_position, 1);
    assert_eq!(header.original.parameters.len(), 2);
    assert!(producer
        .exports()
        .source_resource_facts()
        .any(|fact| Arc::ptr_eq(fact, &header.original)));
    let originals = ["Allocate", "Free", "QueryBytes", "ByteLength", "QueryNul"].map(|name| {
        let effect = producer
            .registry()
            .effects()
            .iter()
            .find(|e| e.spelling == name)
            .unwrap();
        Arc::clone(
            producer
                .registry()
                .native_symbol(crate::types::OperationId::new(effect.id, 0))
                .unwrap(),
        )
    });
    for original in &originals {
        assert!(Arc::ptr_eq(
            code.resource(0)
                .unwrap()
                .original_registry()
                .native_symbol(original.operation())
                .unwrap(),
            original
        ));
        assert!(Arc::ptr_eq(original.owner().unwrap(), &header.owner));
        let contract = original.prepared().checked_contract().unwrap();
        let selected = &contract.symbols()[original.symbol_index()];
        assert_eq!(
            selected.host_parameter(),
            if original.symbol().name() == "Allocate" || original.symbol().name() == "Free" {
                0
            } else {
                1
            }
        );
        let callee = contract
            .assumptions()
            .iter()
            .find(|a| a.name() == "Callee")
            .unwrap();
        assert_eq!(
            callee.description(),
            "the admitted native owner, initialized interval and view contracts hold"
        );
        assert!(selected
            .assumption_members()
            .contains(&callee.member_index()));
    }
    let accesses = producer
        .registry()
        .source_accesses()
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(accesses.len(), 2);
    let linked = link_modules(checked, graph.entry()).expect("real byte/window closure links");
    for original in &originals {
        assert!(Arc::ptr_eq(
            linked
                .registry()
                .native_symbol(original.operation())
                .unwrap(),
            original
        ));
    }
    for access in &accesses {
        assert!(Arc::ptr_eq(
            linked
                .registry()
                .source_accesses()
                .find(|actual| actual.nominal() == access.nominal())
                .unwrap(),
            access
        ));
    }
    assert!(Arc::ptr_eq(
        linked
            .registry()
            .source_resource_fact(header.original.id)
            .unwrap(),
        &header.original
    ));
    let linked = crate::evidence_validation::validate_interface_evidence(linked).unwrap();
    let mut elaborator = EffectElaborator::for_module_program(&linked).unwrap();
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("real byte/window closure lowers with default funding");
    let program = elaborator.finish(typed.node).unwrap();
    let sources = graph
        .modules()
        .iter()
        .map(|m| m.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|m| (m.id(), m.source().id()))
        .collect::<Vec<_>>();
    let core = crate::core::validate_effect_modules(program, &sources, &modules)
        .expect("independent default byte/window Core");
    let image_provenance = graph.modules().iter()
        .map(|m| (m.id(), Arc::new(m.source().clone())))
        .collect::<Vec<_>>();
    crate::build::checked_window_static_image_controls(&core, &image_provenance);
    // Insert after canonical `let core = validate_effect_modules(...).expect(...)`
    // in assert_connected_byte_core. Parent core/source_resource declaration:
    // #[cfg(test)] pub(crate) mod checked_byte_window_core_tests;
    use crate::core::source_resource::checked_byte_window_core_tests::{self as hostile, Mutation};
    for mutation in [
        Mutation::RequestHostActual,
        Mutation::RequestHostRow,
        Mutation::NativeOrder,
    ] {
        let mut changed = crate::core::transform::identity_effect_traversal(&core).unwrap();
        hostile::mutate(&mut changed, mutation);
        let error = crate::core::validate_effect_modules(changed, &sources, &modules)
            .expect_err("actual copied byte-window authority mutation must fail independent Core");
        assert_ne!(
            error.reason(),
            crate::core::ValidationReason::Resource,
            "no budget failure credit for {mutation:?}"
        );
    }
    let mut calls = Vec::new();
    let mut intrinsics = Vec::new();
    for node in core.nodes() {
        match &node.kind {
            EffectExprKind::Operation(EffectOperation::SourceResourceScope(scope)) => {
                scope
                    .visit_byte_calls(
                        |call, _| {
                            calls.push(call.function.local());
                            Ok(())
                        },
                        &mut TypeWorkBudget::default(),
                    )
                    .unwrap();
            }
            EffectExprKind::Pure(crate::core::dialect::PureExprKind::Value(
                crate::core::dialect::PureValue::Intrinsic(node),
            )) => match node.operation() {
                Intrinsic::ForeignByteRead { function }
                | Intrinsic::ForeignByteWrite { function }
                | Intrinsic::ForeignCopyBytes { function }
                | Intrinsic::ForeignCopyNul { function } => intrinsics.push(function.local()),
                _ => {}
            },
            _ => {}
        }
    }
    for local in 11..=14 {
        assert!(calls.contains(&local), "actual flow-proved call {local}");
        assert!(
            intrinsics.contains(&local),
            "actual canonical intrinsic {local}"
        );
    }
    for transformed in [
        crate::core::transform::identity_effect_traversal(&core).unwrap(),
        crate::core::transform::fold_effect_literal_primitives(&core).unwrap(),
    ] {
        crate::core::validate_effect_modules(transformed, &sources, &modules)
            .expect("byte/window identity and fold independently validate");
    }
}

#[test]
fn checked_byte_window_body_free_consumer_core_and_transforms() {
    assert_connected_byte_core(&graph_with_entry(SOURCE, Some(BYTE_CONSUMER)));
}

#[test]
fn checked_byte_window_body_free_facade_core_and_transforms() {
    static IDS: AtomicU64 = AtomicU64::new(0);
    struct Owned(std::path::PathBuf);
    impl Drop for Owned {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let directory = loop {
        let p = std::env::temp_dir().join(format!(
            "ash-byte-window-facade-{}-{}",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        match std::fs::create_dir(&p) {
            Ok(()) => break Owned(p),
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(e) => panic!("owned facade directory: {e}"),
        }
    };
    std::fs::write(directory.0.join("producer.ash"), SOURCE).unwrap();
    std::fs::write(
        directory.0.join("facade.ash"),
        "pub import producer (run as wrapped, CopyProbe)\n",
    )
    .unwrap();
    std::fs::write(
        directory.0.join("entry.ash"),
        BYTE_CONSUMER
            .replace("import producer as Producer", "import facade as Producer")
            .replace("Producer.run", "Producer.wrapped"),
    )
    .unwrap();
    let graph =
        crate::module::load_module_graph(&directory.0.join("entry.ash"), &ModuleRoots::empty())
            .unwrap();
    assert_connected_byte_core(&graph);
}

#[test]
fn checked_byte_window_selective_nonanchor_preflights_preserve_import_and_reexport() {
    for name in ["checked_size_t", "byte_read", "checked_copy_nul"] {
        let direct = format!(
            "import @builtin.foreign ({name} as selected)\nmain : Unit -> Int\nmain () = 42\n"
        );
        check_graph(&graph_with_entry(&direct, None))
            .expect("a genuine selected non-anchor preflight remains independently checkable");
        let facade = format!("pub import @builtin.foreign ({name} as selected)\n");
        let entry = "import producer (selected as forwarded)\nmain : Unit -> Int\nmain () = 42\n";
        check_graph(&graph_with_entry(&facade, Some(entry)))
            .expect("a body-free selected non-anchor reexport keeps exact checking facts without adding other global names");
    }
}

#[test]
fn checked_byte_window_selective_facade_does_not_publish_dependency_names() {
    let facade = "pub import @builtin.foreign (checked_copy_nul as selected)\n";
    let entry = "import producer (selected as forwarded)\nmain : Unit -> Int\nmain () = 42\n";
    check_graph(&graph_with_entry(facade, Some(entry))).unwrap();
    for name in ["Call", "Returned", "NativeHost", "checked_byte_read"] {
        let entry =
            format!("import producer ({name} as hidden)\nmain : Unit -> Int\nmain () = 42\n");
        let error = resolve_entry(&graph_with_entry(facade, Some(&entry)), true)
            .expect_err("checking-only dependencies must not create facade names");
        assert!(
            matches!(error, ResolveModuleError::Resolution(ref diagnostic) if diagnostic.reason == ResolveReason::UnavailableExport),
            "{error:?}"
        );
    }
}

// Append inside elaborate::checked_owner_lifecycle_tests::checked_byte_window_tests.
// STAGED, UNBUILT, UNEXECUTED. Canonical gate includes real source/summary checks.
fn byte_window_replace_once(source: &str, from: &str, to: &str) -> String {
    assert_eq!(
        source.matches(from).count(),
        1,
        "exact source mutation anchor"
    );
    source.replacen(from, to, 1)
}

fn byte_window_source_refuses(source: &str) {
    check_graph(&fixture()).expect("genuine unchanged byte/window source first");
    let error = check_graph(&graph_with_entry(source, None))
        .expect_err("hostile connected byte/window source must refuse");
    assert!(
        matches!(error, TypeError::Source(_)),
        "semantic source refusal required, not setup/contract/internal/resource: {error:?}"
    );
}

#[test]
fn checked_byte_window_legacy_primitives_do_not_authorize_checked_state_or_views() {
    for (checked, legacy) in [
        ("Foreign.checked_byte_read", "Foreign.byte_read"),
        ("Foreign.checked_byte_write", "Foreign.byte_write"),
        ("Foreign.checked_copy_bytes", "Foreign.copy_bytes"),
        ("Foreign.checked_copy_nul", "Foreign.copy_nul"),
    ] {
        byte_window_source_refuses(&byte_window_replace_once(SOURCE, checked, legacy));
    }
}

#[test]
fn checked_byte_window_extent_query_requires_the_original_view_key() {
    let source = byte_window_replace_once(
        SOURCE,
        "perform QueryBytes<W, H, R>.call (state, key)",
        "perform QueryBytes<W, H, R>.call (state, 0)",
    );
    let source = byte_window_replace_once(
        &source,
        "perform ByteLength<W, H, R>.call (state, key, view)",
        "perform ByteLength<W, H, R>.call (state, 0, view)",
    );
    check_graph(&graph_with_entry(&source, None))
        .expect("same known producing/query key is valid first");
    byte_window_source_refuses(&byte_window_replace_once(
        &source,
        "perform ByteLength<W, H, R>.call (state, 0, view)",
        "perform ByteLength<W, H, R>.call (state, 1, view)",
    ));
}

#[test]
fn checked_byte_window_cannot_suspend_for_an_ordinary_trace_request() {
    byte_window_source_refuses(&byte_window_replace_once(
        SOURCE,
        "let copied = copy_window ByteView<W, H, R> from state {",
        "let copied = copy_window ByteView<W, H, R> from state {\n                let ignored = perform Trace.note ()",
    ));
}

#[test]
fn checked_byte_window_current_read_after_finish_attempt_has_no_permission() {
    byte_window_source_refuses(&byte_window_replace_once(
        SOURCE,
        "let outcome = perform Free<H, R>.call state",
        "let outcome = perform Free<H, R>.call state\n        let action : (State<H, R>, Int) -> Foreign.CheckedCall<Int> ! {Foreign.NativeHost<H>} = Foreign.checked_byte_read\n        let ignored = action (state, 0)",
    ));
}

#[test]
fn checked_byte_window_boundary_failure_does_not_restore_current_permission() {
    // Only this actual finish BoundaryFailed branch changes. The original reason
    // remains forwarded after the attempted Current read; no constructor forgery.
    byte_window_source_refuses(&byte_window_replace_once(
        SOURCE,
        "Foreign.BoundaryFailed(reason) => Foreign.FinishedBoundary reason",
        "Foreign.BoundaryFailed(reason) => {\n                let action : (State<H, R>, Int) -> Foreign.CheckedCall<Int> ! {Foreign.NativeHost<H>} = Foreign.checked_byte_read\n                let ignored = action (state, 0)\n                Foreign.FinishedBoundary reason\n            }",
    ));
}

// Append alongside source-tests.fragment.rs. STAGED/UNBUILT/UNEXECUTED.
// One window, two actual same-family view queries with distinct key expressions.
// The donor's own extent/view pair MUST check before swapping only its view.
#[test]
fn checked_byte_window_same_family_donor_extent_cannot_authorize_another_view() {
    check_graph(&fixture()).expect("unchanged source first");
    // The actual inner ByteLength request is replaced by a second genuine view
    // query. Its completed result still lives inside the same copy_window.
    let anchor = "Foreign.CheckedReturned(Foreign.Readable(Foreign.NonNull(view))) => match perform ByteLength<W, H, R>.call (state, key, view) {";
    let donor = "Foreign.CheckedReturned(Foreign.Readable(Foreign.NonNull(view))) => match perform QueryBytes<W, H, R>.call (state, 1) {\n                    Foreign.CheckedReturned(Foreign.Readable(Foreign.NonNull(donor_view))) => match perform ByteLength<W, H, R>.call (state, 1, donor_view) {";
    let source = byte_window_replace_once(SOURCE, anchor, donor);
    let tail = "Foreign.BoundaryFailed(reason) => Copied (Foreign.BoundaryFailed reason)\n                    }\n                    Foreign.CheckedReturned(_) => NoView";
    let donor_tail = "Foreign.BoundaryFailed(reason) => Copied (Foreign.BoundaryFailed reason)\n                    }\n                    Foreign.CheckedReturned(_) => NoView\n                    Foreign.CheckedConversionFailed(error) => Copied (Foreign.CheckedConversionFailed error)\n                    Foreign.BoundaryFailed(reason) => Copied (Foreign.BoundaryFailed reason)\n                    }\n                    Foreign.CheckedReturned(_) => NoView";
    let source = byte_window_replace_once(&source, tail, donor_tail);
    let valid = byte_window_replace_once(
        &source,
        "Copied (action (view, extent))",
        "Copied (action (donor_view, extent))",
    );
    check_graph(&graph_with_entry(&valid, None))
        .expect("real same-family donor view paired with its own completed extent checks");
    let hostile = byte_window_replace_once(
        &valid,
        "Copied (action (donor_view, extent))",
        "Copied (action (view, extent))",
    );
    byte_window_source_refuses(&hostile);
}
