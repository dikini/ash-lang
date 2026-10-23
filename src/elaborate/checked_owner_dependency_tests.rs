//! Static declared owner-dependency correspondence; no evaluator/native entry.

use super::*;

const DEPENDENT: &str = include_str!("../../tests/fixtures/checked-owner-dependencies/owner.ash");
const CONSUMER: &str = "import @builtin.foreign as Foreign\nimport producer as Producer\nmain : Unit -> Foreign.CheckedScope<Foreign.CheckedScope<Int, Unit, Unit>, Unit, Unit>\nmain () = Producer.run ()\n";

#[test]
fn checked_owner_dependency_canonical_source_retains_exact_parent() {
    let canonical = check_graph(&graph(PRODUCER, false))
        .expect("existing dependency-free checked lifecycle is the positive setup");
    assert_producer_originals(&canonical);
    let graph = graph_with_entry(DEPENDENT, Some(CONSUMER));
    let checked = check_graph(&graph)
        .expect("declared checked child dependency must survive source and body-free checking");
    let producer = checked
        .iter()
        .find(|module| module.source_resource_code().is_some())
        .expect("actual dependent producer retains immutable original resource forests");
    let child = producer
        .source_resource_code()
        .unwrap()
        .headers()
        .find(|header| header.original.spelling == "Child")
        .expect("actual checked child header");
    assert_eq!(child.original.host.unwrap().position, 0);
    assert_eq!(child.original.owned_position, 2);
    assert_eq!(child.original.parameters[0].spelling, "H");
    assert_eq!(child.original.parameters[1].spelling, "C");
    assert_eq!(child.original.parameters[2].spelling, "S");
    assert_eq!(
        child.dependencies.as_ref(),
        &[child.original.parameters[1].id]
    );
    assert_ne!(child.dependencies[0], child.original.parameters[2].id);
    assert_eq!(child.owner.owner().retained_parameters(), &[1]);
    assert!(child.owner.prepared().checked_contract().is_some());
    assert!(
        producer
            .exports()
            .source_resource_facts()
            .any(|header| Arc::ptr_eq(header, &child.original))
    );
    validate_latest_payload_core(&graph);
    let parent = producer
        .source_resource_code()
        .unwrap()
        .headers()
        .find(|header| header.original.spelling == "Parent")
        .expect("actual independent parent header from the same checked source");
    crate::foreign::assert_dependent_header_refused_before_entry(parent, child);
}

fn linked_core(
    source: &str,
    entry: &str,
) -> (
    crate::core::ValidatedEffectProgram,
    Vec<(crate::module::ModuleId, Arc<crate::source::SourceFile>)>,
) {
    let graph = graph_with_entry(source, Some(entry));
    let checked = check_graph(&graph).expect("canonical dependency source and body-free summaries");
    let linked = link_modules(checked, graph.entry()).expect("canonical dependency closure links");
    let linked = crate::evidence_validation::validate_interface_evidence(linked).unwrap();
    let mut elaborator = EffectElaborator::for_module_program(&linked).unwrap();
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .unwrap();
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
        .expect("default independent dependency Core");
    for transformed in [
        crate::core::transform::identity_effect_traversal(&core).unwrap(),
        crate::core::transform::fold_effect_literal_primitives(&core).unwrap(),
    ] {
        crate::core::validate_effect_modules(transformed, &sources, &modules).unwrap();
    }
    let provenance = graph
        .modules()
        .iter()
        .map(|m| (m.id(), Arc::clone(m.retained_source())))
        .collect();
    (core, provenance)
}

fn source_refuses(source: &str) {
    let error = match check_graph(&graph_with_entry(source, Some(CONSUMER))) {
        Ok(_) => panic!("hostile dependency source must refuse after its canonical control"),
        Err(error) => error,
    };
    match error {
        TypeError::Source(diagnostic) => {
            println!("dependency source refusal: {:?}", diagnostic.reason);
            assert!(matches!(
                diagnostic.reason,
                TypeReason::Argument | TypeReason::ResourceEscape
            ));
        }
        TypeError::Mismatch(_) => println!("dependency source refusal: structural TypeMismatch"),
        _ => panic!("require semantic source refusal rather than setup/internal/work failure"),
    }
}

#[test]
fn checked_owner_dependency_wrong_host_identity_and_native_data_refuse() {
    linked_core(DEPENDENT, CONSUMER);
    for (before, after) in [
        (
            "resource Child<H, C, S> {\n    owned S\n    host H",
            "resource Child<H, C, S> {\n    owned S\n    host C",
        ),
        (
            "    state ChildState<H, C, S>",
            "    state ChildState<H, S, C>",
        ),
    ] {
        assert_eq!(DEPENDENT.matches(before).count(), 1);
        source_refuses(&DEPENDENT.replace(before, after));
    }
    let native_data = DEPENDENT
        .replace("    data (Parent<H, C>, Int)", "    data ParentState<H, C>")
        .replace("Acquire<ChildState<H, C, S>, (Parent<H, C>, Int), Unit>", "Acquire<ChildState<H, C, S>, ParentState<H, C>, Unit>")
        .replace("Acquired(state, (parent, label))", "Acquired(state, dependency)")
        .replace("finish (state, (parent, label)) => {\n        let dependency = perform ParentOps<Parent<H, C>, ParentState<H, C>>.borrow parent", "finish (state, dependency) => {")
        .replace("handlers (state, (parent, label)) {\n        read access => resume label", "handlers (state, dependency) {\n        read access => resume 4");
    assert_ne!(native_data, DEPENDENT);
    source_refuses(&native_data);
}

#[test]
fn checked_owner_dependency_missing_retains_refuses_original_binding() {
    linked_core(DEPENDENT, CONSUMER);
    assert_eq!(DEPENDENT.matches("        retains C\n").count(), 1);
    binding_refuses(&DEPENDENT.replace("        retains C\n", ""));
}

fn binding_refuses(source: &str) {
    use crate::resolve::{DependencyExports, ResolveModuleError, ResolveReason};
    let graph = graph_with_entry(source, None);
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
                        .find(|m| m.module() == edge.target())
                        .unwrap()
                        .exports(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let resolved = crate::resolve::resolve_checked_foreign_module(loaded, &dependencies);
        if loaded.id() == graph.entry() {
            match resolved {
                Err(ResolveModuleError::Resolution(error)) => {
                    assert_eq!(error.reason, ResolveReason::ForeignContract)
                }
                _ => panic!("missing original retained identity must fail foreign binding"),
            }
            return;
        }
        checked.push(crate::elaborate::check_module(resolved.unwrap()).unwrap());
    }
    panic!("actual graph contains producer entry");
}

fn row_source_from(input: &str) -> String {
    let mut source = input.to_owned();
    for (kind, name, args) in [
        ("owner", "ParentState", "H, C"),
        ("owner", "ChildState", "H, C, S"),
        ("symbol", "ParentAllocate", "H, C"),
        ("symbol", "ParentFree", "H, C"),
        ("symbol", "ChildAllocate", "H, C, S"),
        ("symbol", "ChildFree", "H, C, S"),
        ("resource", "Parent", "H, C"),
        ("resource", "Child", "H, C, S"),
        ("symbol", "ChildRead", "H, C, S"),
        ("access", "ChildView", "W, H, C, S"),
        ("symbol", "QueryChild", "W, H, C, S"),
        ("symbol", "ChildLength", "W, H, C, S"),
    ] {
        let prefix = if kind == "resource" { "\n" } else { "\n    " };
        let before = format!("{prefix}{kind} {name}<{args}>");
        if !source.contains(&before)
            && ["ChildRead", "ChildView", "QueryChild", "ChildLength"].contains(&name)
        {
            continue;
        }
        assert_eq!(source.matches(&before).count(), 1);
        source = source.replace(
            &before,
            &format!("{prefix}{kind} {name}<Before : EffectRow, {args}, After : EffectRow>"),
        );
    }
    for (name, args) in [
        ("ParentState", "H, C"),
        ("ChildState", "H, C, S"),
        ("ParentAllocate", "H, C"),
        ("ParentFree", "H, C"),
        ("ChildAllocate", "H, C, S"),
        ("ChildFree", "H, C, S"),
        ("Parent", "H, C"),
        ("Child", "H, C, S"),
        ("ChildRead", "H, C, S"),
        ("ChildView", "W, H, C, S"),
        ("QueryChild", "W, H, C, S"),
        ("ChildLength", "W, H, C, S"),
    ] {
        source = source.replace(
            &format!("{name}<{args}>"),
            &format!("{name}<{{| Before}}, {args}, {{| After}}>"),
        );
    }
    source = source
        .replace(
            "resource Parent<{| Before}, H, C, {| After}> parent",
            "resource Parent<{BeforeMark}, H, C, {AfterMark}> parent",
        )
        .replace(
            "resource Child<{| Before}, H, C, S, {| After}> child",
            "resource Child<{BeforeMark}, H, C, S, {AfterMark}> child",
        );
    source.replacen("\n\nforeign checked library", "\n\neffect BeforeMark {\n    before_mark : Unit -> Unit\n}\neffect AfterMark {\n    after_mark : Unit -> Unit\n}\n\nforeign checked library", 1)
}

#[test]
fn checked_owner_dependency_complete_rows_core_and_budget_controls() {
    let (core, provenance) = linked_core(&row_source_from(DEPENDENT), CONSUMER);
    crate::core::source_resource::checked_dependency_tests::assert_core_controls(
        &core,
        &provenance,
        false,
    );
}

#[test]
fn checked_owner_dependency_genuine_parent_donor_core_refuses() {
    let source = DEPENDENT.replace("Foreign.CheckedScope<Foreign.CheckedScope<Int, Unit, Unit>, Unit, Unit>",
        "Foreign.CheckedScope<Foreign.CheckedScope<Foreign.CheckedScope<Int, Unit, Unit>, Unit, Unit>, Unit, Unit>")
        .replace("        resource Child<H, C, S> child = (parent, 4) {\n            read child\n        }",
        "        resource Parent<H, Donor> donor = 32 {\n            resource Child<H, Donor, S> child = (donor, 4) {\n                read child\n            }\n        }");
    assert_ne!(source, DEPENDENT);
    let consumer = CONSUMER.replace("Foreign.CheckedScope<Foreign.CheckedScope<Int, Unit, Unit>, Unit, Unit>",
        "Foreign.CheckedScope<Foreign.CheckedScope<Foreign.CheckedScope<Int, Unit, Unit>, Unit, Unit>, Unit, Unit>");
    let (core, provenance) = linked_core(&source, &consumer);
    crate::core::source_resource::checked_dependency_tests::assert_core_controls(
        &core,
        &provenance,
        true,
    );
}

#[test]
fn checked_owner_dependency_private_static_image_roundtrip_and_bounds() {
    let (core, provenance) = linked_core(DEPENDENT, CONSUMER);
    crate::build::checked_owner_dependency_image_controls(&core, &provenance, crate::build::CheckedDependencyStandalone::Fits);
    let (row_core, row_provenance) = linked_core(&row_source_from(DEPENDENT), CONSUMER);
    crate::build::checked_owner_dependency_image_controls(&row_core, &row_provenance, crate::build::CheckedDependencyStandalone::Resource);
}

fn scalar_borrow_source() -> String {
    let declaration = r#"    symbol ChildRead<H, C, S> : ChildState<H, C, S> -> Foreign.CheckedCall<Int> {
        name "ash_child_read"
        abi (pointer(Address)) -> CInt
        host H
        assumes { Callee }
        operand 0 from 0 current
        output result as scalar
        outcome otherwise { readable result }
    }
"#;
    DEPENDENT.replacen("    repr Size = size_t", "    repr CInt = signed(32)\n    repr Size = size_t", 1)
        .replacen("}\n\npub type Acquire", &format!("{declaration}}}\n\npub type Acquire"), 1)
        .replace("read : Access -> Int", "read : Access -> Foreign.CheckedCall<Int>")
        .replace("interpret ChildAllocate<H, C, S>, ChildFree<H, C, S>", "interpret ChildAllocate<H, C, S>, ChildFree<H, C, S>, ChildRead<H, C, S>")
        .replace("read access => resume label", "read access => resume (perform ChildRead<H, C, S>.call state)")
        .replace("            read child", "            match read child {\n                Foreign.CheckedReturned(value) => value\n                Foreign.CheckedConversionFailed(_) => 0\n                Foreign.BoundaryFailed(_) => 0\n            }")
}

#[test]
fn checked_owner_dependency_retained_scalar_borrow_keeps_host_and_parent() {
    let source = scalar_borrow_source();
    linked_core(&source, CONSUMER);
    linked_core(&row_source_from(&source), CONSUMER);
    for actual in ["ChildRead<C, H, S>", "ChildRead<H, S, C>"] {
        let wrong = source.replace(
            "perform ChildRead<H, C, S>.call state",
            &format!("perform {actual}.call state"),
        );
        assert_ne!(source, wrong);
        source_refuses(&wrong);
    }
}

fn access_borrow_source() -> String {
    let bytes = include_str!("../../tests/fixtures/checked-byte-windows/owner.ash");
    let start = bytes.find("    access ByteView").unwrap();
    let end = bytes.find("    access NulView").unwrap();
    let contracts = bytes[start..end]
        .replace("State<H, R>", "ChildState<H, C, S>")
        .replace("<W, H, R>", "<W, H, C, S>")
        .replace("ByteView", "ChildView")
        .replace("QueryBytes", "QueryChild")
        .replace("ByteLength", "ChildLength")
        .replace("-> pointer(Address)", "-> pointer(ViewBytes)");
    let start = bytes.find("        copy_bytes (access, key) => {").unwrap();
    let end = bytes
        .find("        copy_nul (access, key, bound) => {")
        .unwrap();
    let handler = bytes[start..end]
        .replace(
            "copy_bytes (access, key) => {",
            "read access => {\n            let key = 0",
        )
        .replace("<W, H, R>", "<W, H, C, S>")
        .replace("ByteView", "ChildView")
        .replace("QueryBytes", "QueryChild")
        .replace("ByteLength", "ChildLength");
    DEPENDENT.replacen("    repr Address = opaque", "    repr Address = opaque\n    repr ViewBytes = bytes", 1)
        .replacen("}\n\npub type Acquire", &format!("{contracts}}}\n\npub type Acquire"), 1)
        .replace("    | Refused(I)", "    | Refused(I)\npub type CopyProbe = Copied(Foreign.CheckedCall<Bytes>)\n    | NoView")
        .replace("read : Access -> Int", "read : Access -> CopyProbe")
        .replace("        read access => resume label\n", &handler)
        .replace("            read child", "            let copied = read child\n            4")
}

#[test]
fn checked_owner_dependency_retained_access_borrow_requires_exact_window() {
    // The existing legacy view-result contract keeps the opaque owner pointer
    // distinct from the bytes pointer returned by its access operation.
    let legacy = crate::foreign::source_contract::access_contract::tests::view_source();
    let file = crate::source::SourceFile::new("legacy-opaque-view.ash", &legacy).unwrap();
    let tree = crate::parser::parse(crate::lexer::lex(&file).unwrap());
    assert!(tree.parse_diagnostics().is_empty());
    let surface = crate::parser::project_module(&file, &tree).unwrap();
    let prepared = crate::foreign::source_contract::prepare_foreign_library(
        crate::module::ModuleId::from(file.id()),
        &surface.foreign_libraries[0],
    )
    .unwrap();
    assert_eq!(
        prepared.owners()[0].representation(),
        crate::foreign::source_contract::PreparedAddressRepresentation::Opaque
    );
    assert!(
        prepared
            .symbols()
            .iter()
            .find(|s| s.name() == "Column")
            .unwrap()
            .access_result()
            .is_some()
    );
    let source = access_borrow_source();
    linked_core(&source, CONSUMER);
    let row_source = row_source_from(&source);
    let (row_core, row_provenance) = linked_core(&row_source, CONSUMER);
    let window = row_core
        .nodes()
        .iter()
        .find_map(|node| match &node.kind {
            crate::core::EffectExprKind::Operation(
                crate::core::EffectOperation::SourceCopyWindow(window),
            ) => Some(window),
            _ => None,
        })
        .expect("actual copied checked access window");
    assert_eq!(window.family().declaration().window_parameter(), 1);
    let access_span = window.family().declaration().origin().primary_span();
    let parameters = crate::foreign::source_owner::row_foreign_parameters(
        window.family().nominal(),
        row_core.registry(),
        access_span,
        &mut TypeWorkBudget::default(),
    )
    .unwrap();
    assert_eq!(parameters.len(), window.arguments().len());
    match crate::foreign::source_owner::row_owner_parameters(
        window.family().nominal(),
        row_core.registry(),
        access_span,
        &mut TypeWorkBudget::default(),
    ) {
        Err(error) => assert!(
            !error.is_resource_exhaustion(),
            "Access kind is not State authority"
        ),
        Ok(_) => panic!("an original Access must not acquire Owner role"),
    }

    assert_eq!(window.arguments().iter().filter(|argument| matches!(argument, crate::types::KindedArgument::RowArg(row) if !row.known().is_empty())).count(), 2);
    let view = crate::types::IterativeTypeOwner::new(crate::types::Type::ForeignOwnerApply(
        window.family().nominal(),
        crate::types::clone_kinded_arguments_with_budget(
            window.arguments().iter(),
            &mut TypeWorkBudget::default(),
        )
        .unwrap(),
    ));
    assert!(
        crate::core::source_window::matches_static_view_type(
            window.family(),
            window.arguments(),
            &view,
            &mut TypeWorkBudget::default()
        )
        .unwrap()
    );
    assert!(
        !crate::core::source_window::matches_view_type(
            window.family(),
            window.arguments(),
            &view,
            &mut TypeWorkBudget::default()
        )
        .unwrap(),
        "existing executable matcher remains Type-only"
    );
    crate::core::source_window::assert_erased_row_window_refuses(&row_core, &row_provenance);
    let row_request = "perform QueryChild<{| Before}, W, H, C, S, {| After}>";
    assert_eq!(row_source.matches(row_request).count(), 1);
    source_refuses(&row_source.replace(
        row_request,
        "perform QueryChild<{| After}, W, H, C, S, {| Before}>",
    ));
    crate::build::checked_owner_dependency_image_controls(&row_core, &row_provenance, crate::build::CheckedDependencyStandalone::Resource);
    for (before, after) in [
        (
            "copy_window ChildView<W, H, C, S>",
            "copy_window ChildView<W, C, H, S>",
        ),
        (
            "perform QueryChild<W, H, C, S>",
            "perform QueryChild<W, H, S, C>",
        ),
    ] {
        assert_eq!(source.matches(before).count(), 1);
        source_refuses(&source.replace(before, after));
    }
}

#[test]
fn checked_owner_dependency_child_finish_requires_actual_attempt() {
    linked_core(DEPENDENT, CONSUMER);
    assert_eq!(
        DEPENDENT
            .matches("match perform ChildFree<H, C, S>.call (state, dependency)")
            .count(),
        1
    );
    let source = DEPENDENT.replace("match perform ChildFree<H, C, S>.call (state, dependency)",
        "let outcome : Foreign.CheckedCall<Foreign.Disposition<Unit>> = Foreign.CheckedReturned (Foreign.Consumed ())\n        match outcome");
    source_refuses(&source);
}

#[test]
fn checked_owner_dependency_initialized_byte_child_remains_refused() {
    linked_core(DEPENDENT, CONSUMER);
    let source = DEPENDENT.replace("    repr Address = opaque", "    repr Address = opaque\n    repr ChildBytes = bytes")
        .replace("owner ChildState<H, C, S> {\n        representation Address", "owner ChildState<H, C, S> {\n        representation ChildBytes")
        .replace("abi (pointer(Address), Size) -> pointer(Address)", "abi (pointer(Address), Size) -> pointer(ChildBytes)")
        .replace("abi (pointer(Address), pointer(Address)) -> void", "abi (pointer(ChildBytes), pointer(Address)) -> void")
        .replace("output result as owner(ChildState<H, C, S>)\n        outcome result nonnull { readable result }", "output result as owner(ChildState<H, C, S>)\n        outcome result nonnull { readable result, initialized_bytes result from 1 }");
    let graph = graph_with_entry(&source, None);
    let producer = graph.module(graph.entry()).unwrap();
    let prepared = crate::foreign::source_contract::prepare_checked_foreign_library(
        producer.id(),
        &producer.surface().foreign_libraries[0],
    )
    .unwrap();
    assert_eq!(prepared.owners()[1].retained_parameters(), &[1]);
    assert_eq!(
        prepared.owners()[1].representation(),
        crate::foreign::source_contract::PreparedAddressRepresentation::Bytes
    );
    binding_refuses(&source);
}
