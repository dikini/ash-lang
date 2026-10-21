use ash::{
    lexer::lex,
    parser::{parse, project_module},
    source::SourceFile,
};

#[test]
fn checked_foreign_host_syntax_preserves_nested_lexical_boundaries() {
    let source = SourceFile::new(
        "checked-foreign-host.ash",
        "main : Unit -> Int\nmain () = foreign host Outer {\n    foreign host Inner {\n        42\n    }\n}\n",
    )
    .unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).unwrap();
    assert_eq!(module.definitions.len(), 1);
    let ash::surface::SurfaceDefinitionKind::Equational(main) = &module.definitions[0].kind else {
        panic!("main");
    };
    let ash::surface::SurfaceExprKind::ForeignHost(outer) = &main.equations[0].body.kind else {
        panic!("outer host");
    };
    assert_eq!(outer.identity.text, "Outer");
    let ash::surface::SurfaceExprKind::ForeignHost(inner) = &outer.body.result.kind else {
        panic!("inner host");
    };
    assert_eq!(inner.identity.text, "Inner");
    assert_ne!(outer.identity.span, inner.identity.span);
}

struct Fixture(std::path::PathBuf);
impl Fixture {
    fn new(text: &str) -> Self {
        static IDS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let id = IDS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("ash-checked-host-{}-{id}", std::process::id()));
        std::fs::create_dir(&path).unwrap();
        std::fs::write(path.join("entry.ash"), text).unwrap();
        Self(path)
    }
    fn graph(&self) -> ash::module::ModuleGraph {
        ash::module::load_module_graph(
            &self.0.join("entry.ash"),
            &ash::module::ModuleRoots::empty(),
        )
        .unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn checked_foreign_host_builtin_legacy_resolved_formals_do_not_shift() {
    use ash::resolved::ResolvedDefinitionKind;
    let fixture =
        Fixture::new("import @builtin.foreign as Foreign\nmain : Unit -> Int\nmain () = 42\n");
    let graph = fixture.graph();
    let builtin = graph
        .modules()
        .iter()
        .find(|module| module.source().display_path() == "@builtin.foreign")
        .unwrap();
    let resolved = ash::resolve::resolve_module(builtin, &[]).unwrap();
    for (index, expected) in [
        vec![],
        vec![],
        vec![5],
        vec![6],
        vec![],
        vec![7, 8],
        vec![9, 10],
        vec![11],
        vec![12],
        vec![13],
    ]
    .into_iter()
    .enumerate()
    {
        let ResolvedDefinitionKind::Equational(global) = &resolved.definitions()[index].kind else {
            panic!("legacy global");
        };
        let actual: Vec<_> = global
            .interface
            .type_parameters
            .iter()
            .map(|parameter| parameter.id.local())
            .collect();
        assert_eq!(actual, expected, "legacy global {index}");
    }
    assert_eq!(resolved.definitions().len(), 11);
    assert_eq!(resolved.effects()[0].parameters[0].id.local(), 22);
}

#[test]
fn checked_foreign_core_rejects_replayed_reserved_module_with_rewritten_bytes() {
    use ash::{
        core::{CoreBuilder, ValidationReason, validate_modules},
        source::{ByteRange, Origin},
        types::Type,
    };
    let fixture =
        Fixture::new("import @builtin.foreign as Foreign\nmain : Unit -> Int\nmain () = 42\n");
    let graph = fixture.graph();
    let builtin = graph
        .modules()
        .iter()
        .find(|module| module.source().display_path() == "@builtin.foreign")
        .unwrap();
    let canonical = builtin.source();
    let rewritten = SourceFile::new(
        "replayed-foreign.ash",
        canonical
            .text()
            .replacen("ConversionError", "ConversionWrong", 1),
    )
    .unwrap();
    assert_eq!(rewritten.text().len(), canonical.text().len());
    let check = |source: &SourceFile| {
        let mut builder = CoreBuilder::new();
        let origin = Origin::Source(source.span(ByteRange::new(0, 1).unwrap()).unwrap());
        let root = builder.unit(Type::Unit, origin).unwrap();
        validate_modules(
            builder.finish(root).unwrap(),
            &[source],
            &[(builtin.id(), source.id())],
        )
    };
    check(canonical).expect("canonical reserved source permits an otherwise valid literal");
    let error = check(&rewritten)
        .expect_err("replayed reserved identity cannot authenticate rewritten bytes");
    assert_eq!(error.reason(), ValidationReason::Registry);
}

const CHECKED_SCALAR: &str = r#"import @builtin.foreign as Foreign
foreign checked library C {
    profile "x86_64-unknown-linux-gnu"
    repr I32 = signed(32)
    symbol Abs<H> : Int -> Foreign.CheckedCall<Int> {
        name "abs"
        abi (I32) -> I32
        host H
        assumes { }
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
}
main : Unit -> Foreign.CheckedCall<Int>
main () = foreign host H {
    perform Abs<H>.call 1
}
"#;

fn check_static_graph(
    graph: &ash::module::ModuleGraph,
) -> Result<Vec<ash::resolved::CheckedModule>, String> {
    let mut checked: Vec<ash::resolved::CheckedModule> = Vec::new();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                ash::resolve::DependencyExports::new(
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
        let resolved = ash::resolve::resolve_checked_foreign_module(loaded, &dependencies)
            .map_err(|error| format!("resolution: {error:?}"))?;
        checked.push(
            ash::elaborate::check_module(resolved)
                .map_err(|error| format!("checking: {error:?}"))?,
        );
    }
    Ok(checked)
}

#[test]
fn checked_foreign_closed_scalar_host_checks_through_explicit_static_api() {
    let fixture = Fixture::new(CHECKED_SCALAR);
    let graph = fixture.graph();
    let checked =
        check_static_graph(&graph).expect("a closed checked scalar host must statically check");
    assert_eq!(checked.len(), graph.modules().len());
}

#[test]
fn checked_foreign_default_resolution_refuses_required_host_closure() {
    let fixture = Fixture::new(CHECKED_SCALAR);
    let graph = fixture.graph();
    let mut checked: Vec<ash::resolved::CheckedModule> = Vec::new();
    for loaded in graph.modules() {
        let dependencies = loaded
            .dependencies()
            .iter()
            .map(|edge| {
                ash::resolve::DependencyExports::new(
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
        match ash::resolve::resolve_module(loaded, &dependencies) {
            Ok(resolved) => checked.push(ash::elaborate::check_module(resolved).unwrap()),
            Err(_) => {
                assert_eq!(loaded.id(), graph.entry());
                return;
            }
        }
    }
    panic!("default resolution must not publish checked host permission");
}

fn checked_effect_core(graph: &ash::module::ModuleGraph) -> ash::core::ValidatedEffectProgram {
    let linked = ash::elaborate::link_modules(check_static_graph(graph).unwrap(), graph.entry())
        .expect("static module closure links");
    let linked = ash::evidence_validation::validate_interface_evidence(linked)
        .expect("checked closure evidence authenticates");
    let mut elaborator = ash::elaborate::EffectElaborator::for_module_program(&linked).unwrap();
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("checked host lowers through ordinary Effect Core");
    let unchecked = elaborator.finish(typed.node).unwrap();
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    ash::core::validate_effect_modules(unchecked, &sources, &modules)
        .expect("Core independently reconstructs checked host authority")
}

#[test]
fn checked_foreign_scalar_host_core_reconstructs_and_survives_transforms() {
    let fixture = Fixture::new(CHECKED_SCALAR);
    let graph = fixture.graph();
    let core = checked_effect_core(&graph);
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let modules = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    for transformed in [
        ash::core::transform::identity_effect_traversal(&core).unwrap(),
        ash::core::transform::fold_effect_literal_primitives(&core).unwrap(),
    ] {
        ash::core::validate_effect_modules(transformed, &sources, &modules)
            .expect("transformed checked host retains its binder and exact contract");
    }
    assert!(
        ash::eval::evaluate_effect(&core).is_err(),
        "static checked Core has no runtime launch permission"
    );
}

#[test]
fn checked_foreign_empty_host_core_is_static_and_refuses_runtime() {
    let fixture = Fixture::new(
        "import @builtin.foreign as Foreign\nmain : Unit -> Int\nmain () = foreign host H {\n    42\n}\n",
    );
    let graph = fixture.graph();
    let core = checked_effect_core(&graph);
    assert!(
        ash::eval::evaluate_effect(&core).is_err(),
        "even an empty native vector cannot turn static host metadata into launch permission"
    );
}

#[test]
fn checked_foreign_nested_hosts_select_only_their_exact_fresh_identity() {
    let text = CHECKED_SCALAR.replace("    perform Abs<H>.call 1\n}", "    let outer = perform Abs<H>.call 1\n    foreign host Inner {\n        perform Abs<Inner>.call 2\n    }\n}");
    let fixture = Fixture::new(&text);
    let graph = fixture.graph();
    let _ = checked_effect_core(&graph);
}

#[test]
fn checked_foreign_host_identity_cannot_escape_as_a_latent_call() {
    let text = CHECKED_SCALAR
        .replace(
            "main : Unit -> Foreign.CheckedCall<Int>",
            "main : Unit -> (Int -> Foreign.CheckedCall<Int>)",
        )
        .replace(
            "    perform Abs<H>.call 1\n}",
            "    let later : Int -> Foreign.CheckedCall<Int> ! {Abs<H>, Foreign.NativeHost<H>} = fn (value) {\n        perform Abs<H>.call value\n    }\n    later\n}",
        );
    let fixture = Fixture::new(&text);
    let error = check_static_graph(&fixture.graph())
        .expect_err("latent native and host rows cannot escape");
    assert!(error.contains("escapes"), "{error}");
}

#[test]
fn checked_foreign_host_identity_is_unavailable_outside_or_in_a_sibling_scope() {
    for body in [
        "    let first = foreign host Left {\n        perform Abs<Left>.call 1\n    }\n    perform Abs<Left>.call 2\n",
        "    let first = foreign host Left {\n        perform Abs<Left>.call 1\n    }\n    foreign host Right {\n        perform Abs<Left>.call 2\n    }\n",
    ] {
        let start = CHECKED_SCALAR.find("main () =").unwrap();
        let text = format!("{}main () = {{\n{body}}}\n", &CHECKED_SCALAR[..start]);
        let fixture = Fixture::new(&text);
        let error = check_static_graph(&fixture.graph())
            .expect_err("an earlier host cannot enter the sibling or outer type namespace");
        assert!(error.starts_with("resolution:"), "{error}");
    }
}

#[test]
fn checked_foreign_host_does_not_discharge_a_same_kind_unrelated_actual() {
    let fixture =
        Fixture::new(&CHECKED_SCALAR.replace("perform Abs<H>.call 1", "perform Abs<Int>.call 1"));
    let error =
        check_static_graph(&fixture.graph()).expect_err("Int is not the lexical host identity");
    assert!(error.starts_with("checking:"), "{error}");
}
