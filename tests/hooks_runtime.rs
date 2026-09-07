use ash::{
    core::validate_effect_modules,
    driver::{RunConfiguration, run_path},
    elaborate::{EffectElaborator, check_module, link_modules},
    eval::evaluate_effect,
    evidence_validation::validate_interface_evidence,
    module::{ModuleRoots, load_module_graph},
    resolve::resolve_module,
    source::SourceFile,
};

#[test]
fn empty_root_preserves_publication_and_unused_body() {
    let mut failures = Vec::new();
    for (name, body, expected) in [
        ("publish", "perform Adjust.publish 3", "3 : Int\n"),
        ("unused", "42", "42 : Int\n"),
    ] {
        let path = std::env::temp_dir().join(format!(
            "ash-hook-{name}-{}-{}.ash",
            std::process::id(),
            SourceFile::new(name, "").unwrap().id().value()
        ));
        std::fs::write(&path, format!(
            "effect Adjust {{\npublish : Int -> Int\n}}\nmain : Unit -> Int\nmain () = hook Adjust {{\n{body}\n}}\n"
        )).unwrap();
        let result = run_path(RunConfiguration {
            entry: path.clone(),
            roots: ModuleRoots::empty(),
        });
        let _ = std::fs::remove_file(path);
        match result {
            Ok(result) => assert_eq!(format!("{} : Int\n", result.value()), expected),
            Err(error) => failures.push(format!("{name}: {error:?}")),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn nested_root_pipeline_and_disposal_fit_a_small_stack() {
    const CHILD: &str = "ASH_HOOK_RUNTIME_STACK_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let status = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "nested_root_pipeline_and_disposal_fit_a_small_stack",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .status()
            .unwrap();
        assert!(status.success(), "fresh hook runtime process: {status}");
        return;
    }
    std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
        let path = std::env::temp_dir().join(format!("ash-hook-stack-{}.ash", std::process::id()));
        let source = format!("effect Adjust {{\npublish : Int -> Int\n}}\nmain : Unit -> Int\nmain () = {}perform Adjust.publish 42{}\n", "hook Adjust {\n".repeat(24), "\n}".repeat(24));
        std::fs::write(&path, source).unwrap();
        let graph = load_module_graph(&path, &ModuleRoots::empty()).unwrap();
        std::fs::remove_file(path).unwrap();
        let module = &graph.modules()[0];
        let checked = check_module(resolve_module(module, &[]).unwrap()).unwrap();
        let linked = validate_interface_evidence(link_modules(vec![checked], graph.entry()).unwrap()).unwrap();
        let mut elaborator = EffectElaborator::for_module_program(&linked).unwrap();
        let typed = elaborator.synthesize_effect_module_program(&linked).unwrap();
        let core = elaborator.finish(typed.node).unwrap();
        let program = validate_effect_modules(core, &[module.source()], &[(module.id(), module.source().id())]).unwrap();
        assert_eq!(evaluate_effect(&program).unwrap().value.to_string(), "42");
    }).unwrap().join().unwrap();
}
