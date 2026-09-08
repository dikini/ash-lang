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

fn run_hook_source(source: &str) -> String {
    let path = std::env::temp_dir().join(format!(
        "ash-hook-execution-{}-{}.ash",
        std::process::id(),
        SourceFile::new("hook execution", "").unwrap().id().value()
    ));
    std::fs::write(&path, source).unwrap();
    let result = run_path(RunConfiguration {
        entry: path.clone(),
        roots: ModuleRoots::empty(),
    });
    std::fs::remove_file(path).unwrap();
    result.unwrap().value().to_string()
}

#[test]
fn registrations_transform_in_registration_order() {
    let source = "effect Adjust {\n    publish : Int -> Int\n}\n\nincrement : Int -> Int\nincrement value = value + 1\n\ndouble : Int -> Int\ndouble value = value * 2\n\nmain : Unit -> Int\nmain () = hook Adjust {\n    register Adjust increment {\n        register Adjust double {\n            perform Adjust.publish 3\n        }\n    }\n}\n";
    assert_eq!(run_hook_source(source), "8");
    let reversed = source
        .replace("register Adjust increment", "register Adjust temporary")
        .replace("register Adjust double", "register Adjust increment")
        .replace("register Adjust temporary", "register Adjust double");
    assert_eq!(run_hook_source(&reversed), "7");
}

#[test]
fn initializer_runs_once_before_activation_and_repeated_entries_remain_distinct() {
    assert_eq!(
        run_hook_source(
            "import @builtin.cell as Cell\neffect Adjust {\npublish : Int -> Int\n}\nmain : Unit -> Int\nmain () = resource cell<R> count = 0 {\nhook Adjust {\nlet callback : Int -> Int ! {Cell.Ops<R>} = fn(value) {\nlet n = Cell.read count\nlet _ = Cell.write (count, n + 1)\nvalue + 1\n}\nlet factory : Unit -> (Int -> Int ! {Cell.Ops<R>}) ! {Cell.Ops<R>, Adjust} = fn(ignored) {\nlet _ = Cell.write (count, perform Adjust.publish 10)\ncallback\n}\nlet result = register Adjust (factory ()) {\nregister Adjust callback {\nlet first = perform Adjust.publish 3\nfirst * 10 + perform Adjust.publish 4\n}\n}\nresult * 100 + Cell.read count\n}\n}\n"
        ),
        "5614"
    );
}

#[test]
fn normal_inner_exit_removes_only_that_registration() {
    assert_eq!(
        run_hook_source(
            "effect Adjust {\npublish : Int -> Int\n}\nincrement : Int -> Int\nincrement value = value + 1\ndouble : Int -> Int\ndouble value = value * 2\nmain : Unit -> Int\nmain () = hook Adjust {\nlet inside = register Adjust increment {\nlet both = register Adjust double {\nperform Adjust.publish 3\n}\nboth * 10 + perform Adjust.publish 3\n}\ninside * 10 + perform Adjust.publish 3\n}\n"
        ),
        "843"
    );
}

#[test]
fn callback_observes_intermediate_payload_under_registration_site_handlers() {
    assert_eq!(
        run_hook_source(
            "effect Adjust {\npublish : Int -> Int\n}\neffect Log {\nlog : Int -> Int\n}\nfirst : Int -> Int ! {Log}\nfirst value = (perform Log.log value) + 1\nsecond : Int -> Int ! {Log}\nsecond value = (perform Log.log value) * 2\nmain : Unit -> Int\nmain () = handle (hook Adjust {\nregister Adjust first {\nregister Adjust second {\nhandle {\nlet _ = perform Log.log 0\nperform Adjust.publish 3\n} with Log {\nlog value => resume 1000\n}\n}\n}\n}) with Log {\nlog value => resume (value + 10)\n}\n"
        ),
        "48"
    );
}

#[test]
fn nested_publication_sees_older_prefix_and_does_not_replay_pending_callbacks() {
    assert_eq!(
        run_hook_source(
            "effect Adjust {\npublish : Int -> Int\n}\nfirst : Int -> Int\nfirst value = value + 1\nsecond : Int -> Int ! {Adjust}\nsecond value = perform Adjust.publish (value * 10)\nthird : Int -> Int\nthird value = value * 2\nmain : Unit -> Int\nmain () = hook Adjust {\nregister Adjust first {\nregister Adjust second {\nregister Adjust third {\nperform Adjust.publish 3\n}\n}\n}\n}\n"
        ),
        "82"
    );
}

#[test]
fn callback_temporary_registration_and_root_affect_only_nested_publications() {
    for (nested, expected) in [
        (
            "register Adjust temporary {\nperform Adjust.publish value\n}",
            "410",
        ),
        (
            "hook Adjust {\nregister Adjust temporary {\nperform Adjust.publish value\n}\n}",
            "310",
        ),
    ] {
        assert_eq!(
            run_hook_source(&format!(
                "effect Adjust {{\npublish : Int -> Int\n}}\nfirst : Int -> Int\nfirst value = value + 1\ntemporary : Int -> Int\ntemporary value = value * 10\nsecond : Int -> Int ! {{Adjust}}\nsecond value = {{\nlet nested = {nested}\nnested + perform Adjust.publish 0\n}}\nthird : Int -> Int\nthird value = value * 10\nmain : Unit -> Int\nmain () = hook Adjust {{\nregister Adjust first {{\nregister Adjust second {{\nregister Adjust third {{\nperform Adjust.publish 2\n}}\n}}\n}}\n}}\n"
            )),
            expected
        );
    }
}

#[test]
fn ordinary_exact_handler_can_intercept_publication() {
    assert_eq!(
        run_hook_source(
            "effect Adjust {\npublish : Int -> Int\n}\nincrement : Int -> Int\nincrement value = value + 1\nmain : Unit -> Int\nmain () = hook Adjust {\nregister Adjust increment {\nhandle (perform Adjust.publish 3) with Adjust {\npublish value => resume (value * 10)\n}\n}\n}\n"
        ),
        "30"
    );
}

#[test]
fn subscriber_local_discard_preserves_registration_and_pending_completion() {
    assert_eq!(
        run_hook_source(
            "effect Adjust {\npublish : Int -> Int\n}\neffect Skip {\nskip : Unit -> Unit\n}\ncallback : Int -> Int\ncallback value = handle {\nlet ignored = perform Skip.skip ()\nvalue\n} with Skip {\nskip ignored => {\nlet done = discard\nvalue + 1\n}\n}\nmain : Unit -> Int\nmain () = hook Adjust {\nregister Adjust callback {\nperform Adjust.publish 3\n}\n}\n"
        ),
        "4"
    );
}

#[test]
fn constructor_function_is_an_ordinary_transformer() {
    assert_eq!(
        run_hook_source(
            "type Tree =\nLeaf\n| Wrap(Tree)\neffect Grow {\npublish : Tree -> Tree\n}\nmain : Unit -> Int\nmain () = hook Grow {\nregister Grow Wrap {\nmatch (perform Grow.publish Leaf) {\nWrap(Leaf) => 42\n_ => 0\n}\n}\n}\n"
        ),
        "42"
    );
}

#[test]
fn repeated_source_site_activations_overlap_without_merging() {
    assert_eq!(
        run_hook_source(
            "effect Adjust {\npublish : Int -> Int\n}\nrecursive : Int -> Int ! {Adjust}\nrecursive depth = register Adjust (fn(value) {\nvalue + depth\n}) {\nmatch depth == 4 {\ntrue => perform Adjust.publish 3\nfalse => recursive (depth + 1)\n}\n}\nmain : Unit -> Int\nmain () = hook Adjust {\nrecursive 0\n}\n"
        ),
        "13"
    );
}

#[test]
fn outward_callback_request_restores_pending_owners_and_cells_once() {
    assert_eq!(
        run_hook_source(
            "import @builtin.cell as Cell\neffect Adjust {\npublish : Int -> Int\n}\neffect Pause {\nask : Int -> Int\n}\nmain : Unit -> Int\nmain () = handle (resource cell<R> count = 0 {\nhook Adjust {\nlet first : Int -> Int ! {Cell.Ops<R>, Pause} = fn(value) {\nlet n = Cell.read count\nlet _ = Cell.write (count, n + 1)\nperform Pause.ask (value + 1)\n}\nregister Adjust first {\nregister Adjust (fn(value) {\nvalue * 2\n}) {\nlet result = perform Adjust.publish 3\nresult * 10 + Cell.read count\n}\n}\n}\n}) with Pause {\nask value => resume (value + 10)\n}\n"
        ),
        "281"
    );
}

#[test]
fn ordinary_callback_copies_and_static_request_closures_survive_deregistration() {
    assert_eq!(
        run_hook_source(
            "effect Adjust {\npublish : Int -> Int\n}\nmain : Unit -> Int\nmain () = hook Adjust {\nlet callback : Int -> Int = fn(value) {\nvalue + 1\n}\nlet later = register Adjust callback {\nlet saved : Unit -> Int ! {Adjust} = fn(ignored) {\nperform Adjust.publish 3\n}\nsaved\n}\nregister Adjust (fn(value) {\nvalue * 2\n}) {\ncallback 3 * 10 + later ()\n}\n}\n"
        ),
        "46"
    );
}

#[test]
fn unused_effectful_callback_is_retained_without_invocation() {
    assert_eq!(
        run_hook_source(
            "import @builtin.cell as Cell\neffect Adjust {\npublish : Int -> Int\n}\nmain : Unit -> Int\nmain () = resource cell<R> count = 0 {\nhook Adjust {\nlet callback : Int -> Int ! {Cell.Ops<R>} = fn(value) {\nlet _ = Cell.write (count, 99)\nvalue\n}\nlet _ = register Adjust callback {\ntrue\n}\nCell.read count\n}\n}\n"
        ),
        "0"
    );
}

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
