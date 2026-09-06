use ash::{
    core::{ValidatedEffectProgram, validate_effect_modules},
    elaborate::{EffectElaborator, check_module, link_modules},
    eval::EffectTraceEvent,
    eval::{Evaluation, evaluate_effect},
    evidence_validation::validate_interface_evidence,
    module::{ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
    source::SourceFile,
};

#[test]
fn same_site_metadata_only_closure_uses_its_lexical_activation() {
    let result = run(
        "import @builtin.cell as Cell\neffect E<T> {\nask : Unit -> Int\n}\neffect Pause {\nask : Unit -> Unit\n}\nvisit : Int -> Int ! {Pause}\nvisit depth = resource cell<R> c = depth {\nlet observe : Unit -> Int ! {E<R>} = fn(ignored) {\nperform E<R>.ask ()\n}\nhandle (match depth == 0 {\ntrue => {\nlet _ = perform Pause.ask ()\nobserve ()\n}\nfalse => {\nhandle (visit 0) with Pause {\nask ignored => {\nlet outer = observe ()\nlet inner = resume ()\nouter + inner\n}\n}\n}\n}) with E<R> {\nask ignored => resume (match depth == 0 {\ntrue => 1\nfalse => 41\n})\n}\n}\nmain : Unit -> Int\nmain () = handle (visit 1) with Pause {\nask ignored => resume ()\n}\n",
    );
    assert_eq!(result.value.to_string(), "42");
}

#[test]
fn copied_closure_runs_after_payload_release() {
    let result = run(
        "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = {\nlet escaped = resource cell<R> c = 41 {\nlet copied = Cell.read c\nlet later : Unit -> Int = fn(ignored) {\ncopied + 1\n}\nlater\n}\nescaped ()\n}\n",
    );
    assert_eq!(result.value.to_string(), "42");
}

#[test]
fn imported_accessor_factory_preserves_provider_and_outer_identity() {
    let helper = "import @builtin.cell as Cell\npub reader<R> : Cell.Handle<R> -> (Unit -> Int ! {Cell.Ops<R>}) where Cell.Provider<R>\nreader value = fn(ignored) {\nCell.read value\n}\npub relay<E : EffectRow, A> : ((Unit -> Int ! {| E}), A) -> Int ! {| E}\nrelay (action, ignored) = action ()\n";
    for body in [
        "get ()",
        "resource cell<S> other = 10 {\nlet _ = Cell.write (other, 99)\nget ()\n}",
    ] {
        let source = format!(
            "import @builtin.cell as Cell\nimport helper (reader)\nmain : Unit -> Int\nmain () = resource cell<R> c = 42 {{\nlet get = reader c\n{body}\n}}\n"
        );
        let program = program_with_modules(&source, &[("helper.ash", helper)]);
        assert_eq!(evaluate_effect(&program).unwrap().value.to_string(), "42");
    }
}

fn program(source: &str) -> ValidatedEffectProgram {
    program_with_modules(source, &[])
}

fn program_with_modules(source: &str, modules: &[(&str, &str)]) -> ValidatedEffectProgram {
    let directory = std::env::temp_dir().join(format!(
        "ash-resource-runtime-{}-{}",
        std::process::id(),
        SourceFile::new("resource runtime", "")
            .unwrap()
            .id()
            .value()
    ));
    std::fs::create_dir(&directory).unwrap();
    for (name, text) in modules {
        std::fs::write(directory.join(name), text).unwrap();
    }
    let path = directory.join("entry.ash");
    std::fs::write(&path, source).unwrap();
    let graph = load_module_graph(&path, &ModuleRoots::empty()).unwrap();
    let _ = std::fs::remove_dir_all(directory);
    let mut checked: Vec<CheckedModule> = Vec::new();
    for module in graph.modules() {
        let dependencies = module
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
        checked.push(check_module(resolve_module(module, &dependencies).unwrap()).unwrap());
    }
    let linked =
        validate_interface_evidence(link_modules(checked, graph.entry()).unwrap()).unwrap();
    let mut elaborator = EffectElaborator::for_module_program(&linked).unwrap();
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .unwrap();
    let core = elaborator.finish(typed.node).unwrap();
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let module_sources = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    validate_effect_modules(core, &sources, &module_sources).expect("resource Core should execute")
}

fn run(source: &str) -> Evaluation {
    evaluate_effect(&program(source)).expect("resource execution")
}

#[test]
fn nested_source_execution_and_release_fit_a_fresh_small_stack() {
    const CHILD: &str = "ASH_RESOURCE_RUNTIME_STACK_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let status = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "nested_source_execution_and_release_fit_a_fresh_small_stack",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .status()
            .unwrap();
        assert!(status.success(), "fresh resource runtime process: {status}");
        return;
    }
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut source =
                String::from("import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = ");
            for _ in 0..24 {
                source.push_str("resource cell<R> c = 42 {\n");
            }
            source.push_str("Cell.read c\n");
            for _ in 0..24 {
                source.push_str("}\n");
            }
            let result = run(&source);
            assert_eq!(result.value.to_string(), "42");
            let released = result
                .effect_trace()
                .iter()
                .filter_map(|event| match event {
                    EffectTraceEvent::ResourceReleased(key) => Some(*key),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(released, (0..24).rev().collect::<Vec<_>>());
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn write_then_read_observes_42() {
    let result = run(
        "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource cell<R> c = 41 {\nlet _ = Cell.write (c, 42)\nCell.read c\n}\n",
    );
    assert_eq!(result.value.to_string(), "42");
    assert!(
        result
            .effect_trace()
            .contains(&EffectTraceEvent::ResourceWritten(0))
    );
}

#[test]
fn nested_independent_cells_accept_aliases_and_constructor_transport() {
    let result = run(
        "import @builtin.cell as Cell\ntype Box<A> = Box(A)\nmain : Unit -> Int\nmain () = resource cell<R> outer = 1 {\nresource cell<S> inner = 10 {\nlet alias = outer\nlet boxed = Box inner\nlet _ = Cell.write (alias, 41)\nlet _ = match boxed {\n(Box saved) => Cell.write (saved, 1)\n}\nCell.read outer + Cell.read inner\n}\n}\n",
    );
    assert_eq!(result.value.to_string(), "42");
}

#[test]
fn capturing_accessor_can_be_called_repeatedly() {
    let result = run(
        "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource cell<R> c = 20 {\nlet observe : Unit -> Int ! {Cell.Ops<R>} = fn(ignored) {\nCell.read c\n}\nlet first = observe ()\nlet _ = Cell.write (c, 22)\nfirst + observe ()\n}\n",
    );
    assert_eq!(result.value.to_string(), "42");
}

#[test]
fn copied_result_survives_nested_scope_completion() {
    let result = run(
        "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource cell<R> outer = 20 {\nlet copied = resource cell<S> inner = 22 {\nCell.read inner\n}\ncopied + Cell.read outer\n}\n",
    );
    assert_eq!(result.value.to_string(), "42");
    let resource_events = result
        .effect_trace()
        .iter()
        .filter(|event| {
            matches!(
                event,
                EffectTraceEvent::ResourceAcquired(_)
                    | EffectTraceEvent::ResourceReleased(_)
                    | EffectTraceEvent::ResourceRead(_)
                    | EffectTraceEvent::ResourceWritten(_)
            )
        })
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(
        resource_events,
        [
            EffectTraceEvent::ResourceAcquired(0),
            EffectTraceEvent::ResourceAcquired(1),
            EffectTraceEvent::ResourceRead(1),
            EffectTraceEvent::ResourceReleased(1),
            EffectTraceEvent::ResourceRead(0),
            EffectTraceEvent::ResourceReleased(0),
        ]
    );
}

#[test]
fn capture_resume_retains_the_cell() {
    let result = run(
        "import @builtin.cell as Cell\neffect Pause {\npause : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = handle (resource cell<R> c = 1 {\nlet _ = Cell.write (c, 41)\nlet _ = perform Pause.pause ()\nCell.read c\n}) with Pause {\npause ignored => {\nlet result = resume ()\nresult + 1\n}\n}\n\n",
    );
    assert_eq!(result.value.to_string(), "42");
}

#[test]
fn discard_inside_live_scope_preserves_completion() {
    let result = run(
        "import @builtin.cell as Cell\neffect Stop {\nstop : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = resource cell<R> c = 41 {\nlet _ = handle (perform Stop.stop ()) with Stop {\nstop ignored => discard\n}\nlet _ = Cell.write (c, 42)\nCell.read c\n}\n\n",
    );
    assert_eq!(result.value.to_string(), "42");
}

#[test]
fn sequential_scopes_release_before_next_acquisition() {
    let result = run(
        "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = {\nlet first = resource cell<R> c = 20 {\nCell.read c\n}\nlet second = resource cell<S> c = 22 {\nCell.read c\n}\nfirst + second\n}\n\n",
    );
    assert_eq!(result.value.to_string(), "42");
}

#[test]
fn same_site_closure_uses_its_outer_activation() {
    let result = run(
        "import @builtin.cell as Cell\neffect Pause {\nask : Unit -> Unit\n}\nvisit : Int -> Int ! {Pause}\nvisit depth = resource cell<R> c = (match depth == 0 {\ntrue => 1\nfalse => 41\n}) {\nmatch depth == 0 {\ntrue => {\nlet _ = perform Pause.ask ()\nCell.read c\n}\nfalse => {\nlet observe : Unit -> Int ! {Cell.Ops<R>} = fn(ignored) {\nCell.read c\n}\nhandle (visit 0) with Pause {\nask ignored => {\nlet outer = observe ()\nlet inner = resume ()\nouter + inner\n}\n}\n}\n}\n}\nmain : Unit -> Int\nmain () = handle (visit 1) with Pause {\nask ignored => resume ()\n}\n\n",
    );
    assert_eq!(result.value.to_string(), "42");
}

#[test]
fn initializer_runs_once_before_acquisition() {
    let result = run(
        "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource cell<R> counter = 0 {\nresource cell<S> c = ({\nlet before = Cell.read counter\nlet _ = Cell.write (counter, before + 1)\n41\n}) {\nCell.read c + Cell.read counter\n}\n}\n",
    );
    assert_eq!(result.value.to_string(), "42");
}

#[test]
fn nearest_exact_user_handler_intercepts_cell_operations() {
    let result = run(
        "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource cell<R> c = 1 {\nlet intercepted = handle (Cell.read c) with Cell.Ops<R> {\nread ignored => resume 41\nwrite ignored => resume ()\n}\nintercepted + Cell.read c\n}\n",
    );
    assert_eq!(result.value.to_string(), "42");
}
