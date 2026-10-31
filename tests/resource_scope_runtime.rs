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
    let result = run_modular(
        "import @builtin.cell as Cell\neffect E<T> {\nask : Unit -> Int\n}\neffect Pause {\nask : Unit -> Unit\n}\nvisit : Int -> Int ! {Pause}\nvisit depth = resource cell<R> c = depth {\nlet observe : Unit -> Int ! {E<R>} = fn(ignored) {\nperform E<R>.ask ()\n}\nhandle (match depth == 0 {\ntrue => {\nlet _ = perform Pause.ask ()\nobserve ()\n}\nfalse => {\nhandle (visit 0) with Pause {\nask ignored => {\nlet outer = observe ()\nlet inner = resume ()\nouter + inner\n}\n}\n}\n}) with E<R> {\nask ignored => resume (match depth == 0 {\ntrue => 1\nfalse => 41\n})\n}\n}\nmain : Unit -> Int\nmain () = handle (visit 1) with Pause {\nask ignored => resume ()\n}\n",
    );
    assert_eq!(result.value_display(), "42");
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

// Functional source execution uses the modular driver's phase-owner allowances.
// The lower-level helper above intentionally retains standalone API capacities.
fn run_modular(source: &str) -> ash::driver::Observation {
    let path = std::env::temp_dir().join(format!(
        "ash-resource-modular-{}-{}.ash",
        std::process::id(),
        SourceFile::new("resource modular", "")
            .unwrap()
            .id()
            .value()
    ));
    std::fs::write(&path, source).unwrap();
    let result = ash::driver::run_path(ash::driver::RunConfiguration {
        entry: path.clone(),
        roots: ModuleRoots::empty(),
    });
    std::fs::remove_file(path).unwrap();
    result.expect("normal modular resource execution")
}

#[test]
fn write_then_read_observes_42() {
    let result = run(
        "import @builtin.cell as Cell\nmain : Unit -> Int\nmain () = resource cell<R> c = 41 {\nlet _ = Cell.write (c, 42)\nCell.read c\n}\n",
    );
    assert_eq!(result.value.to_string(), "42");
    let acquired = result
        .effect_trace()
        .iter()
        .filter_map(|event| match event {
            EffectTraceEvent::ResourceAcquired(key) => Some(*key),
            _ => None,
        })
        .collect::<Vec<_>>();
    let [key] = acquired.as_slice() else {
        panic!("one Cell activation");
    };
    for event in [
        EffectTraceEvent::ResourceWritten(*key),
        EffectTraceEvent::ResourceRead(*key),
        EffectTraceEvent::ResourceReleased(*key),
    ] {
        assert!(result.effect_trace().contains(&event), "{event:?}");
    }
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
    let acquired = resource_events
        .iter()
        .filter_map(|event| match event {
            EffectTraceEvent::ResourceAcquired(key) => Some(*key),
            _ => None,
        })
        .collect::<Vec<_>>();
    let [outer, inner] = acquired.as_slice() else {
        panic!("two Cell activations");
    };
    assert_ne!(outer, inner);
    assert_eq!(
        resource_events,
        [
            EffectTraceEvent::ResourceAcquired(*outer),
            EffectTraceEvent::ResourceAcquired(*inner),
            EffectTraceEvent::ResourceRead(*inner),
            EffectTraceEvent::ResourceReleased(*inner),
            EffectTraceEvent::ResourceRead(*outer),
            EffectTraceEvent::ResourceReleased(*outer),
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
    let result = run_modular(
        "import @builtin.cell as Cell\neffect Pause {\nask : Unit -> Unit\n}\nvisit : Int -> Int ! {Pause}\nvisit depth = resource cell<R> c = (match depth == 0 {\ntrue => 1\nfalse => 41\n}) {\nmatch depth == 0 {\ntrue => {\nlet _ = perform Pause.ask ()\nCell.read c\n}\nfalse => {\nlet observe : Unit -> Int ! {Cell.Ops<R>} = fn(ignored) {\nCell.read c\n}\nhandle (visit 0) with Pause {\nask ignored => {\nlet outer = observe ()\nlet inner = resume ()\nouter + inner\n}\n}\n}\n}\n}\nmain : Unit -> Int\nmain () = handle (visit 1) with Pause {\nask ignored => resume ()\n}\n\n",
    );
    assert_eq!(result.value_display(), "42");
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

#[test]
fn generic_cell_public_bool_alias_replaces_one_shared_root() {
    let path = std::env::temp_dir().join(format!(
        "ash-generic-runtime-{}.ash",
        SourceFile::new("generic runtime", "").unwrap().id().value(),
    ));
    std::fs::write(
        &path,
        "import @builtin.generic_cell as Cell\nmain : Unit -> Bool\nmain () = resource Cell.Cell<R, Bool> c = false {\n    let alias = c\n    let _ = Cell.write (alias, true)\n    Cell.read c\n}\n",
    )
    .unwrap();
    let result = ash::driver::run_path(ash::driver::RunConfiguration {
        entry: path.clone(),
        roots: ModuleRoots::empty(),
    });
    std::fs::remove_file(path).unwrap();
    assert_eq!(
        result.expect("generic Bool execution").value().to_string(),
        "true"
    );
}

fn generic_runtime_observation(
    source: &str,
    modules: &[(&str, &str)],
    expected: &str,
    acquisitions: usize,
    writes: usize,
) -> Evaluation {
    let directory = std::env::temp_dir().join(format!(
        "ash-generic-observation-{}-{}",
        std::process::id(),
        SourceFile::new("generic observation", "")
            .unwrap()
            .id()
            .value(),
    ));
    std::fs::create_dir(&directory).unwrap();
    for (name, text) in modules {
        std::fs::write(directory.join(name), text).unwrap();
    }
    let path = directory.join("entry.ash");
    std::fs::write(&path, source).unwrap();
    let public = ash::driver::run_path(ash::driver::RunConfiguration {
        entry: path,
        roots: ModuleRoots::empty(),
    });
    std::fs::remove_dir_all(directory).unwrap();
    assert_eq!(
        public.expect("public generic runtime").value().to_string(),
        expected
    );
    // Reconstruct from the same source through ordinary linked validation to
    // observe machine ownership events without adding a product tracing API.
    let evaluation = evaluate_effect(&program_with_modules(source, modules)).unwrap();
    assert_eq!(evaluation.value.to_string(), expected);
    let acquired = evaluation
        .effect_trace()
        .iter()
        .filter_map(|event| match event {
            EffectTraceEvent::ResourceAcquired(key) => Some(*key),
            _ => None,
        })
        .collect::<Vec<_>>();
    let released = evaluation
        .effect_trace()
        .iter()
        .filter_map(|event| match event {
            EffectTraceEvent::ResourceReleased(key) => Some(*key),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(acquired.len(), acquisitions);
    assert_eq!(released.len(), acquisitions);
    for key in &acquired {
        assert_eq!(acquired.iter().filter(|other| *other == key).count(), 1);
        assert_eq!(released.iter().filter(|other| *other == key).count(), 1);
    }
    assert_eq!(
        evaluation
            .effect_trace()
            .iter()
            .filter(|event| matches!(event, EffectTraceEvent::ResourceWritten(_)))
            .count(),
        writes
    );
    evaluation
}

#[test]
fn generic_helper_reads_live_outer_cell_inside_nested_scope() {
    generic_runtime_observation(
        include_str!("fixtures/generic-cell/nested-helper-outer-read.ash"),
        &[],
        "42",
        2,
        0,
    );
}

#[test]
fn generic_helper_reads_live_outer_cell_inside_nested_generic_scope() {
    let source = include_str!("fixtures/generic-cell/nested-helper-outer-read.ash").replace(
        "resource cell<C> cursor",
        "resource Scoped.Cell<C, Int> cursor",
    );
    generic_runtime_observation(&source, &[], "42", 2, 0);
}

#[test]
fn generic_helper_outer_read_passes_inner_cell_source_handler() {
    let source = include_str!("fixtures/generic-cell/nested-helper-inner-handler.ash");
    generic_runtime_observation(source, &[], "42", 2, 0);
    let local = source
        .replace(
            "let _ = Scoped.read cursor\n        Scoped.read outer",
            "let local = Scoped.read cursor\n        let value = Scoped.read outer\n        local + value",
        )
        .replace("read ignored => resume 0", "read ignored => resume 7");
    generic_runtime_observation(&local, &[], "49", 2, 0);
}

#[test]
fn legacy_helper_outer_read_passes_inner_cell_source_handler() {
    generic_runtime_observation(
        include_str!("fixtures/generic-cell/nested-legacy-helper-inner-handler.ash"),
        &[],
        "42",
        2,
        0,
    );
}

#[test]
fn imported_helper_outer_read_passes_inner_cell_source_handler() {
    generic_runtime_observation(
        include_str!("fixtures/generic-cell/nested-helper-import-entry.ash"),
        &[(
            "helper.ash",
            include_str!("fixtures/generic-cell/nested-handler-import.ash"),
        )],
        "42",
        2,
        0,
    );
}

#[test]
fn source_handler_for_outer_cell_still_intercepts_outer_read() {
    generic_runtime_observation(
        include_str!("fixtures/generic-cell/nested-helper-outer-handler.ash"),
        &[],
        "42",
        2,
        0,
    );
}

#[test]
fn legacy_helper_reads_live_outer_cell_inside_nested_legacy_scope() {
    generic_runtime_observation(
        include_str!("fixtures/generic-cell/nested-legacy-helper-outer-read.ash"),
        &[],
        "42",
        2,
        0,
    );
}

#[test]
fn imported_generic_helper_reads_live_outer_cell_inside_nested_scope() {
    let helper = include_str!("fixtures/generic-cell/nested-helper-import.ash");
    for helper in [
        helper.to_owned(),
        helper.replace(
            "resource cell<C> cursor",
            "resource Scoped.Cell<C, Int> cursor",
        ),
    ] {
        generic_runtime_observation(
            include_str!("fixtures/generic-cell/nested-helper-import-entry.ash"),
            &[("helper.ash", &helper)],
            "42",
            2,
            0,
        );
    }
}

#[test]
fn callback_receiving_local_cell_still_mutates_that_cell() {
    for (source, acquisitions) in [
        (
            include_str!("fixtures/generic-cell/local-owner-callback.ash"),
            1,
        ),
        (
            include_str!("fixtures/generic-cell/nested-local-callback.ash"),
            2,
        ),
    ] {
        generic_runtime_observation(source, &[], "42", acquisitions, 1);
    }
}

#[test]
fn generic_cell_p01_fixed_payload_shapes_share_aliases() {
    for (declarations, ty, initial, replacement, answer, expected) in [
        ("", "Int", "41", "42", "Cell.read c", "42"),
        ("", "Bool", "false", "true", "Cell.read c", "true"),
        (
            "",
            "(Int,Bool)",
            "(41,false)",
            "(42,true)",
            "Cell.read c",
            "(42, true)",
        ),
        (
            "type Payload = Pack(Int)\n",
            "Payload",
            "(Pack 41)",
            "(Pack 42)",
            "match Cell.read c {\nPack(value) => value\n}",
            "42",
        ),
    ] {
        let source = format!(
            "import @builtin.generic_cell as Cell\n{declarations}main : Unit -> {result}\nmain () = resource Cell.Cell<R,{ty}> c = {initial} {{\nlet alias = c\nlet _ = Cell.write (alias,{replacement})\n{answer}\n}}\n",
            result = if ty == "Payload" { "Int" } else { ty }
        );
        generic_runtime_observation(&source, &[], expected, 1, 1);
    }
}

#[test]
fn generic_cell_p02_snapshots_and_p03_outer_access_have_actual_values() {
    for (source, expected, acquisitions, writes) in [
        (
            "import @builtin.generic_cell as Cell\nmain : Unit -> (Int,Int)\nmain () = resource Cell.Cell<R,Int> c = 41 {\nlet old = Cell.read c\nlet _ = Cell.write (c,42)\n(old, Cell.read c)\n}\n",
            "(41, 42)",
            1,
            1,
        ),
        (
            "import @builtin.generic_cell as Cell\nmain : Unit -> Int\nmain () = {\nlet saved = resource Cell.Cell<R,Int> c = 41 {\nlet old = Cell.read c\nlet _ = Cell.write (c,42)\nlet snapshot : Unit -> Int = fn(ignored) {\nold\n}\nsnapshot\n}\nsaved ()\n}\n",
            "41",
            1,
            1,
        ),
        (
            "import @builtin.generic_cell as Cell\nmain : Unit -> Int\nmain () = resource Cell.Cell<A,Int> a = 7 {\nlet outer = resource Cell.Cell<B,Cell.Cell<A,Int>> b = a {\nCell.read b\n}\nCell.read outer\n}\n",
            "7",
            2,
            0,
        ),
    ] {
        generic_runtime_observation(source, &[], expected, acquisitions, writes);
    }
}

#[test]
fn generic_cell_p04_p05_p13_imported_snapshots_and_recursive_owners_execute() {
    for (source, modules, expected, acquisitions, writes) in [
        (
            include_str!("fixtures/generic-cell/snapshot-entry.ash"),
            vec![(
                "helper.ash",
                include_str!("fixtures/generic-cell/dependency-helper.ash"),
            )],
            "7",
            2,
            1,
        ),
        (
            include_str!("fixtures/generic-cell/handler-snapshot-entry.ash"),
            vec![(
                "helper.ash",
                include_str!("fixtures/generic-cell/dependency-helper.ash"),
            )],
            "7",
            2,
            1,
        ),
        (
            include_str!("fixtures/generic-cell/recursive-direct-entry.ash"),
            vec![],
            "9",
            2,
            0,
        ),
        (
            include_str!("fixtures/generic-cell/recursive-entry.ash"),
            vec![(
                "helper.ash",
                include_str!("fixtures/generic-cell/recursive-helper.ash"),
            )],
            "9",
            2,
            0,
        ),
    ] {
        generic_runtime_observation(source, &modules, expected, acquisitions, writes);
    }
}

#[test]
fn generic_cell_p07_exact_handler_interception_and_forwarding_execute() {
    for (body, expected, writes) in [
        (
            "handle (Cell.read c) with Cell.Ops<R,Int> {\nread ignored => resume 99\nwrite ignored => resume ()\n}",
            "99",
            0,
        ),
        (
            "let _ = handle (Cell.write (c,42)) with Cell.Ops<R,Int> {\nread ignored => resume 99\nwrite ignored => resume ()\n}\nCell.read c",
            "41",
            0,
        ),
        (
            "let _ = handle (Cell.write (c,42)) with Cell.Ops<R,Int> {\nread value => resume (Cell.read value)\nwrite pair => {\nlet _ = Cell.write pair\nresume ()\n}\n}\nCell.read c",
            "42",
            1,
        ),
    ] {
        let source = format!(
            "import @builtin.generic_cell as Cell\nmain : Unit -> Int\nmain () = resource Cell.Cell<R,Int> c = 41 {{\n{body}\n}}\n"
        );
        generic_runtime_observation(&source, &[], expected, 1, writes);
    }
    generic_runtime_observation(
        include_str!("fixtures/generic-cell/intercept-entry.ash"),
        &[(
            "helper.ash",
            include_str!("fixtures/generic-cell/intercept-helper.ash"),
        )],
        "7",
        1,
        0,
    );
}

#[test]
fn generic_cell_p10_cyclic_immutable_payload_keeps_finite_prefix() {
    generic_runtime_observation(
        "import @builtin.generic_cell as Cell\ntype Stream = Next(Int, Stream)\nmain : Unit -> Int\nmain () = {\nlet rec ones : Stream = Next(1, ones)\nresource Cell.Cell<R,Stream> c = ones {\nmatch Cell.read c {\nNext(first, rest) => match rest {\nNext(second, ignored) => first + second\n}\n}\n}\n}\n",
        &[],
        "2",
        1,
        0,
    );
}

#[test]
fn generic_cell_p12_other_handler_mutation_survives_original_write_interception() {
    generic_runtime_observation(
        "import @builtin.generic_cell as Cell\neffect Tick {\ntick : Unit -> Unit\n}\nmain : Unit -> Int\nmain () = resource Cell.Cell<R,Int> c = 41 {\nlet _ = handle (handle (Cell.write (c,42)) with Cell.Ops<R,Int> {\nread ignored => resume 0\nwrite ignored => {\nlet _ = perform Tick.tick ()\nresume ()\n}\n}) with Tick {\ntick ignored => {\nlet _ = Cell.write (c,99)\nresume ()\n}\n}\nCell.read c\n}\n",
        &[],
        "99",
        1,
        1,
    );
}

#[test]
fn generic_cell_p01_initializer_runs_once_before_body_publication() {
    generic_runtime_observation(
        "import @builtin.generic_cell as Cell\nimport @builtin.cell as Legacy\neffect Init {\nstart : Unit -> Int\n}\nmain : Unit -> (Int,Int)\nmain () = resource cell<C> count = 0 {\nlet answer = handle (resource Cell.Cell<R,Int> c = (perform Init.start ()) {\nlet _ = Cell.write (c,42)\nCell.read c\n}) with Init {\nstart ignored => {\nlet previous = Legacy.read count\nlet _ = Legacy.write (count, previous + 1)\nresume 41\n}\n}\n(answer, Legacy.read count)\n}\n",
        &[],
        "(42, 1)",
        2,
        2,
    );
}

#[test]
fn generic_cell_p06_local_imported_facade_and_same_owner_branch_agree() {
    let modules = [
        (
            "helper.ash",
            include_str!("fixtures/generic-cell/dependency-helper.ash"),
        ),
        (
            "facade.ash",
            "pub import helper (get,put)\npub import @builtin.generic_cell (Cell as Access,Provider,Ops)\n",
        ),
    ];
    for choice in ["true", "false"] {
        generic_runtime_observation(
        &"import facade as Wrapped\nlocal<R> : Wrapped.Access<R,Int> -> Int ! {Wrapped.Ops<R,Int>} where Wrapped.Provider<R,Int>\nlocal value = Wrapped.get value\nmain : Unit -> Int\nmain () = resource Wrapped.Access<R,Int> c = 41 {\nlet alias = c\nlet selected = match true {\ntrue => c\nfalse => alias\n}\nlet _ = Wrapped.put (selected,42)\nlocal c\n}\n".replace("match true", &format!("match {choice}")),
        &modules,
        "42",
        1,
        1,
    );
    }
}

#[test]
fn generic_cell_p08_actual_local_reply_and_independent_escape_execute() {
    for (dependent, answer, expected) in
        [("let held = a\n42", "reply ()", "42"), ("7", "reply", "7")]
    {
        let body = format!(
            "resource Cell.Cell<A,Int> a = 1 {{\nresource Cell.Cell<B,(Unit -> Int)> b = independent {{\nlet actual : Unit -> Int = fn(ignored) {{\n{dependent}\n}}\nlet reply = handle (Cell.read b) with Cell.Ops<B,(Unit -> Int)> {{\nread ignored => resume actual\nwrite ignored => resume ()\n}}\n{answer}\n}}\n}}"
        );
        let main = if answer == "reply" {
            format!("let saved = {body}\nsaved ()")
        } else {
            body
        };
        let source = format!(
            "import @builtin.generic_cell as Cell\nindependent : Unit -> Int\nindependent () = 7\nmain : Unit -> Int\nmain () = {{\n{main}\n}}\n"
        );
        generic_runtime_observation(&source, &[], expected, 2, 0);
    }
}

#[test]
fn generic_cell_p09_independent_and_enclosing_payload_crossings_execute() {
    generic_runtime_observation(
        "import @builtin.generic_cell as Cell\neffect Send {\nsend : Int -> Int\n}\nmain : Unit -> Int\nmain () = handle (resource Cell.Cell<R,Int> c = 41 {\nlet old = Cell.read c\nlet _ = Cell.write (c,42)\nperform Send.send old\n}) with Send {\nsend value => resume (value + 1)\n}\n",
        &[],
        "42",
        1,
        1,
    );
    generic_runtime_observation(
        "import @builtin.generic_cell as Cell\neffect Send {\nsend : (Unit -> Int) -> Int\n}\nmain : Unit -> Int\nmain () = resource Cell.Cell<A,Int> a = 7 {\nhandle (resource Cell.Cell<B,Int> b = 41 {\nlet payload : Unit -> Int = fn(ignored) {\nlet held = a\n7\n}\nperform Send.send payload\n}) with Send {\nsend action => resume (action ())\n}\n}\n",
        &[],
        "7",
        2,
        0,
    );
}

#[test]
fn generic_cell_p11_repeated_monomorphic_reads_and_legacy_nesting_execute() {
    generic_runtime_observation(
        "import @builtin.generic_cell as Cell\nimport @builtin.cell as Legacy\nplus : Int -> Int\nplus value = value + 1\nmain : Unit -> Int\nmain () = resource cell<L> legacy = 40 {\nresource Cell.Cell<R,(Int -> Int)> c = plus {\nlet first = Cell.read c\nlet second = Cell.read c\nfirst (second (Legacy.read legacy))\n}\n}\n",
        &[],
        "42",
        2,
        0,
    );
}

#[test]
fn generic_cell_p13_reply_and_later_stored_function_have_distinct_actual_values() {
    generic_runtime_observation(
        "import @builtin.generic_cell as Cell\nindependent : Unit -> Int\nindependent () = 7\nmain : Unit -> (Int,Int)\nmain () = resource Cell.Cell<A,Int> a = 1 {\nresource Cell.Cell<B,(Unit -> Int)> b = independent {\nlet dependent : Unit -> Int = fn(ignored) {\nlet held = a\n42\n}\nlet reply = handle (Cell.read b) with Cell.Ops<B,(Unit -> Int)> {\nread ignored => {\nlet _ = Cell.write (b,dependent)\nresume independent\n}\nwrite ignored => resume ()\n}\nlet later = Cell.read b\n(reply (), later ())\n}\n}\n",
        &[],
        "(7, 42)",
        2,
        1,
    );
}

#[test]
fn generic_cell_indexed_effectful_function_payload_uses_its_saved_outer_owner() {
    generic_runtime_observation(
        "import @builtin.generic_cell as Cell\nimport helper (get)\nmain : Unit -> Int\nmain () = resource Cell.Cell<A,Int> a = 7 {\nlet access : Unit -> Int ! {Cell.Ops<A,Int>} = fn(ignored) {\nCell.read a\n}\nresource Cell.Cell<B,(Unit -> Int ! {Cell.Ops<A,Int>})> b = access {\nlet action = get b\naction ()\n}\n}\n",
        &[(
            "helper.ash",
            include_str!("fixtures/generic-cell/dependency-helper.ash"),
        )],
        "7",
        2,
        0,
    );
}

#[test]
fn generic_cell_c01_capture_resume_moves_the_latest_function_root() {
    generic_runtime_observation(
        "import @builtin.generic_cell as Cell\neffect Pause {\npause : Unit -> Unit\n}\ninitial : Unit -> Int\ninitial () = 7\nmain : Unit -> (Int,Int)\nmain () = handle (resource Cell.Cell<R,(Unit -> Int)> c = initial {\nlet first : Unit -> Int = fn(ignored) {\n41\n}\nlet _ = Cell.write (c,first)\nlet _ = perform Pause.pause ()\nlet observed = Cell.read c\nlet first_result = observed ()\nlet second : Unit -> Int = fn(ignored) {\n42\n}\nlet _ = Cell.write (c,second)\nlet _ = perform Pause.pause ()\nlet final = Cell.read c\n(first_result, final ())\n}) with Pause {\npause ignored => resume ()\n}\n",
        &[],
        "(41, 42)",
        1,
        2,
    );
}

#[test]
fn generic_cell_c02_owned_discard_keeps_both_cells_live_for_dependent_cleanup() {
    let result = generic_runtime_observation(
        "import @builtin.generic_cell as Cell\neffect Stop {\nstop : Unit -> Unit\n}\nindependent : Unit -> Int\nindependent () = 7\nmain : Unit -> Int\nmain () = resource Cell.Cell<A,Int> trace = 0 {\nlet _ = handle (resource Cell.Cell<B,(Unit -> Int)> c = independent {\ncleanup fn(ignored) {\nlet action = Cell.read c\nCell.write (trace,action ())\n} {\nperform Stop.stop ()\n}\n}) with Stop {\nstop ignored => discard\n}\nCell.read trace\n}\n",
        &[],
        "7",
        2,
        1,
    );
    let acquired = result
        .effect_trace()
        .iter()
        .filter_map(|event| match event {
            EffectTraceEvent::ResourceAcquired(key) => Some(*key),
            _ => None,
        })
        .collect::<Vec<_>>();
    let [outer, inner] = acquired.as_slice() else {
        panic!("two Cell activations");
    };
    assert_ne!(outer, inner);
    let written = result
        .effect_trace()
        .iter()
        .position(|event| matches!(event, EffectTraceEvent::ResourceWritten(key) if key == outer))
        .unwrap();
    let inner_release = result
        .effect_trace()
        .iter()
        .position(|event| matches!(event, EffectTraceEvent::ResourceReleased(key) if key == inner))
        .unwrap();
    assert!(
        written < inner_release,
        "dependent cleanup precedes inner release"
    );
}

#[test]
fn generic_cell_c04_handle_and_replacement_effects_keep_strict_source_order() {
    generic_runtime_observation(
        include_str!("fixtures/generic-cell/operand-order-entry.ash"),
        &[],
        "(42, 12)",
        2,
        3,
    );
}

#[test]
fn generic_cell_c02_initializer_discard_never_publishes_the_unacquired_owner() {
    let result = generic_runtime_observation(
        "import @builtin.generic_cell as Cell\neffect Stop {\nstop : Unit -> Int\n}\nmain : Unit -> Int\nmain () = resource Cell.Cell<A,Int> side = 0 {\nlet _ = handle ({\nlet answer = resource Cell.Cell<B,Int> target = ({\nlet _ = Cell.write (side,1)\nperform Stop.stop ()\n}) {\nlet _ = Cell.write (side,99)\nCell.read target\n}\nCell.write (side,88)\n}) with Stop {\nstop ignored => discard\n}\nCell.read side\n}\n",
        &[],
        "1",
        1,
        1,
    );
    assert_eq!(
        result
            .effect_trace()
            .iter()
            .filter(|event| matches!(event, EffectTraceEvent::ResourceAcquired(_)))
            .count(),
        1
    );
}

#[test]
fn returned_closure_recurrence_keeps_existing_context_bound() {
    assert_eq!(run("import @builtin.cell as Cell\ntype Chain = Chain(Unit -> Chain)\nmake : Unit -> Chain\nmake () = Chain (fn(ignored) {\n    make ()\n})\nnext : Chain -> Chain\nnext (Chain(step)) = step ()\nwalk : (Int, Chain) -> Int\nwalk (depth, value) = match depth == 0 {\ntrue => 42\nfalse => walk (0, next value)\n}\nmain : Unit -> Int\nmain () = resource cell<R> c = 7 {\n    let _ = Cell.read c\n    walk (1, make ())\n}\n").value.to_string(), "42");
}
