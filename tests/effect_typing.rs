use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::check_module,
    module::{ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    types::{EffectRow, Kind, Type},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempModule(PathBuf);

impl TempModule {
    fn write(source: &str) -> Self {
        let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("ash-effect-typing-{}-{id}.ash", std::process::id()));
        fs::write(&path, source).expect("effect typing fixture should be writable");
        Self(path)
    }
}

impl Drop for TempModule {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn check_source(source: &str) -> ash::resolved::CheckedModule {
    try_check_source(source).expect("the effect typing fixture should check")
}

fn try_check_source(
    source: &str,
) -> Result<ash::resolved::CheckedModule, ash::elaborate::TypeError> {
    let fixture = TempModule::write(source);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the effect typing fixture should load");
    let mut checked = Vec::<ash::resolved::CheckedModule>::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                DependencyExports::new(
                    edge,
                    checked
                        .iter()
                        .find(|dependency| dependency.module() == edge.target())
                        .expect("dependencies precede their importer")
                        .exports(),
                )
                .expect("the exact dependency summary authenticates its edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies)
            .expect("the effect typing fixture should resolve");
        if module.id() == graph.entry() {
            return check_module(resolved);
        }
        checked.push(check_module(resolved).expect("builtin dependency should check"));
    }
    panic!("the graph should retain its entry")
}

fn latent_effects<'a>(checked: &'a ash::resolved::CheckedModule, spelling: &str) -> &'a EffectRow {
    checked
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == spelling)
        .and_then(|scheme| scheme.scheme.value_type().function_view())
        .and_then(|function| function.effects())
        .expect("the checked function should retain a nonempty latent row")
}

#[test]
fn row_unification_retries_coalescing_matches_in_any_written_order() {
    for domain in ["Unit", "A"] {
        for actual in ["Tag<A>, Tag<Int>", "Tag<Int>, Tag<A>"] {
            for expected in ["Tag<Int>, Tag<Bool>", "Tag<Bool>, Tag<Int>"] {
                let expected_domain = if domain == "A" { "Bool" } else { "Unit" };
                let source = format!(
                    "effect Tag<A> {{\n    emit : Unit -> Unit\n}}\n\
                     choose<A> : {domain} -> Unit ! {{{actual}}}\n\
                     choose value = ()\n\
                     accept : ({expected_domain} -> Unit ! {{{expected}}}) -> Unit\n\
                     accept f = ()\n\
                     main : Unit -> Unit\n\
                     main () = accept(choose)\n"
                );
                let fixture = TempModule::write(&source);
                let observation = ash::driver::run_path(ash::driver::RunConfiguration {
                    entry: fixture.0.clone(),
                    roots: ModuleRoots::empty(),
                })
                .unwrap_or_else(|error| {
                    panic!("the substitution A=Bool must check:\n{source}\n{error:?}")
                });
                assert_eq!(observation.value_display(), "()");
            }
        }
    }
}

#[test]
fn row_unification_retains_concrete_single_member_and_idempotent_controls() {
    for (parameters, domain, actual, expected) in [
        ("", "Bool", "Tag<Int>, Tag<Bool>", "Tag<Bool>, Tag<Int>"),
        ("<A>", "A", "Tag<A>", "Tag<Bool>"),
        ("<A>", "A", "Tag<A>, Tag<Bool>", "Tag<Bool>"),
    ] {
        check_source(&format!(
            "effect Tag<A> {{\n    emit : Unit -> Unit\n}}\n\
             choose{parameters} : {domain} -> Unit ! {{{actual}}}\n\
             choose value = ()\n\
             accept : (Bool -> Unit ! {{{expected}}}) -> Unit\n\
             accept f = ()\n\
             main : Unit -> Unit\n\
             main () = accept(choose)\n"
        ));
    }
}

#[test]
fn row_unification_rejects_inconsistent_domain_and_row_arguments() {
    let error = try_check_source(
        "effect Tag<A> {\n    emit : Unit -> Unit\n}\n\
         choose<A> : A -> Unit ! {Tag<A>, Tag<Int>}\n\
         choose value = ()\n\
         accept : (Bool -> Unit ! {Tag<Int>, Tag<String>}) -> Unit\n\
         accept f = ()\n\
         main : Unit -> Unit\n\
         main () = accept(choose)\n",
    )
    .expect_err("no substitution satisfies the domain and the exact effect row");
    assert!(
        matches!(error, ash::elaborate::TypeError::Source(diagnostic)
        if diagnostic.reason == ash::elaborate::TypeReason::Argument)
    );
}

#[test]
fn cyclic_opaque_resumption_consumes_or_owns_the_visible_clause_capture() {
    for clause in [
        "let _ = resume ()\nperform B.ask ()",
        "let _ = perform B.ask ()\nresume ()",
    ] {
        let source = format!(
            "effect H {{\nask : Unit -> Unit\n}}\neffect B {{\nask : Unit -> Unit\n}}\n\
             run : (Unit -> Unit ! {{H}}) -> Unit\nrun action = handle (handle (action ()) with H {{\nask ignored => {{\n{clause}\n}}\n}}) with B {{\nask ignored => discard\n}}\n\
             main : Unit -> Unit\nmain () = ()\n"
        );
        try_check_source(&source)
            .expect("the selected B capture owns every remaining visible H clause");
    }
}

#[test]
fn repeated_handler_requests_complete_consumed_or_owned_captured_clauses() {
    for request in [
        "let _ = perform A.ask ()\nlet _ = resume ()\nperform B.ask ()",
        "let _ = perform A.ask ()\nlet _ = perform B.ask ()\nresume ()",
    ] {
        let source = format!(
            "effect H {{\nask : Unit -> Unit\n}}\neffect A {{\nask : Unit -> Unit\n}}\neffect B {{\nask : Unit -> Unit\n}}\n\
             twice : Unit -> Unit ! {{H}}\ntwice () = {{\nlet _ = perform H.ask ()\nperform H.ask ()\n}}\n\
             run : Unit -> Unit ! {{A, B}}\nrun () = handle (twice ()) with H {{\nask ignored => {{\n{request}\n}}\n}}\n\
             main : Unit -> Unit\nmain () = handle (handle (run ()) with A {{\nask ignored => handle ({{\nlet _ = resume ()\nperform B.ask ()\n}}) with B {{\nask ignored => discard\n}}\n}}) with B {{\nask ignored => resume ()\n}}\n"
        );
        try_check_source(&source)
            .expect("H clauses are consumed or owned by the selected B capture");
    }
}

#[test]
fn generic_local_discard_closes_owned_clauses_when_type_parameters_coincide() {
    for completion in ["discard", "resume ()"] {
        let source = format!(
            "effect E<T> {{\nask : Unit -> Unit\n}}\neffect A {{\nask : Unit -> Unit\n}}\neffect B {{\nask : Unit -> Unit\n}}\n\
             route<T, U> : (T, U) -> Unit ! {{A, B, E<T>}}\nroute ignored = handle ({{\nlet _ = perform E<U>.ask ()\nlet _ = perform A.ask ()\nperform E<T>.ask ()\n}}) with E<U> {{\nask ignored => {{\nlet _ = perform B.ask ()\nresume ()\n}}\n}}\n\
             invoke<T, U> : (T, U) -> Unit ! {{E<T>}}\ninvoke pair = handle (handle (route pair) with A {{\nask ignored => handle ({{\nlet _ = resume ()\nperform B.ask ()\n}}) with B {{\nask ignored => {completion}\n}}\n}}) with B {{\nask ignored => resume ()\n}}\n\
             main : Unit -> Unit\nmain () = ()\n"
        );
        try_check_source(&source).expect("coincident E clauses are owned by the selected capture");
    }
}

#[test]
fn unknown_request_loop_keeps_a_finite_resume_only_handler_summary() {
    check_source(concat!(
        "effect H {\nask : Unit -> Unit\n}\n",
        "effect A {\nask : Unit -> Unit\n}\n",
        "effect B {\nask : Unit -> Unit\n}\n",
        "run : (Unit -> Unit ! {H}) -> Unit ! {A, B}\n",
        "run action = handle (action ()) with H {\n",
        "ask ignored => {\n",
        "let _ = perform A.ask ()\n",
        "let _ = resume ()\n",
        "perform B.ask ()\n",
        "}\n}\n",
        "main : Unit -> Unit\nmain () = ()\n",
    ));
}

#[test]
fn discard_capture_boundary_accepts_direct_and_helper_requests() {
    let mut failures = Vec::new();
    for request in ["perform B.ask ()", "ask ()"] {
        for (index, clause) in [
            format!("{{\nlet _ = handle ({request}) with B {{\nask ignored => discard\n}}\nresume ()\n}}"),
            format!("{{\nlet _ = resume ()\n{request}\n}}"),
        ].into_iter().enumerate() {
            let handled = format!("handle (perform A.ask ()) with A {{\nask ignored => {clause}\n}}");
            let body = if index == 0 { handled } else {
                format!("handle ({handled}) with B {{\nask ignored => discard\n}}")
            };
            if let Err(error) = try_check_source(&format!(
                "effect A {{\nask : Unit -> Unit\n}}\neffect B {{\nask : Unit -> Unit\n}}\n\
                 ask : Unit -> Unit ! {{B}}\nask () = perform B.ask ()\n\
                 main : Unit -> Unit\nmain () = {body}\n"
            )) { failures.push(error); }
        }
    }
    assert!(
        failures.is_empty(),
        "all direct/helper boundaries must check: {failures:?}"
    );
}

#[test]
fn discard_accepts_known_closure_alias_factory_and_recursive_helpers() {
    let mut failures = Vec::new();
    for helper in [
        "let ask = fn(ignored) {\nperform B.ask ()\n}\nlet alias = ask\nalias ()",
        "let factory : Unit -> (Unit -> Unit ! {B}) = fn(ignored) {\nfn(ignored) {\nperform B.ask ()\n}\n}\nlet ask = factory ()\nask ()",
        "let rec ask : Int -> Unit ! {B} = fn(n) {\nmatch n == 2 {\ntrue => perform B.ask ()\nfalse => ask (n + 1)\n}\n}\nask 0",
    ] {
        if let Err(error) = try_check_source(&format!(
            "effect B {{\nask : Unit -> Unit\n}}\nmain : Unit -> Unit\n\
             main () = handle ({{\n{helper}\n}}) with B {{\nask ignored => discard\n}}\n"
        )) {
            failures.push(error);
        }
    }
    assert!(
        failures.is_empty(),
        "all known callables must check: {failures:?}"
    );
}

#[test]
fn discard_keeps_polymorphic_exact_effect_instances_separate() {
    check_source(concat!(
        "effect B<A : Type> {\nask : A -> Unit\n}\n",
        "ask<A : Type> : A -> Unit ! {B<A>}\nask value = perform B<A>.ask value\n",
        "main : Unit -> Unit\nmain () = handle (ask 1) with B<Int> {\nask ignored => discard\n}\n",
    ));
}

#[test]
fn discard_separates_unrelated_instantiations_and_stored_closures() {
    check_source(concat!(
        "effect A {\nask : Unit -> Unit\n}\neffect B<T : Type> {\nask : T -> Unit\n}\n",
        "bad : Unit -> Unit ! {B<Bool>}\nbad () = handle (perform A.ask ()) with A {\n",
        "ask ignored => {\nlet _ = perform B<Bool>.ask true\nresume ()\n}\n}\n",
        "main : Unit -> Unit\nmain () = handle (handle ({\n",
        "let stored : Unit -> Unit ! {B<Bool>} = fn(ignored) {\nbad ()\n}\n",
        "let _ = perform B<Int>.ask 1\nbad ()\n}) with B<Int> {\nask ignored => discard\n",
        "}) with B<Bool> {\nask ignored => resume ()\n}\n",
    ));
}

#[test]
fn discard_inside_a_clause_preserves_already_completed_outer_owner() {
    check_source(concat!(
        "effect A {\nask : Unit -> Unit\n}\neffect B {\nask : Unit -> Unit\n}\n",
        "main : Unit -> Unit\nmain () = handle (perform A.ask ()) with A {\n",
        "ask ignored => {\nlet _ = handle ({\nlet _ = resume ()\nperform B.ask ()\n}) with B {\nask ignored => discard\n}\n()\n}\n}\n",
    ));
}

#[test]
fn discard_accepts_restored_requests_without_live_owners() {
    for computation in [
        "{\nlet _ = perform A.ask ()\nperform B.ask ()\n}",
        "handle (perform C.ask ()) with C {\nask ignored => {\nlet _ = perform A.ask ()\nlet _ = resume ()\nperform B.ask ()\n}\n}",
        "handle (perform C.ask ()) with C {\nask ignored => {\nlet _ = perform B.ask ()\nlet _ = resume ()\nperform A.ask ()\n}\n}",
    ] {
        check_source(&format!(
            "effect A {{\nask : Unit -> Unit\n}}\neffect B {{\nask : Unit -> Unit\n}}\neffect C {{\nask : Unit -> Unit\n}}\n\
             main : Unit -> Unit\nmain () = handle (handle ({computation}) with A {{\nask ignored => handle ({{\nlet _ = resume ()\nperform B.ask ()\n}}) with B {{\nask ignored => discard\n}}\n}}) with B {{\nask ignored => resume ()\n}}\n"
        ));
    }
}

#[test]
fn restored_continuations_reinstall_crossed_handler_filters() {
    check_source(concat!(
        "effect A {\nask : Unit -> Unit\n}\neffect B {\nask : Unit -> Unit\n}\neffect C {\nask : Unit -> Unit\n}\n",
        "main : Unit -> Unit\nmain () = handle (handle (perform C.ask ()) with C {\n",
        "ask ignored => {\nlet _ = handle ({\nlet _ = perform A.ask ()\nperform B.ask ()\n}) with B {\nask ignored => resume ()\n}\nresume ()\n}\n",
        "}) with A {\nask ignored => handle ({\nlet _ = resume ()\nperform B.ask ()\n}) with B {\nask ignored => discard\n}\n}\n",
    ));
}

#[test]
fn separate_calls_of_one_helper_keep_capture_suffixes_separate() {
    check_source(concat!(
        "effect A {\nask : Unit -> Unit\n}\neffect B {\nask : Unit -> Unit\n}\neffect C {\nask : Unit -> Unit\n}\n",
        "ask : Unit -> Unit ! {B}\nask () = perform B.ask ()\n",
        "main : Unit -> Unit\nmain () = handle (handle (handle (perform C.ask ()) with C {\n",
        "ask ignored => {\nlet _ = ask ()\nlet _ = resume ()\nlet _ = perform A.ask ()\nask ()\n}\n",
        "}) with A {\nask ignored => handle ({\nlet _ = resume ()\nperform B.ask ()\n}) with B {\nask ignored => discard\n}\n}) with B {\nask ignored => resume ()\n}\n",
    ));
}

#[test]
fn nested_resumption_does_not_replay_a_prior_calls_suffix() {
    check_source(include_str!("fixtures/effects/capture-prefix-before.ash"));
}

#[test]
fn instantiated_unknown_open_row_does_not_taint_unrelated_effects() {
    check_source(concat!(
        "effect A {\nask : Unit -> Unit\n}\neffect B {\nask : Unit -> Unit\n}\n",
        "relay<R : EffectRow> : (Unit -> Unit ! {| R}) -> Unit ! {| R}\nrelay action = action ()\n",
        "ask : Unit -> Unit ! {A}\nask () = perform A.ask ()\n",
        "main : Unit -> Unit\nmain () = handle (handle ({\nlet _ = perform B.ask ()\nrelay ask\n}) with B {\nask ignored => discard\n}) with A {\nask ignored => resume ()\n}\n",
    ));
}

#[test]
fn restored_handler_resumes_its_selected_capture_only() {
    check_source(concat!(
        "effect A {\nask : Unit -> Unit\n}\neffect B {\nask : Unit -> Unit\n}\neffect D {\nask : Unit -> Unit\n}\neffect E {\nask : Unit -> Unit\n}\n",
        "askB : Unit -> Unit ! {B}\naskB () = perform B.ask ()\n",
        "badD : Unit -> Unit ! {D}\nbadD () = handle (perform E.ask ()) with E {\nask ignored => {\nlet _ = perform D.ask ()\nresume ()\n}\n}\n",
        "runB : Unit -> Unit ! {A, D}\nrunB () = handle ({\nlet _ = askB ()\nlet _ = badD ()\nlet _ = perform A.ask ()\naskB ()\n}) with B {\nask ignored => resume ()\n}\n",
        "main : Unit -> Unit\nmain () = handle (handle (runB ()) with A {\nask ignored => handle ({\nlet _ = resume ()\nperform D.ask ()\n}) with D {\nask ignored => discard\n}\n}) with D {\nask ignored => resume ()\n}\n",
    ));
}

#[test]
fn discard_and_resume_branches_have_unit_completion_carriers() {
    let fixture = TempModule::write(concat!(
        "effect Stop {\nstop : Unit -> Unit\n}\n",
        "main : Unit -> Unit\n",
        "main () = handle (perform Stop.stop ()) with Stop {\n",
        "stop ignored => match true {\ntrue => resume ()\nfalse => discard\n}\n}\n",
    ));
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty()).expect("fixture should load");
    let module = graph.module(graph.entry()).expect("entry should exist");
    let resolved = resolve_module(module, &[]).expect("discard should resolve");
    let ash::resolved::ResolvedDefinitionKind::Equational(main) = &resolved.definitions()[0].kind
    else {
        panic!("main should remain equational")
    };
    let body = &main.equations[0].body;
    let mut elaborator = ash::elaborate::EffectElaborator::for_resolved_expression(&resolved, body)
        .expect("carrier elaborator");
    let typed = elaborator
        .synthesize(body, &ash::elaborate::TypeContext::new())
        .expect("both completion paths should type before capture proof");
    assert_eq!(typed.ty, Type::Unit);
    assert!(typed.effects.is_empty());
    let program = elaborator.finish(typed.node).expect("carrier Core");
    let validated = ash::core::validate_effect(program, &[module.source()])
        .expect("independent Core inference proves both completion paths safe");
    ash::core::validate_effect(
        ash::core::transform::identity_effect_traversal(&validated).expect("identity transform"),
        &[module.source()],
    )
    .expect("transformed discard revalidates");
}

#[test]
fn closed_handler_discharges_exact_effect_and_keeps_main_pure() {
    let checked = check_source(concat!(
        "effect Cell {\n",
        "read : Unit -> Int\n",
        "write : Int -> Unit\n",
        "}\n\n",
        "main : Unit -> Int\n",
        "main () = handle (perform Cell.read ()) with Cell {\n",
        "read ignored => resume 42\n",
        "write value => resume ()\n",
        "}\n",
    ));
    let main = checked
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "main")
        .expect("the checked module should retain main");
    let function = main
        .scheme
        .value_type()
        .function_view()
        .expect("main should retain its function type");

    assert_eq!(function.domain(), &Type::Unit);
    assert_eq!(function.value(), &Type::Int);
    assert!(function.effects().is_none_or(|effects| effects.is_empty()));
}

#[test]
fn strict_children_and_branches_union_rows_before_exact_discharge() {
    let checked = check_source(concat!(
        "effect Cell {\n",
        "read : Unit -> Int\n",
        "write : Int -> Unit\n",
        "}\n\n",
        "read_cell : Unit -> Int ! {Cell}\n",
        "read_cell () = perform Cell.read ()\n\n",
        "main : Unit -> Int\n",
        "main () = handle {\n",
        "let first = read_cell ()\n",
        "match true {\n",
        "true => first + 1\n",
        "false => perform Cell.read ()\n",
        "}\n",
        "} with Cell {\n",
        "read ignored => resume 41\n",
        "write value => resume ()\n",
        "}\n",
    ));
    let read_cell = checked
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "read_cell")
        .expect("the checked module should retain read_cell");
    let function = read_cell
        .scheme
        .value_type()
        .function_view()
        .expect("read_cell should retain its function type");
    let effects = function
        .effects()
        .expect("read_cell should retain its latent source effect row");

    assert_eq!(effects.known().len(), 1);
    assert!(effects.tail().is_none());
}

#[test]
fn resume_usage_accepts_exactly_once_in_every_match_branch() {
    check_source(&handler_source(concat!(
        "match true {\n",
        "true => resume 1\n",
        "false => resume 2\n",
        "}",
    )));
}

#[test]
fn handlers_forward_other_instances_remove_exactly_and_reintroduce_direct_requests() {
    let checked = check_source(concat!(
        "effect State<S> {\n",
        "get : Unit -> S\n",
        "}\n\n",
        "forwarded : Unit -> Bool ! {State<Bool>}\n",
        "forwarded () = handle {\n",
        "let ignored = perform State<Int>.get ()\n",
        "perform State<Bool>.get ()\n",
        "} with State<Int> {\n",
        "get ignored => resume 0\n",
        "}\n\n",
        "delegated : Unit -> Int ! {State<Int>}\n",
        "delegated () = handle (perform State<Int>.get ()) with State<Int> {\n",
        "get ignored => resume (perform State<Int>.get ())\n",
        "}\n\n",
        "weakened : Unit -> Int ! {State<Int>, State<Bool>}\n",
        "weakened () = perform State<Int>.get ()\n",
    ));

    let forwarded = latent_effects(&checked, "forwarded");
    assert_eq!(forwarded.known().len(), 1);
    assert_eq!(
        forwarded.known()[0].arguments(),
        &[ash::types::KindedArgument::TypeArg(Type::Bool)]
    );

    let delegated = latent_effects(&checked, "delegated");
    assert_eq!(delegated.known().len(), 1);
    assert_eq!(
        delegated.known()[0].arguments(),
        &[ash::types::KindedArgument::TypeArg(Type::Int)]
    );

    assert_eq!(latent_effects(&checked, "weakened").known().len(), 2);
}

#[test]
fn open_global_relay_and_local_higher_order_function_generalize_effect_rows() {
    let checked = check_source(concat!(
        "effect Left {\nread : Unit -> Int\n}\n\n",
        "effect Right {\nread : Unit -> Bool\n}\n\n",
        "relay<R : EffectRow, A> : (Unit -> A ! {| R}) -> A ! {| R}\n",
        "relay action = action ()\n\n",
        "read_left : Unit -> Int ! {Left}\n",
        "read_left () = perform Left.read ()\n\n",
        "read_right : Unit -> Bool ! {Right}\n",
        "read_right () = perform Right.read ()\n\n",
        "combined : Unit -> (Int, Bool, Int) ! {Left, Right}\n",
        "combined () = {\n",
        "let local = fn(action) {\n",
        "action ()\n",
        "}\n",
        "(local(read_left), local(read_right), relay(read_left))\n",
        "}\n",
    ));

    let relay = checked
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "relay")
        .expect("the checked module should retain relay");
    assert!(
        relay
            .scheme
            .type_parameters
            .iter()
            .any(|(_, kind)| matches!(kind, Kind::EffectRow))
    );
    assert_eq!(latent_effects(&checked, "combined").known().len(), 2);
}

#[test]
fn omitted_global_binders_generalize_and_instantiate_type_and_row_kinds_in_order() {
    let checked = check_source(concat!(
        "effect Read {\nread : Unit -> Int\n}\n\n",
        "relay : (Unit -> A ! {| R}) -> A ! {| R}\n",
        "relay action = action ()\n\n",
        "read : Unit -> Int ! {Read}\n",
        "read () = perform Read.read ()\n\n",
        "used : Unit -> Int ! {Read}\n",
        "used () = relay(read)\n",
    ));

    let relay = checked
        .schemes()
        .iter()
        .find(|scheme| scheme.spelling == "relay")
        .expect("the checked module should retain relay");
    assert!(matches!(
        relay.scheme.type_parameters.as_ref(),
        [(_, Kind::Type), (_, Kind::EffectRow)]
    ));
    assert_eq!(latent_effects(&checked, "used").known().len(), 1);
}

#[test]
fn annotated_output_row_supplies_the_lacks_fact_for_one_requested_effect() {
    let checked = check_source(concat!(
        "effect Choice {\nchoose : Unit -> Int\n}\n\n",
        "relay<R : EffectRow> : (Unit -> Int ! {| R}) -> Int ! {Choice | R}\n",
        "relay action = {\n",
        "let value = action ()\n",
        "value + perform Choice.choose ()\n",
        "}\n",
    ));

    let effects = latent_effects(&checked, "relay");
    assert_eq!(effects.known().len(), 1);
    assert!(effects.tail().is_some());
}

#[test]
fn generic_callback_respects_result_row_tail_exclusions() {
    let prefix = concat!(
        "effect Bonus {\namount : Unit -> Int\n}\n",
        "add_bonus<R : EffectRow> : (Int -> Int ! {| R}, Int) -> Int ! {Bonus | R}\n",
        "add_bonus (function, value) = (function value) + (perform Bonus.amount ())\n",
        "increment : Int -> Int\nincrement value = value + 1\n",
        "score : Int -> Int ! {Bonus}\nscore points = points + perform Bonus.amount ()\n",
    );
    for (callback, accepted) in [("increment", true), ("score", false)] {
        let source = format!(
            "{prefix}\nmain : Unit -> Int\nmain () = handle (add_bonus ({callback}, 40)) with Bonus {{\namount ignored => resume 2\n}}\n"
        );
        let result = try_check_source(&source);
        assert_eq!(result.is_ok(), accepted, "callback {callback}: {result:?}");
        if let Err(error) = result {
            assert!(
                matches!(
                    error,
                    ash::elaborate::TypeError::Source(_) | ash::elaborate::TypeError::Mismatch(_)
                ),
                "expected source rejection: {error:?}"
            );
        }
    }
}

#[test]
fn handled_callback_exclusions_qualify_declared_result_rows() {
    check_source(concat!(
        "effect Read<A> {\nread : Unit -> A\n}\n",
        "relay<E : EffectRow> : (Unit -> Int ! {Read<Int> | E}) -> Int ! {| E}\n",
        "relay action = handle (action ()) with Read<Int> {\nread ignored => resume 42\n}\n",
        "explicit<E : EffectRow> : (Unit -> Int ! {Read<Int> | E}) -> Int ! {| E}\n",
        "explicit action = {\n",
        "let local : (Unit -> Int ! {Read<Int> | E}) -> Int ! {| E} = fn(callback) {\n",
        "handle (callback ()) with Read<Int> {\nread ignored => resume 42\n}\n}\n",
        "local action\n}\n",
    ));
}

#[test]
fn row_exclusions_preserve_distinct_instances_and_open_forwarding() {
    check_source(concat!(
        "effect Read<A> {\nread : Unit -> A\n}\n",
        "with_read<R : EffectRow> : (Unit -> Int ! {| R}) -> Int ! {Read<Int> | R}\n",
        "with_read action = action () + perform Read<Int>.read ()\n",
        "read_bool : Unit -> Int ! {Read<Bool>}\n",
        "read_bool () = {\nlet ignored = perform Read<Bool>.read ()\n1\n}\n",
        "used : Unit -> Int ! {Read<Int>, Read<Bool>}\nused () = with_read(read_bool)\n",
        "forward<R : EffectRow> : (Unit -> Int ! {| R}) -> Int ! {Read<Int> | R}\n",
        "forward action = with_read(action)\n",
        "relay<R : EffectRow> : (Unit -> Int ! {| R}) -> Int ! {| R}\n",
        "relay action = action ()\n",
        "ordinary : Unit -> Int ! {Read<Bool>}\nordinary () = relay(read_bool)\n",
    ));
}

#[test]
fn row_exclusions_substitute_effect_instance_type_arguments() {
    let prefix = concat!(
        "effect Read<A> {\nread : Unit -> A\n}\n",
        "with_read<A, R : EffectRow> : (Unit -> A ! {| R}) -> A ! {Read<A> | R}\n",
        "with_read action = {\nlet ignored = action ()\nperform Read<A>.read ()\n}\n",
        "pure : Unit -> Int\npure () = 1\n",
        "read_int : Unit -> Int ! {Read<Int>}\nread_int () = perform Read<Int>.read ()\n",
    );
    for (callback, accepted) in [("pure", true), ("read_int", false)] {
        let source = format!(
            "{prefix}\nused : Unit -> Int ! {{Read<Int>}}\nused () = with_read({callback})\n"
        );
        let result = try_check_source(&source);
        assert_eq!(result.is_ok(), accepted, "callback {callback}: {result:?}");
        if let Err(error) = result {
            assert!(
                matches!(
                    error,
                    ash::elaborate::TypeError::Source(_) | ash::elaborate::TypeError::Mismatch(_)
                ),
                "expected source rejection: {error:?}"
            );
        }
    }
}

fn handler_source(clause_body: &str) -> String {
    format!(
        "effect Choice {{\nchoose : Unit -> Int\n}}\n\nmain : Unit -> Int\nmain () = handle (perform Choice.choose ()) with Choice {{\nchoose ignored => {clause_body}\n}}\n"
    )
}
