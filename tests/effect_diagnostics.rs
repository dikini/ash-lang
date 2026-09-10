use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::{
        EffectElaborator, ElaborationFailure, TypeContext, TypeError, TypeReason, check_module,
    },
    module::{ModuleRoots, load_module_graph},
    resolve::{ResolveModuleError, ResolveReason, resolve_module},
    resolved::{ResolvedDefinitionKind, ResolvedExpr, ResolvedExprKind, ResolvedModule},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempModule(PathBuf);

impl TempModule {
    fn write(source: &str) -> Self {
        let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "ash-effect-diagnostics-{}-{id}.ash",
            std::process::id()
        ));
        fs::write(&path, source).expect("effect diagnostic fixture should be writable");
        Self(path)
    }
}

impl Drop for TempModule {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn resolved_source(source: &str) -> ResolvedModule {
    let fixture = TempModule::write(source);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the effect diagnostic fixture should load");
    let module = graph
        .modules()
        .iter()
        .find(|module| module.id() == graph.entry())
        .expect("the graph should retain its entry");
    resolve_module(module, &[]).expect("the effect diagnostic fixture should resolve")
}

fn typing_error(source: &str) -> TypeError {
    let resolved = resolved_source(source);
    check_module(resolved).expect_err("the effect diagnostic fixture should be rejected")
}

fn typing_reason(source: &str) -> TypeReason {
    match typing_error(source) {
        TypeError::Source(diagnostic) => diagnostic.reason,
        error => panic!("expected a source typing diagnostic, found {error:?}"),
    }
}

#[test]
fn excluded_callback_reports_the_row_contract_in_both_locales_and_json() {
    use ash::{
        message::{Catalogue, Locale},
        presentation::{compile_type_diagnostic, write_human, write_json},
    };
    let source = concat!(
        "effect Bonus {\namount : Unit -> Int\n}\n",
        "add_bonus<R : EffectRow> : (Int -> Int ! {| R}, Int) -> Int ! {Bonus | R}\n",
        "add_bonus (function, value) = function value + perform Bonus.amount ()\n",
        "score : Int -> Int ! {Bonus}\nscore value = value + perform Bonus.amount ()\n",
        "main : Unit -> Int\nmain () = handle (add_bonus (score, 40)) with Bonus {\n",
        "amount ignored => resume 2\n}\n",
    );
    let fixture = TempModule::write(source);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty()).unwrap();
    let loaded = graph
        .modules()
        .iter()
        .find(|module| module.id() == graph.entry())
        .unwrap();
    let TypeError::Source(error) = check_module(resolve_module(loaded, &[]).unwrap()).unwrap_err()
    else {
        panic!("expected a source exclusion diagnostic");
    };
    assert_eq!(error.reason, TypeReason::EffectRowExclusion);
    let view = compile_type_diagnostic(&error, &[loaded.source()]).unwrap();
    for (locale, explanation) in [
        (
            Locale::English,
            "This computation requires an effect excluded from the row tail.",
        ),
        (
            Locale::Bulgarian,
            "Това изчисление изисква ефект, изключен от опашката на реда.",
        ),
    ] {
        let mut output = Vec::new();
        write_human(&mut output, &view, &Catalogue::new(locale).unwrap()).unwrap();
        let output = String::from_utf8(output).unwrap();
        assert!(output.starts_with(explanation), "{output}");
        assert!(output.contains("Bonus | R"), "{output}");
        assert!(output.contains("score, 40"), "{output}");
        assert!(!output.contains("<effect:"), "{output}");
        assert!(!output.contains("?row"), "{output}");
    }
    let mut output = Vec::new();
    write_json(&mut output, &view).unwrap();
    let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(json["reason"], "effect.row-exclusion");
    assert_eq!(json["responsibility"], "source");
    assert_eq!(
        json["labels"][0]["relationship"],
        "excluded_effect_requirement"
    );
    assert_eq!(json["labels"][1]["relationship"], "expected_type");
    assert_eq!(
        json["labels"][0]["byte_start"],
        error.primary.span().range().start()
    );
    assert_eq!(
        json["labels"][1]["byte_start"],
        error.related[0].span().range().start()
    );
}

fn assert_owned_discard_runs(source: &str) {
    let fixture = TempModule::write(source);
    let observation = ash::driver::run_path(ash::driver::RunConfiguration {
        entry: fixture.0.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("structurally owned clause captures may be discarded");
    assert_eq!(observation.value_display(), "()");
}

#[test]
fn discard_closes_direct_and_helper_requests_crossing_an_owned_clause() {
    for request in ["perform B.ask ()", "ask ()"] {
        let source = format!(
            "effect A {{\nask : Unit -> Unit\n}}\neffect B {{\nask : Unit -> Unit\n}}\n\
             ask : Unit -> Unit ! {{B}}\nask () = perform B.ask ()\n\
             main : Unit -> Unit\nmain () = handle (handle (perform A.ask ()) with A {{\n\
             ask ignored => {{\nlet _ = {request}\nresume ()\n}}\n}}) with B {{\nask ignored => discard\n}}\n"
        );
        assert_owned_discard_runs(&source);
    }
}

#[test]
fn discard_instantiates_a_polymorphic_helpers_owned_clause() {
    let source = concat!(
        "effect A {\nask : Unit -> Unit\n}\neffect B<T : Type> {\nask : T -> Unit\n}\n",
        "ask<T : Type> : T -> Unit ! {B<T>}\nask value = handle (perform A.ask ()) with A {\n",
        "ask ignored => {\nlet _ = perform B<T>.ask value\nresume ()\n}\n}\n",
        "main : Unit -> Unit\nmain () = handle (ask 1) with B<Int> {\nask ignored => discard\n}\n",
    );
    assert_owned_discard_runs(source);
}

#[test]
fn ordinary_typing_rejects_ambiguous_row_only_specialization_before_capture() {
    let source = concat!(
        "effect A {\nask : Unit -> Unit\n}\neffect B<T : Type> {\nask : Unit -> Unit\n}\n",
        "ask<T : Type> : Unit -> Unit ! {B<T>, B<Int>}\nask () = handle (perform A.ask ()) with A {\n",
        "ask ignored => {\nlet _ = perform B<T>.ask ()\nlet _ = resume ()\nperform B<Int>.ask ()\n}\n}\n",
        "main : Unit -> Unit\nmain () = {\nlet action : Unit -> Unit ! {B<Bool>, B<Int>} = ask\n",
        "handle (handle (action ()) with B<Bool> {\nask ignored => discard\n}) with B<Int> {\nask ignored => resume ()\n}\n}\n",
    );
    assert_eq!(typing_reason(source), TypeReason::BindingInitializer);
}

#[test]
fn discard_closes_owned_clause_after_same_effect_outward_delegation() {
    assert_owned_discard_runs(concat!(
        "effect B {\nask : Unit -> Unit\n}\nmain : Unit -> Unit\n",
        "main () = handle (handle (perform B.ask ()) with B {\nask ignored => {\n",
        "let _ = perform B.ask ()\nresume ()\n}\n}) with B {\nask ignored => discard\n}\n",
    ));
}

#[test]
fn discard_cannot_skip_an_outer_clauses_scheduled_completion() {
    assert_eq!(
        typing_reason(concat!(
            "effect A {\nask : Unit -> Unit\n}\neffect B {\nask : Unit -> Unit\n}\n",
            "main : Unit -> Unit\nmain () = handle (perform A.ask ()) with A {\n",
            "ask ignored => {\nlet _ = handle ({\nlet _ = perform B.ask ()\nresume ()\n}) with B {\nask ignored => discard\n}\n()\n}\n}\n",
        )),
        TypeReason::DiscardUnsafe
    );
}

#[test]
fn discard_closes_owned_clause_in_a_restored_continuation() {
    assert_owned_discard_runs(concat!(
        "effect A {\nask : Unit -> Unit\n}\neffect B {\nask : Unit -> Unit\n}\neffect C {\nask : Unit -> Unit\n}\n",
        "main : Unit -> Unit\nmain () = handle (handle (handle (perform C.ask ()) with C {\n",
        "ask ignored => {\nlet _ = perform A.ask ()\nlet _ = perform B.ask ()\nresume ()\n}\n",
        "}) with A {\nask ignored => handle ({\nlet _ = resume ()\nperform B.ask ()\n}) with B {\nask ignored => discard\n}\n",
        "}) with B {\nask ignored => resume ()\n}\n",
    ));
}

#[test]
fn unknown_higher_order_and_open_row_calls_block_discard_only() {
    for signature in [
        "relay : (Unit -> Unit ! {B}) -> Unit ! {B}",
        "relay<R : EffectRow> : (Unit -> Unit ! {| R}) -> Unit ! {| R}",
    ] {
        for completion in ["discard", "resume ()"] {
            let source = format!(
                "effect B {{\nask : Unit -> Unit\n}}\n{signature}\nrelay action = action ()\n\
                 ask : Unit -> Unit ! {{B}}\nask () = perform B.ask ()\n\
                 main : Unit -> Unit\nmain () = handle (relay ask) with B {{\nask ignored => {completion}\n}}\n"
            );
            let result = check_module(resolved_source(&source));
            if completion == "discard" {
                assert!(
                    matches!(result, Err(TypeError::Source(error)) if error.reason == TypeReason::DiscardUnsafe)
                );
            } else {
                result.expect("unknown capture obligations must not reject resume-only code");
            }
        }
    }
}

#[test]
fn opaque_request_loop_keeps_its_known_clause_inside_the_clients_capture() {
    let source = concat!(
        "effect H {\nask : Unit -> Unit\n}\neffect A {\nask : Unit -> Unit\n}\neffect B {\nask : Unit -> Unit\n}\n",
        "run : (Unit -> Unit ! {H}) -> Unit ! {A, B}\nrun action = handle (action ()) with H {\n",
        "ask ignored => {\nlet _ = perform A.ask ()\nlet _ = perform B.ask ()\nresume ()\n}\n}\n",
        "guard : (Unit -> Unit ! {H}) -> Unit\nguard action = handle (handle (run action) with A {\nask ignored => resume ()\n}) with B {\nask ignored => discard\n}\n",
        "main : Unit -> Unit\nmain () = ()\n",
    );
    assert_owned_discard_runs(source);
    let exercised = source.replace(
        "main () = ()",
        "main () = guard (fn(ignored) {\nperform H.ask ()\n})",
    );
    assert_owned_discard_runs(&exercised);
}

#[test]
fn unknown_calls_retain_admitted_requests_after_resumption() {
    for completion in ["discard", "resume ()"] {
        let source = format!(
            "effect A {{\nask : Unit -> Unit\n}}\neffect B {{\nask : Unit -> Unit\n}}\n\
             relay : (Unit -> Unit ! {{A, B}}) -> Unit\nrelay action = handle (handle (action ()) with A {{\n\
             ask ignored => handle ({{\nlet _ = resume ()\nperform B.ask ()\n}}) with B {{\nask ignored => {completion}\n}}\n\
             }}) with B {{\nask ignored => resume ()\n}}\nmain : Unit -> Unit\nmain () = ()\n"
        );
        let result = check_module(resolved_source(&source));
        if completion == "discard" {
            assert!(
                matches!(result, Err(TypeError::Source(ref error)) if error.reason == TypeReason::DiscardUnsafe),
                "{result:?}"
            );
        } else {
            result.expect("unknown resumed requests do not prohibit resume-only handlers");
        }
    }
}

#[test]
fn recursive_activations_keep_live_owned_clause_captures_discardable() {
    let source = recursive_activation_source(
        "let _ = match n == 2 {\ntrue => perform A.ask ()\nfalse => relay (n + 1)\n}\nlet _ = resume ()\nperform B.ask ()",
    );
    assert_owned_discard_runs(&source);
}

#[test]
fn recursive_activations_preserve_preceding_clause_consumption() {
    let source = recursive_activation_source(
        "let _ = resume ()\nlet _ = match n == 2 {\ntrue => perform A.ask ()\nfalse => relay (n + 1)\n}\nperform B.ask ()",
    );
    check_module(resolved_source(&source))
        .expect("consumption preceding recursive activation remains safe");
}

fn recursive_activation_source(clause: &str) -> String {
    format!(
        "effect A {{\nask : Unit -> Unit\n}}\neffect B {{\nask : Unit -> Unit\n}}\neffect C {{\nask : Unit -> Unit\n}}\n\
             relay : Int -> Unit ! {{A, B}}\nrelay n = handle (perform C.ask ()) with C {{\nask ignored => {{\n{clause}\n}}\n}}\n\
             main : Unit -> Unit\nmain () = handle (handle (relay 0) with A {{\nask ignored => handle ({{\nlet _ = resume ()\nperform B.ask ()\n}}) with B {{\nask ignored => discard\n}}\n}}) with B {{\nask ignored => resume ()\n}}\n"
    )
}

#[test]
fn nested_resumption_closes_a_live_owned_clause_in_the_selected_suffix() {
    assert_owned_discard_runs(include_str!("fixtures/effects/capture-prefix-after.ash"));
}

fn main_body(module: &ResolvedModule) -> &ResolvedExpr {
    let definition = module
        .definitions()
        .iter()
        .find(|definition| match &definition.kind {
            ResolvedDefinitionKind::Equational(global) => global.interface.name.spelling == "main",
            ResolvedDefinitionKind::InlineOperational(global) => {
                global.header.name.spelling == "main"
            }
        })
        .expect("the diagnostic fixture should declare main");
    let ResolvedDefinitionKind::Equational(main) = &definition.kind else {
        panic!("the diagnostic fixture main should be equational");
    };
    &main.equations[0].body
}

fn handler_source(clause_body: &str) -> String {
    format!(
        "effect Choice {{\nchoose : Unit -> Int\n}}\n\nmain : Unit -> Int\nmain () = handle (perform Choice.choose ()) with Choice {{\nchoose ignored => {clause_body}\n}}\n"
    )
}

#[test]
fn discard_uses_the_existing_completion_reason_family() {
    for (body, reason) in [
        (
            "{\nlet _ = discard\nresume 1\n}",
            TypeReason::ResumeAlreadyConsumed,
        ),
        (
            "{\nlet _ = resume 1\nlet _ = discard\n1\n}",
            TypeReason::ResumeAlreadyConsumed,
        ),
        (
            "{\nlet _ = discard\nlet _ = discard\n1\n}",
            TypeReason::ResumeAlreadyConsumed,
        ),
        (
            "match true {\ntrue => {\nlet _ = discard\n1\n}\nfalse => 2\n}",
            TypeReason::ResumeNotConsumed,
        ),
        (
            "{\nlet deferred = fn(ignored) {\ndiscard\n}\nresume 1\n}",
            TypeReason::ResumeCapture,
        ),
        (
            "{\nlet rec deferred : Unit -> Unit = fn(ignored) {\ndiscard\n}\nresume 1\n}",
            TypeReason::ResumeCapture,
        ),
    ] {
        assert_eq!(typing_reason(&handler_source(body)), reason, "{body}");
    }
}

#[test]
fn discard_usage_diagnostic_names_the_completion_capability() {
    let TypeError::Source(error) = typing_error(&handler_source("{\nlet _ = discard\nresume 1\n}"))
    else {
        panic!("expected source diagnostic")
    };
    assert!(
        error.primary.message().contains("completion capability"),
        "{}",
        error.primary.message()
    );
}

#[test]
fn discard_outside_a_clause_is_a_resolution_error() {
    let fixture = TempModule::write("main : Unit -> Unit\nmain () = discard\n");
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty()).expect("fixture should load");
    let module = graph.module(graph.entry()).expect("entry should exist");
    let ResolveModuleError::Resolution(error) =
        resolve_module(module, &[]).expect_err("outside discard")
    else {
        panic!("expected resolution error")
    };
    assert_eq!(error.reason, ResolveReason::ResumeOutsideClause);
}

#[test]
fn safe_discard_publication_preserves_ordinary_type_error_precedence() {
    for body in [
        "{\nlet _ = discard\n42\n}",
        "match true {\ntrue => resume 1\nfalse => {\nlet _ = discard\n2\n}\n}",
    ] {
        check_module(resolved_source(&handler_source(body))).expect("safe discard should publish");
    }
    assert!(matches!(
        typing_error(&handler_source("discard")),
        TypeError::Mismatch(_)
    ));
    let later_error = format!(
        "{}\nbroken : Unit -> Int\nbroken () = true\n",
        handler_source("{\nlet _ = discard\n42\n}")
    );
    assert_eq!(typing_reason(&later_error), TypeReason::DefinitionResult);
}

#[test]
fn discard_does_not_cross_supplied_method_or_nested_clause_boundaries() {
    let supplied = concat!(
        "effect Ask {\nask : Unit -> Int\n}\n",
        "interface Read<A> {\nread : A -> Unit\n}\n",
        "main : Unit -> Int\nmain () = handle (perform Ask.ask ()) with Ask {\n",
        "ask ignored => {\nnewtype Token = Token(Unit)\n",
        "with Read<Token> {\nread ignored = discard\n}\nresume 42\n}\n}\n",
    );
    assert_eq!(typing_reason(supplied), TypeReason::ResumeCapture);
    let nested = concat!(
        "effect Ask {\nask : Unit -> Int\n}\n",
        "main : Unit -> Int\nmain () = handle (perform Ask.ask ()) with Ask {\n",
        "ask ignored => handle (perform Ask.ask ()) with Ask {\n",
        "ask ignored => {\nlet _ = discard\n42\n}\n}\n}\n",
    );
    assert_eq!(typing_reason(nested), TypeReason::ResumeNotConsumed);
}

#[test]
fn resume_usage_rejects_zero_double_branch_and_capture() {
    let cases = [
        ("zero", handler_source("1"), TypeReason::ResumeNotConsumed),
        (
            "double",
            handler_source("{\nlet first = resume 1\nresume 2\n}"),
            TypeReason::ResumeAlreadyConsumed,
        ),
        (
            "branch",
            handler_source("match true {\ntrue => resume 1\nfalse => 2\n}"),
            TypeReason::ResumeNotConsumed,
        ),
        (
            "capture",
            handler_source(
                "{\nlet deferred : Unit -> Int = fn(ignored) {\nresume 1\n}\nresume 2\n}",
            ),
            TypeReason::ResumeCapture,
        ),
        (
            "recursive-capture",
            handler_source(
                "{\nlet rec deferred : Unit -> Int = fn(ignored) {\nresume 1\n}\nresume 2\n}",
            ),
            TypeReason::ResumeCapture,
        ),
        (
            "nested-clause-does-not-consume-outer",
            concat!(
                "effect Choice {\nchoose : Unit -> Int\n}\n",
                "effect Inner {\nping : Unit -> Unit\n}\n\n",
                "main : Unit -> Int\n",
                "main () = handle (perform Choice.choose ()) with Choice {\n",
                "choose ignored => handle (perform Inner.ping ()) with Inner {\n",
                "ping ignored => resume ()\n",
                "}\n",
                "}\n",
            )
            .to_owned(),
            TypeReason::ResumeNotConsumed,
        ),
    ];

    for (name, source, expected) in cases {
        assert_eq!(typing_reason(&source), expected, "case: {name}");
    }
}

#[test]
fn resume_outside_a_handler_clause_is_rejected_by_resolution() {
    let fixture = TempModule::write("main : Unit -> Int\nmain () = resume 1\n");
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the outside-resume fixture should load");
    let module = graph
        .modules()
        .iter()
        .find(|module| module.id() == graph.entry())
        .expect("the graph should retain its entry");

    match resolve_module(module, &[]).expect_err("resolution should reject outside resume") {
        ResolveModuleError::Resolution(error) => {
            assert_eq!(error.reason, ResolveReason::ResumeOutsideClause)
        }
        error => panic!("expected a resolution diagnostic, found {error:?}"),
    }
}

#[test]
fn written_duplicate_effect_row_has_exact_reason_code() {
    let fixture = TempModule::write(concat!(
        "effect Cell {\nread : Unit -> Int\n}\n\n",
        "duplicate : Unit -> Unit ! {Cell, Cell}\n",
        "duplicate () = ()\n\n",
        "main : Unit -> Unit\nmain () = ()\n",
    ));
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the duplicate-row fixture should load");
    let module = graph
        .modules()
        .iter()
        .find(|module| module.id() == graph.entry())
        .expect("the graph should retain its entry");
    let ResolveModuleError::Resolution(error) =
        resolve_module(module, &[]).expect_err("a written duplicate row should be rejected")
    else {
        panic!("the duplicate row should retain a resolution diagnostic")
    };

    assert_eq!(error.diagnostic().reason.to_string(), "effect.duplicate");
}

#[test]
fn handler_coverage_patterns_and_exact_input_have_stable_diagnostics() {
    let cases = [
        (
            "missing",
            concat!(
                "effect Cell {\nread : Unit -> Int\nwrite : Int -> Unit\n}\n\n",
                "main : Unit -> Int\n",
                "main () = handle (perform Cell.read ()) with Cell {\n",
                "read ignored => resume 1\n",
                "}\n",
            ),
            TypeReason::HandlerCoverage,
        ),
        (
            "duplicate",
            concat!(
                "effect Cell {\nread : Unit -> Int\nwrite : Int -> Unit\n}\n\n",
                "main : Unit -> Int\n",
                "main () = handle (perform Cell.read ()) with Cell {\n",
                "read ignored => resume 1\n",
                "read ignored => resume 2\n",
                "}\n",
            ),
            TypeReason::HandlerCoverage,
        ),
        (
            "refutable-pattern",
            concat!(
                "effect Gate {\nchoose : Bool -> Int\n}\n\n",
                "main : Unit -> Int\n",
                "main () = handle (perform Gate.choose true) with Gate {\n",
                "choose true => resume 1\n",
                "}\n",
            ),
            TypeReason::RefutableHandlerPattern,
        ),
        (
            "different-parameterized-instance",
            concat!(
                "effect State<S> {\nget : Unit -> S\n}\n\n",
                "main : Unit -> Int\n",
                "main () = handle (perform State<Int>.get ()) with State<Bool> {\n",
                "get ignored => resume false\n",
                "}\n",
            ),
            TypeReason::MissingHandledEffect,
        ),
    ];

    for (name, source, expected) in cases {
        assert_eq!(typing_reason(source), expected, "case: {name}");
    }
}

#[test]
fn annotation_and_open_union_failures_are_stable_and_poison_partial_elaboration() {
    let cases = [
        (
            "annotation-excludes-request",
            concat!(
                "effect First {\nread : Unit -> Int\n}\n",
                "effect Second {\nread : Unit -> Int\n}\n\n",
                "bad : Unit -> Int ! {First}\n",
                "bad () = perform Second.read ()\n",
            ),
        ),
        (
            "unrelated-open-union",
            concat!(
                "effect Choice {\nchoose : Unit -> Int\n}\n\n",
                "ambiguous<R : EffectRow> : (Unit -> Int ! {| R}) -> Int ! {| R}\n",
                "ambiguous action = {\n",
                "let value = action ()\n",
                "value + perform Choice.choose ()\n",
                "}\n",
            ),
        ),
    ];
    for (name, source) in cases {
        match typing_error(source) {
            TypeError::Source(diagnostic) => assert_eq!(
                diagnostic.reason,
                TypeReason::AmbiguousEffectRow,
                "case: {name}",
            ),
            error => panic!("case {name}: expected a source typing diagnostic, found {error:?}"),
        }
    }

    let resolved = resolved_source(concat!(
        "effect Cell {\nread : Unit -> Int\nwrite : Int -> Unit\n}\n\n",
        "main : Unit -> Int\n",
        "main () = handle (perform Cell.read ()) with Cell {\n",
        "read ignored => resume 1\n",
        "}\n",
    ));
    let expression = main_body(&resolved);
    let ResolvedExprKind::Handle(handler) = &expression.kind else {
        panic!("the poisoning fixture should resolve a handler");
    };
    let ResolvedExprKind::Perform(request) = &handler.body.kind else {
        panic!("the poisoning fixture should resolve a request");
    };
    let mut elaborator = EffectElaborator::for_resolved_expression(&resolved, expression)
        .expect("the poisoning fixture should reserve its binders");
    let prior = elaborator
        .synthesize(&request.operand, &TypeContext::new())
        .expect("the independent request operand should synthesize");
    match elaborator.synthesize(expression, &TypeContext::new()) {
        Err(TypeError::Source(diagnostic)) => {
            assert_eq!(diagnostic.reason, TypeReason::HandlerCoverage)
        }
        result => panic!("expected handler coverage after prior synthesis, found {result:?}"),
    }
    assert!(matches!(
        elaborator.finish(prior.node),
        Err(ElaborationFailure::InvalidState)
    ));
}
