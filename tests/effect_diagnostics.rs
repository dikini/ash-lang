use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::{ElaborationFailure, Elaborator, TypeContext, TypeError, TypeReason, check_module},
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
    let mut elaborator = Elaborator::for_resolved_expression(&resolved, expression)
        .expect("the poisoning fixture should reserve its binders");
    let prior = elaborator
        .synthesize(&request.operand, &TypeContext::new())
        .expect("the independent request operand should synthesize");
    assert!(matches!(
        elaborator.synthesize(expression, &TypeContext::new()),
        Err(TypeError::Source(diagnostic)) if diagnostic.reason == TypeReason::HandlerCoverage
    ));
    assert!(matches!(
        elaborator.finish(prior.node),
        Err(ElaborationFailure::InvalidState)
    ));
}
