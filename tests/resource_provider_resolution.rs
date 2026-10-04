use ash::{
    module::{ModuleRoots, load_module_graph},
    resolve::resolve_module,
    resolved::{ResolvedDefinitionKind, ResolvedExprKind},
};
use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

static IDS: AtomicU64 = AtomicU64::new(0);
struct Source(PathBuf);
impl Source {
    fn new(text: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "ash-provider-resolve-{}-{}.ash",
            std::process::id(),
            IDS.fetch_add(1, Ordering::Relaxed)
        ));
        fs::write(&path, text).unwrap();
        Self(path)
    }
}
impl Drop for Source {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

const PRELUDE: &str = "type Report<A, B, T> = Scope(T)\ntype State<R> = Token(Unit)\ninterface ConnectionProvider<R> {\nread : Connection<R> -> Int\n}\neffect ConnectionOps<R> {\nread : Connection<R> -> Int\n}\neffect NativeOps<R> {\nopen : Int -> State<R>\nclose : State<R> -> Unit\nread : State<R> -> Int\n}\n";
const DEFINITION: &str = "pub resource Connection<R> {\ninput Int\nstate State<R>\nresult Report<Int, Int, T> for <T>\nprovider ConnectionProvider<R>\neffect ConnectionOps<R>\ninterpret NativeOps<R>\nacquire config => perform NativeOps<R>.open config\nfinish state => perform NativeOps<R>.close state\nhandlers state {\nread db => resume (perform NativeOps<R>.read state)\n}\n}\n";

fn body(module: &ash::resolved::ResolvedModule) -> &ash::resolved::ResolvedExpr {
    let ResolvedDefinitionKind::Equational(global) = &module.definitions()[0].kind else {
        panic!("equational fixture")
    };
    &global.equations[0].body
}

#[test]
fn declarations_preserve_templates_and_instances_reference_the_defining_family() {
    let source = Source::new(&format!(
        "{PRELUDE}{DEFINITION}main : Unit -> Int\nmain () = resource Connection<C> db = 0 {{\n42\n}}\n"
    ));
    let graph = load_module_graph(&source.0, &ModuleRoots::empty()).unwrap();
    let loaded = graph.modules().last().unwrap();
    let module = resolve_module(loaded, &[]).unwrap();
    let definition = &module.resources()[0];
    let ResolvedExprKind::ProviderResource(instance) = &body(&module).kind else {
        panic!("provider instance")
    };
    assert_eq!(instance.definition, definition.id);
    assert_eq!(instance.family, definition.family);
    assert_eq!(definition.id.module(), module.module());
    assert_ne!(instance.identity.id, definition.parameters[0].id);
    assert!(
        module.registry().nominal(definition.family).is_none(),
        "opaque family must have no data constructors"
    );
    assert!(matches!(
        definition.acquire.kind,
        ResolvedExprKind::Perform(_)
    ));
    assert_eq!(definition.handlers.len(), 1);
}

#[test]
fn fresh_handle_and_identity_are_unavailable_in_initializer_and_after_body() {
    for expression in [
        "resource Connection<C> db = db {\n42\n}",
        "resource Connection<C> db = (perform NativeOps<C>.read ()) {\n42\n}",
        "{\nlet answer = resource Connection<C> db = 0 {\n42\n}\ndb\n}",
    ] {
        let source = Source::new(&format!(
            "{PRELUDE}{DEFINITION}main : Unit -> Int\nmain () = {expression}\n"
        ));
        let graph = load_module_graph(&source.0, &ModuleRoots::empty()).unwrap();
        assert!(
            resolve_module(graph.modules().last().unwrap(), &[]).is_err(),
            "{expression}"
        );
    }
}

#[test]
fn acquire_and_finish_binders_do_not_leak_into_other_templates() {
    let bad = DEFINITION.replace("close state", "close config");
    let source = Source::new(&format!("{PRELUDE}{bad}"));
    let graph = load_module_graph(&source.0, &ModuleRoots::empty()).unwrap();
    assert!(resolve_module(graph.modules().last().unwrap(), &[]).is_err());
}

#[test]
fn resource_answer_parameter_is_distinct_from_resource_identity() {
    let bad = DEFINITION.replace("T> for <T>", "R> for <R>");
    let source = Source::new(&format!("{PRELUDE}{bad}"));
    let graph = load_module_graph(&source.0, &ModuleRoots::empty()).unwrap();
    assert!(resolve_module(graph.modules().last().unwrap(), &[]).is_err());
}

#[test]
fn second_resource_parameter_remains_a_template_while_instances_bind_only_fresh_identity() {
    let statement = "interface StatementProvider<S, C> {\nstep : Statement<S, C> -> Int\n}\neffect StatementOps<S, C> {\nstep : Statement<S, C> -> Int\n}\neffect StatementNative<S, C> {\nprepare : (Connection<C>, Int) -> State<S>\nfinish : State<S> -> Unit\nstep : State<S> -> Int\n}\nresource Statement<S, C> {\ninput (Connection<C>, Int)\nstate State<S>\nresult Report<Int, Int, T> for <T>\nprovider StatementProvider<S, C>\neffect StatementOps<S, C>\ninterpret StatementNative<S, C>\nacquire input => perform StatementNative<S, C>.prepare input\nfinish state => perform StatementNative<S, C>.finish state\nhandlers state {\nstep stmt => resume (perform StatementNative<S, C>.step state)\n}\n}\n";
    let source = Source::new(&format!(
        "{PRELUDE}{DEFINITION}{statement}main : Unit -> Int\nmain () = resource Connection<C> db = 0 {{\nresource Statement<S> stmt = (db, 1) {{\n42\n}}\n}}\n"
    ));
    let graph = load_module_graph(&source.0, &ModuleRoots::empty()).unwrap();
    let module = resolve_module(graph.modules().last().unwrap(), &[]).unwrap();
    let ResolvedExprKind::ProviderResource(connection) = &body(&module).kind else {
        panic!("connection")
    };
    let ResolvedExprKind::Block(block) = &connection.body.kind else {
        panic!("connection body")
    };
    let ResolvedExprKind::ProviderResource(statement) = &block.result.kind else {
        panic!("statement")
    };
    assert_eq!(
        module
            .resource(statement.definition)
            .unwrap()
            .parameters
            .len(),
        2
    );
    assert_ne!(connection.identity.id, statement.identity.id);
    assert_eq!(connection.forwarding.len(), 1);
    assert_eq!(statement.forwarding.len(), 1);
    assert_ne!(connection.provider, statement.provider);
    assert_ne!(
        connection.forwarding[0].binder.id,
        statement.forwarding[0].binder.id
    );
    assert_eq!(statement.definition, module.resources()[1].id);
}

#[test]
fn frontend_resource_templates_cannot_publish_checked_modules_before_lifecycle_support() {
    let source = Source::new(&format!("{PRELUDE}{DEFINITION}"));
    let graph = load_module_graph(&source.0, &ModuleRoots::empty()).unwrap();
    let module = resolve_module(graph.modules().last().unwrap(), &[]).unwrap();
    assert!(ash::elaborate::check_module(module).is_err());
}

#[test]
fn nested_provider_instances_resolve_and_drop_on_a_small_stack() {
    for result in ["42", "missing_name"] {
        let mut text = format!("{PRELUDE}{DEFINITION}main : Unit -> Int\nmain () = ");
        for _ in 0..128 {
            text.push_str("resource Connection<C> db = 0 {\n");
        }
        text.push_str(result);
        text.push('\n');
        for _ in 0..128 {
            text.push_str("}\n");
        }
        let source = Source::new(&text);
        let graph = load_module_graph(&source.0, &ModuleRoots::empty()).unwrap();
        let should_succeed = result == "42";
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let resolved = resolve_module(graph.modules().last().unwrap(), &[]);
                assert_eq!(resolved.is_ok(), should_succeed);
                drop(resolved);
                drop(graph);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
