use ash::{
    module::{ModuleRoots, load_module_graph},
    resolve::{ResolveModuleError, ResolveReason, resolve_module},
    resolved::{ResolvedDefinitionKind, ResolvedExprKind},
    types::{Kind, KindedArgument, Type},
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
    assert!(definition.family_template.is_none());
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

// Ordinary local declarations exercise metadata retention without claiming
// Layout authority, native admission, family selection or executable handlers.
const FAMILY_PRELUDE: &str = "effect Mark {\nmark : Unit -> Unit\n}\ninterface Marker<Payload> {\nmark : Payload -> Unit\n}\ninterface Route<Rows : EffectRow, Payload> {\nroute : (Payload, Unit -> Unit ! {| Rows}) -> Unit\n}\ninterface StorageProvider<R, Payload, Rows : EffectRow> {\nstore : (Connection<R>, Payload, Unit -> Unit ! {| Rows}) -> Payload\nload : Connection<R> -> Payload ! {| Rows}\n}\neffect StorageOps<R, Rows : EffectRow, Payload> {\nstore : (Connection<R>, Payload) -> Payload\nload : Connection<R> -> Payload\n}\neffect StorageNative<Payload, Rows : EffectRow, R> {\nstore : (State<R>, Payload) -> Payload\nload : State<R> -> Payload\n}\n";
const FAMILY_TEMPLATE: &str = "family<Payload> where Marker<Payload>, Route<{Mark}, Payload> {\nprovider StorageProvider<R, Payload, {Mark}>\neffect StorageOps<R, {Mark}, Payload>\ninterpret StorageNative<Payload, {Mark}, R>\nhandlers family_state {\nload access => resume (perform StorageNative<Payload, {Mark}, R>.load family_state)\nstore (access, value) => resume (perform StorageNative<Payload, {Mark}, R>.store (family_state, value))\n}\n}\n";

fn family_source() -> String {
    format!(
        "{PRELUDE}{FAMILY_PRELUDE}{}",
        DEFINITION.replacen(
            "acquire config",
            &format!("{FAMILY_TEMPLATE}acquire config"),
            1
        )
    )
}

#[test]
fn family_failure_paths_drop_retained_bodies_and_current_patterns_on_a_small_stack() {
    // Leave room for the enclosing resource, family, handler and resume syntax.
    let expression = std::iter::repeat_n("1", ash::parser::STRUCTURAL_DEPTH_LIMIT - 16)
        .collect::<Vec<_>>()
        .join(" + ");
    let retained_body = family_source().replace(
        "load access => resume (perform StorageNative<Payload, {Mark}, R>.load family_state)",
        &format!("load access => resume ({expression})"),
    );
    // Public constructor-pattern syntax has a tighter parser depth bound than
    // expressions. Eight levels exercise the current-pattern owner; the long
    // earlier body supplies the recursive cleanup pressure in both paths.
    let pattern = format!("{}_{}", "Step(".repeat(8), ")".repeat(8));
    for (text, missing) in [
        (
            retained_body.replace("NativeOps<R>.open config", "NativeOps<R>.open missing_outer_input"),
            "missing_outer_input",
        ),
        (
            retained_body.replace(
                "store (access, value) => resume (perform StorageNative<Payload, {Mark}, R>.store (family_state, value))",
                &format!("store {pattern} => missing_family_body"),
            ),
            "missing_family_body",
        ),
    ] {
        let text = format!("type Loop =\nEnd\n| Step(Loop)\n\n{text}");
        let expected_start = text.find(missing).unwrap() as u32;
        let source = Source::new(&text);
        // Parsing and graph construction happen on the main thread, matching
        // the existing provider-resolution small-stack harness above.
        let graph = load_module_graph(&source.0, &ModuleRoots::empty()).unwrap();
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(move || {
                let Err(ResolveModuleError::Resolution(error)) =
                    resolve_module(graph.modules().last().unwrap(), &[])
                else {
                    panic!("expected the late name-resolution failure at {missing}")
                };
                assert_eq!(error.reason, ResolveReason::UnknownName);
                let range = error.primary.span().range();
                assert_eq!(range.start(), expected_start);
                assert_eq!(range.end(), expected_start + missing.len() as u32);
                drop(error);
                drop(graph);
            })
            .unwrap()
            .join()
            .expect("family failure cleanup should remain within the stack budget");
    }
}

#[test]
fn family_templates_retain_distinct_scope_ordered_arguments_and_canonical_operations() {
    let source = Source::new(&family_source());
    let graph = load_module_graph(&source.0, &ModuleRoots::empty()).unwrap();
    let loaded = graph.modules().last().unwrap();
    let module = resolve_module(loaded, &[]).unwrap();
    let resource = &module.resources()[0];
    let family = resource
        .family_template
        .as_ref()
        .expect("retained family template");
    let owner = resource.parameters[0].id;
    let payload = family.parameter.id;
    assert_eq!(family.parameter.spelling, "Payload");
    assert_eq!(family.parameter.kind, Kind::Type);
    assert_ne!(payload, owner);
    assert_ne!(payload, resource.answer.id);
    assert_eq!(resource.answer.spelling, "T");
    assert_eq!(
        module.registry().type_variable(payload),
        Some(&family.parameter)
    );
    assert_ne!(family.handlers_binder.id, resource.handlers_binder.id);
    assert_ne!(family.handlers_binder.id, resource.finish_binder.id);
    assert_ne!(family.handlers_binder.id, resource.acquire_binder.id);

    let interface = |name: &str| {
        module
            .interfaces()
            .iter()
            .find(|item| item.spelling == name)
            .unwrap()
    };
    let effect = |name: &str| {
        module
            .effects()
            .iter()
            .find(|item| item.spelling == name)
            .unwrap()
    };
    assert_eq!(family.requirements.len(), 2);
    assert_eq!(family.requirements[0].interface.id, interface("Marker").id);
    assert_eq!(family.requirements[1].interface.id, interface("Route").id);
    assert_eq!(
        family.requirements[0].arguments[0].ty,
        KindedArgument::TypeArg(Type::Variable(payload))
    );
    assert_eq!(
        family.requirements[1].arguments[1].ty,
        KindedArgument::TypeArg(Type::Variable(payload))
    );
    let provider = interface("StorageProvider");
    assert_eq!(family.provider.interface.id, provider.id);
    assert_eq!(provider.parameters[0].kind, Kind::Type);
    assert_eq!(provider.parameters[1].kind, Kind::Type);
    assert_eq!(provider.parameters[2].kind, Kind::EffectRow);
    assert_eq!(provider.methods[0].id.interface(), provider.id);
    assert_eq!(provider.methods[0].id.declaration(), 0);
    assert_eq!(provider.methods[1].id.declaration(), 1);
    assert_eq!(family.provider.arguments.len(), 3);
    assert_eq!(
        family.provider.arguments[0].ty,
        KindedArgument::TypeArg(Type::Variable(owner))
    );
    assert_eq!(
        family.provider.arguments[1].ty,
        KindedArgument::TypeArg(Type::Variable(payload))
    );
    let provided = effect("StorageOps");
    let interpreted = effect("StorageNative");
    assert_eq!(family.provided.instance.effect(), provided.id);
    assert_eq!(family.interpreted.instance.effect(), interpreted.id);
    assert_eq!(family.provided.instance.arguments().len(), 3);
    assert_eq!(family.interpreted.instance.arguments().len(), 3);
    assert_eq!(
        family.provided.instance.arguments()[0],
        KindedArgument::TypeArg(Type::Variable(owner))
    );
    assert_eq!(
        family.provided.instance.arguments()[2],
        KindedArgument::TypeArg(Type::Variable(payload))
    );
    assert_eq!(
        family.interpreted.instance.arguments()[0],
        KindedArgument::TypeArg(Type::Variable(payload))
    );
    assert_eq!(
        family.interpreted.instance.arguments()[2],
        KindedArgument::TypeArg(Type::Variable(owner))
    );
    for argument in [
        &family.requirements[1].arguments[0].ty,
        &family.provider.arguments[2].ty,
        &family.provided.instance.arguments()[1],
        &family.interpreted.instance.arguments()[1],
    ] {
        let KindedArgument::RowArg(row) = argument else {
            panic!("written row actual must remain a RowArg")
        };
        assert!(row.tail().is_none());
        assert_eq!(row.known().len(), 1);
        assert_eq!(row.known()[0].effect(), effect("Mark").id);
    }
    assert_eq!(family.handlers.len(), 2);
    for (clause, ordinal) in family.handlers.iter().zip([1, 0]) {
        assert_eq!(clause.operation, provided.operations[ordinal].id);
        assert_eq!(clause.spelling, provided.operations[ordinal].spelling);
        let ResolvedExprKind::Resume(resume) = &clause.body.kind else {
            panic!("family clause resumes its native operation result")
        };
        assert_eq!(resume.owner, Some(clause.resume));
        let ResolvedExprKind::Perform(request) = &resume.value.kind else {
            panic!("the native request is retained")
        };
        assert_eq!(request.operation, interpreted.operations[ordinal].id);
        assert_eq!(request.effect.instance, family.interpreted.instance);
    }
    let ResolvedExprKind::Resume(resume) = &family.handlers[0].body.kind else {
        panic!("load clause")
    };
    let ResolvedExprKind::Perform(request) = &resume.value.kind else {
        panic!("load request")
    };
    let ResolvedExprKind::Occurrence(state) = &request.operand.kind else {
        panic!("family state operand")
    };
    assert_eq!(state.global_binder(), Some(family.handlers_binder.id));
    assert_eq!(family.origin.primary_span(), family.span);
    assert_eq!(family.span.source(), loaded.source().id());
    assert_eq!(
        family.parameter.origin.primary_span().source(),
        loaded.source().id()
    );
    assert!(family.span.range().start() >= resource.span.range().start());
    assert!(family.span.range().end() <= resource.span.range().end());
    for clause in &family.handlers {
        assert_eq!(clause.span.source(), family.span.source());
        assert!(clause.span.range().start() >= family.span.range().start());
        assert!(clause.span.range().end() <= family.span.range().end());
    }
    let span = family.parameter.origin.primary_span();
    assert_eq!(
        &loaded.source().text()[span.range().start() as usize..span.range().end() as usize],
        "Payload"
    );
    let diagnostic = match ash::elaborate::check_module(module) {
        Err(ash::elaborate::TypeError::Source(diagnostic)) => diagnostic,
        Err(error) => panic!(
            "resolved family metadata must reach the explicit unsupported checkpoint: {error:?}"
        ),
        Ok(_) => panic!("resolved family metadata must not become executable"),
    };
    assert_eq!(
        diagnostic.primary.message(),
        "resource family templates are not executable in this experimental checkpoint"
    );
}

#[test]
fn family_payload_and_state_binders_do_not_leak_across_template_boundaries() {
    let valid = family_source();
    for (label, text) in [
        (
            "answer unavailable in family",
            valid.replace("Marker<Payload>,", "Marker<T>,"),
        ),
        (
            "payload unavailable in finish",
            valid.replace("NativeOps<R>.close state", "NativeOps<Payload>.close state"),
        ),
        (
            "family state unavailable in finish",
            valid.replace("close state", "close family_state"),
        ),
        (
            "family state unavailable in outer handler",
            valid.replace("NativeOps<R>.read state", "NativeOps<R>.read family_state"),
        ),
        (
            "payload unavailable after resource",
            // Free variables in a global annotation are fresh implicit binders.
            // Use an operation actual absent from the global's signature instead.
            format!(
                "{valid}after : Unit -> Int\nafter () = perform StorageNative<Payload, {{Mark}}, Int>.load (Token ())\n"
            ),
        ),
        (
            "family state unavailable after resource",
            format!("{valid}after : Unit -> Int\nafter () = family_state\n"),
        ),
        (
            "acquisition binder unavailable in family",
            valid.replace("load family_state", "load config"),
        ),
    ] {
        let source = Source::new(&text);
        let graph = load_module_graph(&source.0, &ModuleRoots::empty()).unwrap();
        match resolve_module(graph.modules().last().unwrap(), &[]) {
            Err(_) => {}
            Ok(_) => panic!("{label}: expected a resolution error"),
        }
    }
}

#[test]
fn unknown_family_requirements_associations_and_operations_reject_resolution() {
    let valid = family_source();
    for (from, to) in [
        ("where Marker<Payload>", "where MissingMarker<Payload>"),
        ("provider StorageProvider<", "provider MissingProvider<"),
        (
            "effect StorageOps<R, {Mark}, Payload>",
            "effect MissingOps<R, {Mark}, Payload>",
        ),
        ("interpret StorageNative<", "interpret MissingNative<"),
        ("load access =>", "missing access =>"),
    ] {
        let source = Source::new(&valid.replace(from, to));
        let graph = load_module_graph(&source.0, &ModuleRoots::empty()).unwrap();
        assert!(
            resolve_module(graph.modules().last().unwrap(), &[]).is_err(),
            "{to}"
        );
    }
}

#[test]
fn family_effect_actuals_preserve_existing_argument_kind_rejection() {
    let valid = family_source();
    let source = Source::new(&valid.replace(
        "effect StorageOps<R, {Mark}, Payload>",
        "effect StorageOps<R, Payload, {Mark}>",
    ));
    let graph = load_module_graph(&source.0, &ModuleRoots::empty()).unwrap();
    assert!(resolve_module(graph.modules().last().unwrap(), &[]).is_err());
}

#[test]
fn family_effect_arity_actuals_are_retained_until_the_checker_boundary() {
    let valid = family_source();
    for (from, to, provided_count, interpreted_count) in [
        (
            "effect StorageOps<R, {Mark}, Payload>",
            "effect StorageOps<R, {Mark}>",
            2,
            3,
        ),
        (
            "interpret StorageNative<Payload, {Mark}, R>",
            "interpret StorageNative<Payload, {Mark}, R, Int>",
            3,
            4,
        ),
    ] {
        let source = Source::new(&valid.replace(from, to));
        let graph = load_module_graph(&source.0, &ModuleRoots::empty()).unwrap();
        // Existing owner kind preflight leaves arity diagnostics to checking.
        // The carrier must retain every written actual instead of dropping it
        // or inventing an argument while this family remains non-executable.
        let module = resolve_module(graph.modules().last().unwrap(), &[]).unwrap();
        let family = module.resources()[0].family_template.as_ref().unwrap();
        assert_eq!(family.provided.instance.arguments().len(), provided_count);
        assert_eq!(
            family.interpreted.instance.arguments().len(),
            interpreted_count
        );
        assert!(ash::elaborate::check_module(module).is_err(), "{to}");
    }
}
