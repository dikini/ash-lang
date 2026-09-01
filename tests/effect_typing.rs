use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    elaborate::check_module,
    module::{ModuleRoots, load_module_graph},
    resolve::resolve_module,
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
    let fixture = TempModule::write(source);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("the effect typing fixture should load");
    let module = graph
        .modules()
        .iter()
        .find(|module| module.id() == graph.entry())
        .expect("the graph should retain its entry");
    let resolved = resolve_module(module, &[]).expect("the effect typing fixture should resolve");
    check_module(resolved).expect("the effect typing fixture should check")
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
    assert_eq!(forwarded.known()[0].arguments(), &[Type::Bool]);

    let delegated = latent_effects(&checked, "delegated");
    assert_eq!(delegated.known().len(), 1);
    assert_eq!(delegated.known()[0].arguments(), &[Type::Int]);

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

fn handler_source(clause_body: &str) -> String {
    format!(
        "effect Choice {{\nchoose : Unit -> Int\n}}\n\nmain : Unit -> Int\nmain () = handle (perform Choice.choose ()) with Choice {{\nchoose ignored => {clause_body}\n}}\n"
    )
}
