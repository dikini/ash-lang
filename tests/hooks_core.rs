use ash::{
    core::{
        transform::{fold_effect_literal_primitives, identity_effect_traversal},
        validate_effect_modules,
    },
    elaborate::{EffectElaborator, check_module, link_modules},
    eval::evaluate_effect,
    evidence_validation::validate_interface_evidence,
    module::{ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::CheckedModule,
    source::SourceFile,
};

fn transformed(source: &str, modules: &[(&str, &str)], expected: &str) {
    let directory = std::env::temp_dir().join(format!(
        "ash-hooks-core-{}-{}",
        std::process::id(),
        SourceFile::new("hook", "").unwrap().id().value()
    ));
    std::fs::create_dir(&directory).unwrap();
    for (name, text) in modules {
        std::fs::write(directory.join(name), text).unwrap();
    }
    let entry = directory.join("entry.ash");
    std::fs::write(&entry, source).unwrap();
    let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    std::fs::remove_dir_all(directory).unwrap();
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
    let relations = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let mut program = validate_effect_modules(core, &sources, &relations).unwrap();
    for pass in 0..3 {
        if pass > 0 {
            let core = if pass == 1 {
                identity_effect_traversal(&program)
            } else {
                fold_effect_literal_primitives(&program)
            }
            .unwrap();
            program = validate_effect_modules(core, &sources, &relations).unwrap();
        }
        assert_eq!(
            evaluate_effect(&program).unwrap().value.to_string(),
            expected
        );
    }
}

#[test]
fn identity_and_folding_preserve_unused_roots_and_enclosing_resume() {
    transformed(
        "effect Adjust {\npublish : Int -> Int\n}\nmain : Unit -> Bool\nmain () = hook Adjust {\ntrue\n}\n",
        &[],
        "true",
    );
    transformed(
        "effect Adjust {\npublish : Int -> Int\n}\neffect Ask {\nask : Unit -> Int\n}\nmain : Unit -> Int\nmain () = handle (perform Ask.ask ()) with Ask {\nask ignored => hook Adjust {\nresume (40 + 2)\n}\n}\n",
        &[],
        "42",
    );
}

#[test]
fn facade_generic_api_keeps_exact_root_and_request_instantiation() {
    for (argument, expected) in [("()", "3"), ("true", "13")] {
        transformed(
            &format!(
                "import facade (Mark, probe)\nmain : Unit -> Int\nmain () = handle (probe ((), {argument})) with Mark<Unit> {{\npublish input => resume (input + 10)\n}}\n"
            ),
            &[
                (
                    "api.ash",
                    "pub effect Mark<T> {\npublish : Int -> Int\n}\npub probe<T, U> : (T, U) -> Int ! {Mark<T>}\nprobe (first, second) = hook Mark<U> {\nperform Mark<T>.publish 3\n}\n",
                ),
                ("facade.ash", "pub import api (Mark, probe)\n"),
            ],
            expected,
        );
    }
}

#[test]
fn root_preserves_live_resource_function_payloads_through_transforms() {
    transformed(
        "import @builtin.cell as Cell\neffect Adjust {\npublish : (Unit -> Int) -> (Unit -> Int)\n}\nmain : Unit -> Int\nmain () = resource cell<R> c = 42 {\nlet get : Unit -> Int = fn(ignored) {\nhandle (Cell.read c) with Cell.Ops<R> {\nread value => resume 42\nwrite value => resume ()\n}\n}\nlet restored = hook Adjust {\nperform Adjust.publish get\n}\nrestored ()\n}\n",
        &[],
        "42",
    );
}

#[test]
fn imported_open_lacks_helper_preserves_its_least_root_row_after_transforms() {
    transformed(
        "import helper (Adjust, relay)\nconstant : Unit -> Int\nconstant () = 42\nmain : Unit -> Int\nmain () = hook Adjust {\nrelay constant\n}\n",
        &[(
            "helper.ash",
            "pub effect Adjust {\npublish : Int -> Int\n}\npub relay<R : EffectRow> : (Unit -> Int ! {| R}) -> Int ! {Adjust | R}\nrelay action = hook Adjust {\naction ()\n}\n",
        )],
        "42",
    );
}

#[test]
fn registration_order_and_generic_coincidence_execute_after_both_transforms() {
    transformed(
        "effect Adjust {\npublish : Int -> Int\n}\nmain : Unit -> Int\nmain () = hook Adjust {\nregister Adjust (fn(value) {\nvalue + 1\n}) {\nregister Adjust (fn(value) {\nvalue * 2\n}) {\nperform Adjust.publish 3\n}\n}\n}\n",
        &[],
        "8",
    );
    for (argument, expected) in [("()", "4"), ("true", "3")] {
        transformed(
            &format!(
                "import helper (Mark, probe)\nmain : Unit -> Int\nmain () = hook Mark<Unit> {{\nhook Mark<Bool> {{\nprobe ((), {argument})\n}}\n}}\n"
            ),
            &[(
                "helper.ash",
                "pub effect Mark<T> {\npublish : Int -> Int\n}\npub probe<T, U> : (T, U) -> Int ! {Mark<T>, Mark<U>}\nprobe ignored = register Mark<U> (fn(value) {\nvalue + 1\n}) {\nperform Mark<T>.publish 3\n}\n",
            )],
            expected,
        );
    }
}

#[test]
fn imported_opaque_callback_factory_executes_after_both_transforms() {
    transformed(
        "import facade (Adjust, make, Box, pack, unpack)\nconstant : Unit -> Int\nconstant ignored = 1\nsaved : Unit -> Int\nsaved ignored = 42\nmain : Unit -> Int\nmain () = hook Adjust {\nlet callback = unpack (pack (make saved))\nlet result = register Adjust callback {\nperform Adjust.publish constant\n}\nresult ()\n}\n",
        &[
            (
                "api.ash",
                "pub effect Adjust {\npublish : (Unit -> Int) -> (Unit -> Int)\n}\npub opaque type Box<A> = Hidden(A)\npub pack<A> : A -> Box<A>\npack value = Hidden value\npub unpack<A> : Box<A> -> A\nunpack (Hidden value) = value\npub make : (Unit -> Int) -> ((Unit -> Int) -> (Unit -> Int))\nmake saved = fn(previous) {\nsaved\n}\n",
            ),
            (
                "facade.ash",
                "pub import api (Adjust, make, Box, pack, unpack)\n",
            ),
        ],
        "42",
    );
}

#[test]
fn imported_evidence_method_factory_adds_a_live_resource_dependency_after_transforms() {
    transformed(
        "import @builtin.cell as Cell\nimport helper (Adjust, Read, read, Box, make, impl Make)\nconstant : Unit -> Int\nconstant ignored = 1\nmain : Unit -> Int\nmain () = resource cell<R> c = 42 {\nnewtype Token = Token(Unit)\nlet saved = Token(())\nwith Read<Token> {\nread ignored = handle (Cell.read c) with Cell.Ops<R> {\nread value => resume 42\nwrite value => resume ()\n}\n}\nhook Adjust {\nlet callback = make (Box saved)\nlet result = register Adjust callback {\nperform Adjust.publish constant\n}\nresult ()\n}\n}\n",
        &[(
            "helper.ash",
            "pub effect Adjust {\npublish : (Unit -> Int) -> (Unit -> Int)\n}\npub interface Read<A> {\nread : A -> Int\n}\npub type Box<A> = Box(A)\npub interface Make<A> {\nmake : A -> ((Unit -> Int) -> (Unit -> Int))\n}\npub impl<A> Make<Box<A>> where Read<A> {\nmake (Box saved) = fn(previous) {\nfn(ignored) {\nread saved\n}\n}\n}\n",
        )],
        "42",
    );
}

#[test]
fn registration_keeps_saved_generic_callback_type_and_row_context_after_transforms() {
    transformed(
        "import helper (Adjust, relay)\neffect Log {\nlog : Int -> Int\n}\ncallback : Int -> Int ! {Log}\ncallback value = perform Log.log (value + 1)\nmain : Unit -> Int\nmain () = handle (hook Adjust<Int> {\nrelay callback\n}) with Log {\nlog value => resume (value * 2)\n}\n",
        &[(
            "helper.ash",
            "pub effect Adjust<T> {\npublish : T -> T\n}\npub relay<R : EffectRow> : (Int -> Int ! {| R}) -> Int ! {Adjust<Int> | R}\nrelay callback = register Adjust<Int> callback {\nperform Adjust<Int>.publish 3\n}\n",
        )],
        "8",
    );
}

#[test]
fn registration_callback_adds_a_tuple_dependency_preserved_by_projection_and_transforms() {
    transformed(
        "import @builtin.cell as Cell\neffect Adjust {\npublish : (Int, Unit -> Int) -> (Int, Unit -> Int)\n}\nconstant : Unit -> Int\nconstant ignored = 1\nmain : Unit -> Int\nmain () = resource cell<R> c = 42 {\nlet callback : (Int, Unit -> Int) -> (Int, Unit -> Int) = fn(previous) {\nlet (number, old) = previous\nlet saved : Unit -> Int = fn(ignored) {\nlet held = c\n42\n}\n(number + 1, saved)\n}\nlet result = hook Adjust {\nregister Adjust callback {\nperform Adjust.publish (1, constant)\n}\n}\nlet (number, saved) = result\nnumber + saved ()\n}\n",
        &[],
        "44",
    );
}

#[test]
fn registration_generic_dependency_coincidence_executes_with_the_cell_live() {
    for (argument, expected) in [("()", "42"), ("true", "1")] {
        transformed(
            &format!(
                "import @builtin.cell as Cell\neffect Mark<T> {{\npublish : (Unit -> Int) -> (Unit -> Int)\n}}\nconstant : Unit -> Int\nconstant ignored = 1\nprobe<T, U> : (T, U, ((Unit -> Int) -> (Unit -> Int))) -> (Unit -> Int) ! {{Mark<T>, Mark<U>}}\nprobe (first, second, callback) = register Mark<U> callback {{\nperform Mark<T>.publish constant\n}}\nmain : Unit -> Int\nmain () = resource cell<R> c = 42 {{\nlet callback : (Unit -> Int) -> (Unit -> Int) = fn(previous) {{\nfn(ignored) {{\nlet held = c\n42\n}}\n}}\nlet result = hook Mark<Unit> {{\nhook Mark<Bool> {{\nprobe ((), {argument}, callback)\n}}\n}}\nresult ()\n}}\n"
            ),
            &[],
            expected,
        );
    }
}

#[test]
fn registration_generic_completion_coincidence_resumes_after_both_transforms() {
    for (argument, expected) in [("()", "4"), ("true", "3")] {
        transformed(
            &format!(
                "effect Mark<T> {{\npublish : Int -> Int\n}}\neffect Pause {{\nask : Int -> Int\n}}\nincrement : Int -> Int\nincrement value = value + 1\nprobe<T, U> : (T, U) -> Int ! {{Mark<T>, Mark<U>, Pause}}\nprobe ignored = register Mark<U> increment {{\nlet value = perform Mark<T>.publish 3\nperform Pause.ask value\n}}\nmain : Unit -> Int\nmain () = handle (hook Mark<Unit> {{\nhook Mark<Bool> {{\nprobe ((), {argument})\n}}\n}}) with Pause {{\nask value => resume value\n}}\n"
            ),
            &[],
            expected,
        );
    }
}

#[test]
fn registration_forwards_through_an_older_ordinary_exact_handler_after_transforms() {
    transformed(
        "effect Adjust {\npublish : Int -> Int\n}\nincrement : Int -> Int\nincrement value = value + 1\nmain : Unit -> Int\nmain () = handle (register Adjust increment {\nperform Adjust.publish 3\n}) with Adjust {\npublish value => resume (value * 10)\n}\n",
        &[],
        "31",
    );
}
