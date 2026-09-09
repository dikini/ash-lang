use ash::{
    elaborate::{TypeError, check_module},
    message::{Catalogue, Locale},
    module::{ModuleRoots, load_module_graph},
    presentation::{compile_type_diagnostic, write_human, write_short},
    resolve::resolve_module,
};

#[test]
fn real_binding_error_keeps_initializer_and_annotation_context() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/first-stratum/type/binding-initializer.ash");
    let graph = load_module_graph(&path, &ModuleRoots::empty()).unwrap();
    let loaded = graph
        .modules()
        .iter()
        .find(|m| m.id() == graph.entry())
        .unwrap();
    let resolved = resolve_module(loaded, &[]).unwrap();
    let TypeError::Source(error) = check_module(resolved).unwrap_err() else {
        panic!("expected a structured type diagnostic");
    };
    let view = compile_type_diagnostic(&error, &[loaded.source()]).unwrap();
    let mut human = Vec::new();
    let catalogue = Catalogue::new(Locale::English).unwrap();
    write_human(&mut human, &view, &catalogue).unwrap();
    let human = String::from_utf8(human).unwrap();
    assert!(human.starts_with(
        "This binding needs a value of type `Bool`, but its initializer has type `Int`.\n"
    ));
    let path = loaded.source().display_path();
    assert_eq!(
        human,
        format!(
            "This binding needs a value of type `Bool`, but its initializer has type `Int`.\n  --> {path}:3:24\n3 |     let value : Bool = 1\n  | {}^ This initializer has type `Int`.\n  --> {path}:3:17\n3 |     let value : Bool = 1\n  | {}^ This annotation requires type `Bool`.\nreason: type.binding-initializer\n",
            " ".repeat(23),
            " ".repeat(16),
        )
    );
    let mut short = Vec::new();
    write_short(&mut short, &view, &catalogue).unwrap();
    let short = String::from_utf8(short).unwrap();
    assert_eq!(
        short,
        format!(
            "{path}:3:24: This binding needs a value of type `Bool`, but its initializer has type `Int`. [type.binding-initializer]\n"
        )
    );

    let mut bulgarian = Vec::new();
    write_human(
        &mut bulgarian,
        &view,
        &Catalogue::new(Locale::Bulgarian).unwrap(),
    )
    .unwrap();
    assert_eq!(
        String::from_utf8(bulgarian).unwrap(),
        format!(
            "Тази променлива изисква стойност от тип `Bool`, но началният израз има тип `Int`.\n  --> {path}:3:24\n3 |     let value : Bool = 1\n  | {}^ Този начален израз има тип `Int`.\n  --> {path}:3:17\n3 |     let value : Bool = 1\n  | {}^ Тази анотация изисква тип `Bool`.\nreason: type.binding-initializer\n",
            " ".repeat(23),
            " ".repeat(16),
        )
    );
    let mut short_bg = Vec::new();
    write_short(
        &mut short_bg,
        &view,
        &Catalogue::new(Locale::Bulgarian).unwrap(),
    )
    .unwrap();
    assert_eq!(
        String::from_utf8(short_bg).unwrap(),
        format!(
            "{path}:3:24: Тази променлива изисква стойност от тип `Bool`, но началният израз има тип `Int`. [type.binding-initializer]\n"
        )
    );
}
