use ash::{
    elaborate::{TypeError, check_module},
    module::{ModuleRoots, load_module_graph},
    presentation::{compile_type_diagnostic, write_json},
    resolve::{DependencyExports, resolve_module},
};

#[test]
fn json_keeps_named_type_facts_and_semantic_label_relationships() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/first-stratum/type/binding-initializer.ash");
    let graph = load_module_graph(&path, &ModuleRoots::empty()).unwrap();
    let loaded = graph
        .modules()
        .iter()
        .find(|m| m.id() == graph.entry())
        .unwrap();
    let TypeError::Source(error) = check_module(resolve_entry(&graph)).unwrap_err() else {
        panic!("expected a structured type diagnostic");
    };
    let view = compile_type_diagnostic(&error, &[loaded.source()]).unwrap();
    let mut output = Vec::new();
    write_json(&mut output, &view).unwrap();
    assert_eq!(output.iter().filter(|&&b| b == b'\n').count(), 1);
    let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(
        json,
        serde_json::json!({
            "schema_version": 1,
            "reason": "type.binding-initializer",
            "responsibility": "source",
            "facts": [
                {"name": "expected", "kind": "code", "value": "Bool"},
                {"name": "found", "kind": "code", "value": "Int"}
            ],
            "labels": [
                {"role": "primary", "relationship": "initializer", "path": loaded.source().display_path(),
                 "byte_start": error.primary.span().range().start(), "byte_end": error.primary.span().range().end(),
                 "facts": [{"name": "found", "kind": "code", "value": "Int"}]},
                {"role": "related", "relationship": "binding_annotation", "path": loaded.source().display_path(),
                 "byte_start": error.related[0].span().range().start(), "byte_end": error.related[0].span().range().end(),
                 "facts": [{"name": "expected", "kind": "code", "value": "Bool"}]}
            ]
        })
    );
}

fn resolve_entry(graph: &ash::module::ModuleGraph) -> ash::resolved::ResolvedModule {
    let mut checked = Vec::<ash::resolved::CheckedModule>::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|checked| checked.module() == edge.target())
                    .expect("dependencies precede their importer");
                DependencyExports::new(edge, dependency.exports())
                    .expect("the actual target authenticates its edge")
            })
            .collect::<Vec<_>>();
        let resolved =
            resolve_module(module, &dependencies).expect("the diagnostic fixture resolves");
        if module.id() == graph.entry() {
            return resolved;
        }
        checked.push(check_module(resolved).expect("diagnostic dependencies check"));
    }
    panic!("the graph retains its entry");
}
