use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{
        transform::{fold_literal_primitives, identity_traversal},
        validate_modules,
    },
    elaborate::{Elaborator, check_module, link_modules},
    eval::{Value, evaluate},
    evidence_validation::validate_interface_evidence,
    interface::EvidenceNode,
    module::load_module_graph,
    resolve::resolve_module,
    resolved::{ResolvedDefinitionKind, ResolvedExprKind, ResolvedLocalDeclaration},
};
use ash::{
    driver::{RunConfiguration, run_path},
    module::ModuleRoots,
    types::Type,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new(text: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir()
                .join(format!("ash-scoped-evidence-{}-{id}", std::process::id()));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let path = directory.join("entry.ash");
                    fs::write(&path, text).expect("fixture should be writable");
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("fixture directory should be creatable: {error}"),
            }
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        if let Some(directory) = self.0.parent() {
            let _ = fs::remove_dir_all(directory);
        }
    }
}

fn pure_relation(call: &str) {
    let source = format!(
        r#"interface Read<A, B> where A -> B {{
    read : A -> B
}}

forward<A, B> : A -> B where Read<A, B>
forward value = read(value)

main : Unit -> Int
main () = {{
    newtype Token = Token(Int)
    let saved = Token(41)
    with Read<Token, Int> {{
        read ignored = match saved {{
            Token(value) => value + 1
        }}
    }}
    {call}(saved)
}}
"#
    );
    let fixture = Fixture::new(&source);
    let observation = run_path(RunConfiguration {
        entry: fixture.0.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect("scoped evidence should complete the modular pipeline");
    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.ty(), &Type::Int);

    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty()).expect("fixture should load");
    let resolved = resolve_module(&graph.modules()[0], &[]).expect("fixture should resolve");
    let checked = check_module(resolved).expect("fixture should check");
    let main = checked.definitions().last().expect("fixture declares main");
    let ResolvedDefinitionKind::Equational(main) = main.kind() else {
        panic!("main is equational")
    };
    let ResolvedExprKind::Block(block) = &main.equations[0].body.kind else {
        panic!("main owns a block")
    };
    let ResolvedLocalDeclaration::Evidence(source) = &block.declarations[2] else {
        panic!("third declaration supplies evidence")
    };
    let ResolvedExprKind::Apply(application) = &block.result.kind else {
        panic!("main calls a method or constrained function")
    };
    let ResolvedExprKind::Occurrence(occurrence) = &application.function.kind else {
        panic!("call has an occurrence")
    };
    let selection = occurrence.evidence[0]
        .selection()
        .expect("selection is retained");
    assert!(
        matches!(selection.node(selection.root()), Some(EvidenceNode::Lexical { source: selected, methods })
        if selected == source.id && methods == [source.method_groups[0].method.expect("supplied method is resolved")])
    );

    let linked = link_modules(vec![checked], graph.entry()).expect("fixture should link");
    let linked = validate_interface_evidence(linked)
        .expect("linked lexical selection should independently authenticate");
    let mut elaborator =
        Elaborator::for_module_program(&linked).expect("Core namespace should fit");
    let typed = elaborator
        .synthesize_module_program(&linked)
        .expect("ordinary method bindings should lower");
    let unchecked = elaborator.finish(typed.node).expect("Core should finish");
    let source = graph.modules()[0].source();
    let program = validate_modules(unchecked, &[source], &[(graph.entry(), source.id())])
        .expect("Core should independently authenticate lexical methods");
    let identity = identity_traversal(&program).expect("identity traversal should validate");
    let folded = fold_literal_primitives(&program).expect("folded Core should validate");
    let identity = validate_modules(identity, &[source], &[(graph.entry(), source.id())])
        .expect("identity Core should revalidate");
    let folded = validate_modules(folded, &[source], &[(graph.entry(), source.id())])
        .expect("folded Core should revalidate");
    for program in [program, identity, folded] {
        assert!(
            matches!(evaluate(&program).expect("ordinary method closure should execute").value, Value::Integer(value) if value.to_string() == "42")
        );
    }
}

#[test]
fn pure_lexical_method_executes() {
    pure_relation("read");
}

#[test]
fn pure_lexical_method_forwards_through_a_constraint() {
    pure_relation("forward");
}
