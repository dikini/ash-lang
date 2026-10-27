use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{
        EffectExprKind, EffectOperation, PureComputation, PureExprKind,
        transform::{fold_effect_literal_primitives, identity_effect_traversal},
        validate_effect_modules,
    },
    elaborate::{EffectElaborator, check_module, link_modules},
    eval::{Value, evaluate_effect},
    evidence_validation::validate_interface_evidence,
    interface::EvidenceNode,
    module::load_module_graph,
    resolve::{DependencyExports, resolve_module},
    resolved::{
        CheckedModule, ResolvedDefinitionKind, ResolvedExprKind, ResolvedLocalDeclaration,
        ResolvedPatternKind,
    },
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
    let mut modules = Vec::<CheckedModule>::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let target = modules
                    .iter()
                    .find(|checked| checked.module() == edge.target())
                    .expect("the actual dependency should check first");
                DependencyExports::new(edge, target.exports())
                    .expect("the summary should match its edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies).expect("fixture should resolve");
        modules.push(check_module(resolved).expect("fixture should check"));
    }
    let checked = modules
        .iter()
        .find(|module| module.module() == graph.entry())
        .expect("the exact entry should be checked");
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

    let ResolvedLocalDeclaration::Newtype(token) = block.declarations[0] else {
        panic!("the first declaration owns Token")
    };
    let ResolvedLocalDeclaration::Binding(saved) = &block.declarations[1] else {
        panic!("the second declaration saves a Token")
    };
    let ResolvedPatternKind::Binder(saved) = &saved.pattern.kind else {
        panic!("saved has its own lexical binder")
    };
    let saved = saved.id;
    let method_binder = source.method_groups[0].binder.id;
    let linked = link_modules(modules, graph.entry()).expect("fixture should link");
    let linked = validate_interface_evidence(linked)
        .expect("linked lexical selection should independently authenticate");
    let mut elaborator =
        EffectElaborator::for_module_program(&linked).expect("Core namespace should fit");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("ordinary method bindings should lower");
    let unchecked = elaborator.finish(typed.node).expect("Core should finish");
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let relation = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let program = validate_effect_modules(unchecked, &sources, &relation)
        .expect("Core should independently authenticate lexical methods");
    let identity = identity_effect_traversal(&program).expect("identity traversal should validate");
    let folded = fold_effect_literal_primitives(&program).expect("folded Core should validate");
    let identity = validate_effect_modules(identity, &sources, &relation)
        .expect("identity Core should revalidate");
    let folded = validate_effect_modules(folded, &sources, &relation)
        .expect("folded Core should revalidate");
    for program in [program, identity, folded] {
        let mut pending = vec![program.root()];
        let mut method_initializer = None;
        let mut saved_type = None;
        let mut token_scopes = 0;
        while let Some(id) = pending.pop() {
            let node = program.node(id).unwrap();
            match &node.kind {
                EffectExprKind::Pure(PureExprKind::Computation(PureComputation::Bind(binding))) => {
                    if binding.binder().id() == method_binder {
                        assert!(method_initializer.replace(binding.initializer()).is_none());
                    }
                    if binding.binder().id() == saved {
                        saved_type = Some(binding.binder().ty().clone());
                    }
                }
                EffectExprKind::Pure(PureExprKind::Computation(
                    PureComputation::LocalNominalScope(scope),
                )) if scope.owner() == token => token_scopes += 1,
                _ => {}
            }
            pending.extend((0..node.kind.child_count()).filter_map(|i| node.kind.child_at(i)));
        }
        assert_eq!(token_scopes, 1);
        assert_eq!(saved_type, Some(Type::Nominal(token)));
        let mut pending =
            vec![method_initializer.expect("the exact lexical method retains its binding")];
        let mut captures_saved = 0;
        while let Some(id) = pending.pop() {
            let node = program.node(id).unwrap();
            if matches!(
                node.kind,
                EffectExprKind::Operation(EffectOperation::RegionClosure(_))
            ) {
                let captures = (0..node.kind.child_count()).filter_map(|i| node.kind.child_at(i))
                    .filter(|id| matches!(program.node(*id).unwrap().kind,
                        EffectExprKind::Pure(PureExprKind::Variable(variable)) if variable.binder() == saved))
                    .collect::<Vec<_>>();
                for capture in captures {
                    assert_eq!(program.node(capture).unwrap().ty, Type::Nominal(token));
                    captures_saved += 1;
                }
            }
            pending.extend((0..node.kind.child_count()).filter_map(|i| node.kind.child_at(i)));
        }
        assert_eq!(
            captures_saved, 1,
            "the lexical method record retains the exact saved Token"
        );
        assert!(
            matches!(evaluate_effect(&program).expect("ordinary method closure should execute").value, Value::SmallInteger(value) if value.to_string() == "42")
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
