use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{PureComputation, PureExprKind, PureValue, validate_modules},
    elaborate::{Elaborator, TypeError, TypeReason, check_module, link_modules},
    eval::{Value, evaluate},
    evidence_validation::validate_interface_evidence,
    module::{ModuleRoots, load_module_graph},
    resolve::{ResolveModuleError, ResolveReason, resolve_module},
    resolved::{ResolvedDefinitionKind, ResolvedExprKind, ResolvedLocalDeclaration},
    types::{ConstructorId, NominalTypeId, Type},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new(text: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory =
                std::env::temp_dir().join(format!("ash-local-newtype-{}-{id}", std::process::id()));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let path = directory.join("entry.ash");
                    fs::write(&path, text).expect("local-newtype fixture should be writable");
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("local-newtype fixture should be creatable: {error}"),
            }
        }
    }

    fn resolve(&self) -> ash::resolved::ResolvedModule {
        let graph = load_module_graph(&self.0, &ModuleRoots::empty())
            .expect("local-newtype fixture should load");
        resolve_module(&graph.modules()[0], &[]).expect("local-newtype fixture should resolve")
    }
}

fn resolution_error(text: &str) -> ResolveReason {
    let fixture = Fixture::new(text);
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("rejected local-newtype fixture should load");
    match resolve_module(&graph.modules()[0], &[])
        .expect_err("local-newtype fixture should fail resolution")
    {
        ResolveModuleError::Resolution(error) => error.reason,
        ResolveModuleError::Kind(error) => {
            panic!("kind checking stole resolution ownership: {error:?}")
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

fn constructor_head(expression: &ash::resolved::ResolvedExpr) -> ConstructorId {
    let ResolvedExprKind::Apply(application) = &expression.kind else {
        panic!("expected constructor application")
    };
    let ResolvedExprKind::Constructor(constructor) = &application.function.kind else {
        panic!("expected constructor head")
    };
    constructor.constructor
}

fn annotated_nominal(binding: &ash::resolved::ResolvedBinding) -> NominalTypeId {
    let Some(annotation) = &binding.annotation else {
        panic!("expected binding annotation")
    };
    let Type::Nominal(nominal) = annotation.ty else {
        panic!("expected nominal annotation")
    };
    nominal
}

#[test]
fn identity_free_closure_may_capture_a_local_newtype() {
    let fixture = Fixture::new(concat!(
        "make : Unit -> (Unit -> Int)\n",
        "make () = {\n",
        "    newtype Offset = Offset(Int)\n",
        "    let offset = Offset(41)\n",
        "    fn(ignored) {\n",
        "        match offset {\n",
        "            Offset(value) => value + 1\n",
        "        }\n",
        "    }\n",
        "}\n\n",
        "main : Unit -> (Unit -> Int)\n",
        "main () = make()\n",
    ));
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty())
        .expect("identity-free closure fixture should load");
    let resolved = resolve_module(&graph.modules()[0], &[])
        .expect("identity-free closure fixture should resolve");
    let checked = check_module(resolved).expect("identity-free closure should check");
    let linked = link_modules(vec![checked], graph.entry()).expect("fixture should link");
    let linked = validate_interface_evidence(linked).expect("fixture evidence should validate");
    let mut elaborator =
        Elaborator::for_module_program(&linked).expect("fixture Core namespace should fit");
    let typed = elaborator
        .synthesize_module_program(&linked)
        .expect("identity-free closure should elaborate");
    let unchecked = elaborator
        .finish(typed.node)
        .expect("identity-free closure Core should finish");
    let source = graph.modules()[0].source();
    let program = validate_modules(unchecked, &[source], &[(graph.entry(), source.id())])
        .expect("identity-free closure Core should validate");

    let evaluation = evaluate(&program).expect("identity-free closure should execute");
    let Value::Function(closure) = evaluation.value else {
        panic!("main should return the identity-free closure")
    };
    assert_eq!(
        program.node(program.root()).unwrap().ty,
        Type::Function(Box::new(Type::Unit), Box::new(Type::Int))
    );
    assert!(
        closure.environment.len() >= 3,
        "the closure should retain its lexical environment"
    );

    let mut pending = vec![program.root()];
    let mut scopes = 0;
    let mut conversions = 0;
    let mut ordinary_constructors = 0;
    while let Some(node) = pending.pop() {
        let expression = program.node(node).expect("reachable Core node");
        match &expression.kind {
            PureExprKind::Value(PureValue::Constructor(_)) => ordinary_constructors += 1,
            PureExprKind::Computation(PureComputation::NewtypeConversion(_)) => conversions += 1,
            PureExprKind::Computation(PureComputation::LocalNominalScope(_)) => scopes += 1,
            _ => {}
        }
        pending
            .extend((0..expression.kind.child_count()).filter_map(|i| expression.kind.child_at(i)));
    }
    assert_eq!(scopes, 1);
    assert_eq!(conversions, 2);
    assert_eq!(ordinary_constructors, 0);
}

#[test]
fn direct_local_value_cannot_escape() {
    let resolved = Fixture::new(concat!(
        "main : Unit -> Int\n",
        "main () = {\n",
        "    let escaped = {\n",
        "        newtype Hidden = Hidden(Int)\n",
        "        Hidden(1)\n",
        "    }\n",
        "    0\n",
        "}\n",
    ))
    .resolve();
    let TypeError::Source(diagnostic) = check_module(resolved)
        .expect_err("the local nominal identity must not cross its lexical boundary")
    else {
        panic!("escape should be a source typing error")
    };
    assert_eq!(diagnostic.reason, TypeReason::LocalNominalEscape);
}

fn assert_local_escape(source: &str, case: usize) {
    let resolved = Fixture::new(source).resolve();
    let error = check_module(resolved)
        .expect_err("the local nominal identity must not cross its lexical boundary");
    let TypeError::Source(diagnostic) = error else {
        panic!("escape case {case} should be a source typing error: {error:?}")
    };
    assert_eq!(diagnostic.reason, TypeReason::LocalNominalEscape);
}

#[test]
fn local_nominal_escape_matrix_covers_nested_outward_types() {
    let prefix = "type Box<A> = Box(A)\n\neffect Read<A> {\nread : Unit -> A\n}\n\nmain : Unit -> Int\nmain () = {\n    let escaped = {\n        newtype Hidden = Hidden(Int)\n";
    let suffix = "\n    }\n    0\n}\n";
    let cases = [
        "        Hidden",
        "        (Hidden(1), 0)",
        "        Box(Hidden(1))",
        concat!(
            "        let expose : Hidden -> Int = fn(value) {\n",
            "            0\n",
            "        }\n",
            "        expose",
        ),
        concat!(
            "        let expose : Unit -> Hidden = fn(value) {\n",
            "            Hidden(1)\n",
            "        }\n",
            "        expose",
        ),
        concat!(
            "        let expose : Unit -> Unit ! {Read<Hidden>} = ",
            "fn(value) {\n",
            "            ()\n",
            "        }\n",
            "        expose",
        ),
        concat!(
            "        let project = fn((hidden, value)) {\n",
            "            match hidden {\n",
            "                Hidden(number) => value\n",
            "            }\n",
            "        }\n",
            "        project",
        ),
        concat!(
            "        let reveal : Hidden -> Int = fn(value) {\n",
            "            match value {\n",
            "                Hidden(number) => number\n",
            "            }\n",
            "        }\n",
            "        (Hidden(1), reveal)",
        ),
    ];
    for (index, case) in cases.into_iter().enumerate() {
        assert_local_escape(&format!("{prefix}{case}{suffix}"), index);
    }
}

#[test]
fn local_nominal_scope_accepts_identity_free_representation_and_polymorphic_results() {
    for body in [
        concat!(
            "        match Hidden(42) {\n",
            "            Hidden(value) => value\n",
            "        }",
        ),
        "        ignore(Hidden(1))",
    ] {
        let source = format!(
            "ignore<A> : A -> Int\nignore value = 42\n\nmain : Unit -> Int\nmain () = {{\n    let accepted = {{\n        newtype Hidden = Hidden(Int)\n{body}\n    }}\n    accepted\n}}\n"
        );
        let resolved = Fixture::new(&source).resolve();
        check_module(resolved).expect("identity-free outward type should be accepted");
    }
}

#[test]
fn deep_local_nominal_scopes_accept_and_reject_on_a_small_stack() {
    const DEPTH: usize = 4_096;

    std::thread::Builder::new()
        .name("deep-local-nominal-scopes".to_owned())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut declarations = String::new();
            for index in 0..DEPTH {
                declarations.push_str(&format!("        newtype N{index} = N{index}(Int)\n"));
            }

            let accepted = Fixture::new(&format!(
                "main : Unit -> Unit\nmain () = {{\n    let accepted = {{\n{declarations}        ()\n    }}\n    accepted\n}}\n"
            ));
            let graph = load_module_graph(&accepted.0, &ModuleRoots::empty())
                .expect("deep accepted fixture should load");
            let resolved = resolve_module(&graph.modules()[0], &[])
                .expect("deep accepted fixture should resolve");
            let checked = check_module(resolved).expect("deep identity-free result should check");
            let linked = link_modules(vec![checked], graph.entry()).expect("fixture should link");
            let linked =
                validate_interface_evidence(linked).expect("fixture evidence should validate");
            let mut elaborator =
                Elaborator::for_module_program(&linked).expect("deep Core namespace should fit");
            let typed = elaborator
                .synthesize_module_program(&linked)
                .expect("deep local scopes should elaborate iteratively");
            let unchecked = elaborator
                .finish(typed.node)
                .expect("deep local scope Core should finish");
            let source = graph.modules()[0].source();
            let program = validate_modules(unchecked, &[source], &[(graph.entry(), source.id())])
                .expect("deep local scopes should validate iteratively");
            let mut pending = vec![program.root()];
            let mut scopes = 0;
            while let Some(id) = pending.pop() {
                let node = program.node(id).expect("reachable deep Core node");
                if matches!(
                    node.kind,
                    PureExprKind::Computation(PureComputation::LocalNominalScope(_))
                ) {
                    scopes += 1;
                }
                pending.extend(
                    (0..node.kind.child_count()).filter_map(|index| node.kind.child_at(index)),
                );
            }
            assert_eq!(scopes, DEPTH);
            assert!(matches!(
                evaluate(&program).expect("deep local scopes should execute").value,
                Value::Unit
            ));

            let rejected = Fixture::new(&format!(
                "main : Unit -> Unit\nmain () = {{\n    let escaped = {{\n{declarations}        N{}(0)\n    }}\n    ()\n}}\n",
                DEPTH - 1,
            ));
            let error = check_module(rejected.resolve())
                .expect_err("the deep outward local identity must be rejected");
            let TypeError::Source(diagnostic) = error else {
                panic!("deep escape should remain a source typing error: {error:?}")
            };
            assert_eq!(diagnostic.reason, TypeReason::LocalNominalEscape);
        })
        .expect("the deep local-scope thread should start")
        .join()
        .expect("deep accepted and rejected local scopes must remain stack-safe");
}

#[test]
fn nested_shadowed_local_newtypes_keep_distinct_lexical_identities() {
    let resolved = Fixture::new(concat!(
        "newtype Shadow = Shadow(Int)\n\n",
        "main : Unit -> Unit\n",
        "main () = {\n",
        "    newtype Shadow = Shadow(Shadow)\n",
        "    let outer : Shadow = Shadow(1)\n",
        "    let nested = {\n",
        "        newtype Shadow = Shadow(Shadow)\n",
        "        let inner : Shadow = Shadow(2)\n",
        "        ()\n",
        "    }\n",
        "    let restored : Shadow = Shadow(3)\n",
        "    ()\n",
        "}\n\n",
        "after : Shadow -> Shadow\n",
        "after value = Shadow(value)\n",
    ))
    .resolve();

    let [module_nominal] = resolved.registry().nominals() else {
        panic!("expected one module nominal")
    };
    let [outer_nominal, inner_nominal] = resolved.registry().lexical_nominals() else {
        panic!("expected two lexical nominals")
    };
    assert!(!module_nominal.id.is_lexical());
    assert!(outer_nominal.id.is_lexical());
    assert!(inner_nominal.id.is_lexical());
    assert_ne!(module_nominal.id, outer_nominal.id);
    assert_ne!(outer_nominal.id, inner_nominal.id);
    assert_eq!(
        outer_nominal.representation,
        Some(Type::Nominal(module_nominal.id))
    );
    assert_eq!(
        inner_nominal.representation,
        Some(Type::Nominal(outer_nominal.id))
    );

    let [outer_constructor, inner_constructor] = resolved.registry().lexical_constructors() else {
        panic!("expected two lexical constructors")
    };
    assert_eq!(outer_constructor.owner, outer_nominal.id);
    assert_eq!(outer_constructor.id.owner(), outer_nominal.id);
    assert_eq!(inner_constructor.owner, inner_nominal.id);
    assert_eq!(inner_constructor.id.owner(), inner_nominal.id);

    let ResolvedDefinitionKind::Equational(main) = &resolved.definitions()[0].kind else {
        panic!("expected equational main")
    };
    let ResolvedExprKind::Block(block) = &main.equations[0].body.kind else {
        panic!("expected main block")
    };
    let ResolvedLocalDeclaration::Newtype(outer_owner) = block.declarations[0] else {
        panic!("expected outer local newtype marker")
    };
    assert_eq!(outer_owner, outer_nominal.id);
    let ResolvedLocalDeclaration::Binding(outer) = &block.declarations[1] else {
        panic!("expected outer binding")
    };
    assert_eq!(annotated_nominal(outer), outer_nominal.id);
    assert_eq!(constructor_head(&outer.initializer), outer_constructor.id);

    let ResolvedLocalDeclaration::Binding(nested) = &block.declarations[2] else {
        panic!("expected nested block binding")
    };
    let ResolvedExprKind::Block(nested_block) = &nested.initializer.kind else {
        panic!("expected nested block")
    };
    let ResolvedLocalDeclaration::Newtype(inner_owner) = nested_block.declarations[0] else {
        panic!("expected inner local newtype marker")
    };
    assert_eq!(inner_owner, inner_nominal.id);
    let ResolvedLocalDeclaration::Binding(inner) = &nested_block.declarations[1] else {
        panic!("expected inner binding")
    };
    assert_eq!(annotated_nominal(inner), inner_nominal.id);
    assert_eq!(constructor_head(&inner.initializer), inner_constructor.id);

    let ResolvedLocalDeclaration::Binding(restored) = &block.declarations[3] else {
        panic!("expected restored outer binding")
    };
    assert_eq!(annotated_nominal(restored), outer_nominal.id);
    assert_eq!(
        constructor_head(&restored.initializer),
        outer_constructor.id
    );

    let ResolvedDefinitionKind::Equational(after) = &resolved.definitions()[1].kind else {
        panic!("expected post-block definition")
    };
    let Type::Function(domain, codomain) = &after.interface.annotation.ty else {
        panic!("expected post-block function annotation")
    };
    assert_eq!(domain.as_ref(), &Type::Nominal(module_nominal.id));
    assert_eq!(codomain.as_ref(), &Type::Nominal(module_nominal.id));
    assert_eq!(
        constructor_head(&after.equations[0].body),
        resolved.registry().constructors()[0].id
    );
}

#[test]
fn sibling_local_newtypes_with_equal_shapes_have_distinct_identities() {
    let resolved = Fixture::new(concat!(
        "main : Unit -> Unit\n",
        "main () = {\n",
        "    let first = {\n",
        "        newtype Token = Token(Int)\n",
        "        ()\n",
        "    }\n",
        "    let second = {\n",
        "        newtype Token = Token(Int)\n",
        "        ()\n",
        "    }\n",
        "    ()\n",
        "}\n",
    ))
    .resolve();

    let [first, second] = resolved.registry().lexical_nominals() else {
        panic!("expected two sibling lexical facts")
    };
    assert_ne!(first.id, second.id);
    assert_eq!(first.spelling, "Token");
    assert_eq!(second.spelling, "Token");
    assert_eq!(first.representation, Some(Type::Int));
    assert_eq!(second.representation, Some(Type::Int));
}

#[test]
fn local_nominal_shadows_same_spelled_module_interface() {
    let resolved = Fixture::new(concat!(
        "interface Token<A> {\n",
        "    token : A -> A\n",
        "}\n\n",
        "main : Unit -> Unit\n",
        "main () = {\n",
        "    newtype Token = Token(Int)\n",
        "    let local : Token = Token(1)\n",
        "    ()\n",
        "}\n",
    ))
    .resolve();

    let [local] = resolved.registry().lexical_nominals() else {
        panic!("expected one lexical nominal")
    };
    let ResolvedDefinitionKind::Equational(main) = &resolved.definitions()[0].kind else {
        panic!("expected equational main")
    };
    let ResolvedExprKind::Block(block) = &main.equations[0].body.kind else {
        panic!("expected main block")
    };
    let ResolvedLocalDeclaration::Binding(binding) = &block.declarations[1] else {
        panic!("expected binding after local newtype")
    };
    assert_eq!(annotated_nominal(binding), local.id);
}

#[test]
fn local_newtype_visibility_is_strictly_sequential() {
    assert_eq!(
        resolution_error(concat!(
            "main : Unit -> Unit\n",
            "main () = {\n",
            "    newtype SelfRef = SelfRef(SelfRef)\n",
            "    ()\n",
            "}\n",
        )),
        ResolveReason::UnknownType,
    );
    assert_eq!(
        resolution_error(concat!(
            "main : Unit -> Unit\n",
            "main () = {\n",
            "    newtype First = First(Second)\n",
            "    newtype Second = Second(Int)\n",
            "    ()\n",
            "}\n",
        )),
        ResolveReason::UnknownType,
    );
    assert_eq!(
        resolution_error(concat!(
            "main : Unit -> Unit\n",
            "main () = {\n",
            "    let nested = {\n",
            "        newtype Hidden = Hidden(Int)\n",
            "        ()\n",
            "    }\n",
            "    let escaped : Hidden = 1\n",
            "    ()\n",
            "}\n",
        )),
        ResolveReason::UnknownType,
    );
    assert_eq!(
        resolution_error(concat!(
            "main : Unit -> Unit\n",
            "main () = {\n",
            "    let nested = {\n",
            "        newtype Hidden = Hidden(Int)\n",
            "        ()\n",
            "    }\n",
            "    let escaped = Hidden(1)\n",
            "    ()\n",
            "}\n",
        )),
        ResolveReason::UnknownConstructor,
    );
}

#[test]
fn following_recursive_group_uses_local_nominal_without_absorbing_declaration() {
    let resolved = Fixture::new(concat!(
        "main : Unit -> Unit\n",
        "main () = {\n",
        "    newtype Cell = Cell(Int)\n",
        "    let rec loop : Cell -> Cell = fn(value) {\n",
        "        value\n",
        "    }\n",
        "    ()\n",
        "}\n",
    ))
    .resolve();
    let owner = resolved.registry().lexical_nominals()[0].id;
    let ResolvedDefinitionKind::Equational(main) = &resolved.definitions()[0].kind else {
        panic!("expected equational main")
    };
    let ResolvedExprKind::Block(block) = &main.equations[0].body.kind else {
        panic!("expected main block")
    };
    assert!(matches!(block.declarations[0], ResolvedLocalDeclaration::Newtype(id) if id == owner));
    let ResolvedLocalDeclaration::Recursive(group) = &block.declarations[1] else {
        panic!("expected following recursive group")
    };
    let [member] = group.members.as_slice() else {
        panic!("the newtype must not become a recursive member")
    };
    assert_eq!(
        member.annotation.ty,
        Type::Function(
            Box::new(Type::Nominal(owner)),
            Box::new(Type::Nominal(owner)),
        )
    );
}

#[test]
fn local_facts_do_not_enter_module_or_export_partitions() {
    let resolved = Fixture::new(concat!(
        "pub newtype Visible = Visible(Int)\n\n",
        "main : Unit -> Unit\n",
        "main () = {\n",
        "    newtype Hidden = Hidden(Visible)\n",
        "    ()\n",
        "}\n",
    ))
    .resolve();
    let [local] = resolved.registry().lexical_nominals() else {
        panic!("expected one lexical nominal")
    };

    assert_eq!(resolved.registry().nominals().len(), 1);
    assert_eq!(resolved.registry().constructors().len(), 1);
    assert!(resolved.export_candidate().nominal("Visible").is_some());
    assert!(resolved.export_candidate().constructor("Visible").is_some());
    assert!(resolved.export_candidate().nominal("Hidden").is_none());
    assert!(resolved.export_candidate().constructor("Hidden").is_none());
    assert!(
        resolved
            .export_candidate()
            .hidden_nominal(local.id)
            .is_none()
    );
    assert!(!resolved.export_candidate().is_private("Hidden"));
    assert!(resolved.imported_facts().nominal(local.id).is_none());
    assert!(
        resolved
            .imported_facts()
            .constructor(resolved.registry().lexical_constructors()[0].id)
            .is_none()
    );
}
