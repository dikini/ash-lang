use std::{
    cell::RefCell,
    fs,
    path::{Path, PathBuf},
    rc::Rc,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::validate_effect_modules,
    elaborate::{EffectElaborator, TypeError, TypeReason, check_module, link_modules},
    eval::{Value, evaluate_effect},
    evidence_validation::validate_interface_evidence,
    module::{LoadedModule, ModuleGraph, ModuleId, ModuleRoots, load_module_graph},
    resolve::{DependencyExports, ResolveModuleError, ResolveReason, resolve_module},
    resolved::{CheckedModule, ImportedTypeAccess, ResolvedModule, ResolvedNominalDeclarationKind},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct ModuleTree(PathBuf, RefCell<Vec<(ModuleId, Rc<Vec<CheckedModule>>)>>);

impl ModuleTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-module-newtypes-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path, RefCell::new(Vec::new())),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("fixture tree should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, source: &str) -> PathBuf {
        let path = self.0.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("fixture parent should be creatable");
        }
        fs::write(&path, source).expect("fixture source should be writable");
        path
    }

    fn implicit_services(&self, graph: &ModuleGraph) -> Rc<Vec<CheckedModule>> {
        if let Some((_, services)) = self
            .1
            .borrow()
            .iter()
            .find(|(entry, _)| *entry == graph.entry())
        {
            return Rc::clone(services);
        }
        let mut services = Vec::<CheckedModule>::new();
        for module in graph.modules().iter().filter(|module| {
            matches!(
                module.canonical_path().to_str(),
                Some("@builtin.foreign" | "@compiler.region")
            )
        }) {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    let service = services
                        .iter()
                        .find(|service| service.module() == edge.target())
                        .expect("implicit services must be dependency ordered");
                    DependencyExports::new(edge, service.exports())
                        .expect("the actual implicit edge matches its export")
                })
                .collect::<Vec<_>>();
            let resolved =
                resolve_module(module, &dependencies).expect("the implicit service should resolve");
            services.push(check_module(resolved).expect("the implicit service should check"));
        }
        let services = Rc::new(services);
        self.1
            .borrow_mut()
            .push((graph.entry(), Rc::clone(&services)));
        services
    }

    fn take_implicit_services(&self, graph: &ModuleGraph) -> Vec<CheckedModule> {
        let index = self
            .1
            .borrow()
            .iter()
            .position(|(entry, _)| *entry == graph.entry())
            .expect("the implicit services should have been checked");
        let (_, services) = self.1.borrow_mut().remove(index);
        Rc::try_unwrap(services).expect("no implicit service borrow should outlive resolution")
    }
}

impl Drop for ModuleTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn module_named<'a>(graph: &'a ModuleGraph, file_name: &str) -> &'a LoadedModule {
    graph
        .modules()
        .iter()
        .find(|module| {
            Path::new(module.source().display_path()).file_name() == Some(file_name.as_ref())
        })
        .expect("fixture module should be present")
}

fn resolve_fixture(
    tree: &ModuleTree,
    graph: &ModuleGraph,
    target: &LoadedModule,
    retained: &[&CheckedModule],
) -> Result<ResolvedModule, ResolveModuleError> {
    let implicit = tree.implicit_services(graph);
    let mut checked = Vec::new();
    for module in graph.modules() {
        if implicit
            .iter()
            .any(|service| service.module() == module.id())
        {
            continue;
        }
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let summary = retained
                    .iter()
                    .copied()
                    .find(|checked| checked.module() == edge.target())
                    .map(CheckedModule::exports)
                    .or_else(|| {
                        implicit
                            .iter()
                            .find(|service| service.module() == edge.target())
                            .map(CheckedModule::exports)
                    })
                    .or_else(|| {
                        checked
                            .iter()
                            .find(|checked: &&CheckedModule| checked.module() == edge.target())
                            .map(|checked| checked.exports())
                    })
                    .expect("each exact dependency target must precede its importer");
                DependencyExports::new(edge, summary)
                    .expect("the original summary authenticates its actual target edge")
            })
            .collect::<Vec<_>>();
        let resolved = resolve_module(module, &dependencies);
        if module.id() == target.id() {
            return resolved;
        }
        checked.push(
            check_module(resolved.expect("preceding fixture modules resolve"))
                .expect("preceding fixture modules check"),
        );
    }
    panic!("the actual target remains in the graph");
}

#[test]
fn opaque_newtype_named_and_scheme_routes_merge_without_exposing_constructors() {
    for declaration in ["pub opaque newtype", "pub opaque type", "pub newtype"] {
        for import in [
            "import tickets as Tickets",
            "import tickets (Ticket, issue)",
            "import tickets (issue, Ticket)",
            "import facade (Ticket, issue)",
            "import reverse (issue, Ticket)",
            "import facade as Tickets",
            "import names (Ticket)\nimport operations (issue)",
            "import operations (issue)\nimport names (Ticket)",
            "import tickets as Tickets\nimport facade as Facade",
            "import tickets (Ticket, Envelope, issue)",
            "import tickets (Envelope, Ticket, issue)",
            "import tickets as Tickets\nimport envelopes as Envelopes",
        ] {
            let tree = ModuleTree::create();
            tree.write("tickets.ash", &format!(
                "{declaration} Ticket = Ticket(Int)\npub issue : Int -> Ticket\nissue value = Ticket(value)\npub type Envelope = Envelope(Ticket)\n"
            ));
            tree.write("facade.ash", "pub import tickets (Ticket, issue)\n");
            tree.write("reverse.ash", "pub import tickets (issue, Ticket)\n");
            tree.write("names.ash", "pub import tickets (Ticket)\n");
            tree.write("operations.ash", "pub import tickets (issue)\n");
            tree.write("envelopes.ash", "pub import tickets (Envelope)\n");
            for call in [false, true] {
                let expression = if !call {
                    "42"
                } else if import.contains("as Tickets") {
                    "{\nlet ignored = Tickets.issue 42\n42\n}"
                } else {
                    "{\nlet ignored = issue 42\n42\n}"
                };
                let entry = tree.write(
                    "entry.ash",
                    &format!("{import}\nmain : Unit -> Int\nmain () = {expression}\n"),
                );
                let output = std::process::Command::new(env!("CARGO_BIN_EXE_ash"))
                    .arg(&entry)
                    .output()
                    .unwrap();
                assert!(
                    output.status.success(),
                    "{declaration}, {import}, call={call}: {}",
                    String::from_utf8_lossy(&output.stderr)
                );
                assert_eq!(output.stdout, b"42 : Int\n");
                assert!(output.stderr.is_empty());
            }
        }
    }
}

#[test]
fn opaque_newtype_combined_import_keeps_constructor_rejection_source_owned() {
    for import in [
        "import tickets (Ticket, issue)",
        "import tickets (issue, Ticket)",
        "import facade (Ticket, issue)",
        "import tickets as Tickets",
    ] {
        let tree = ModuleTree::create();
        tree.write("tickets.ash", "pub opaque newtype Ticket = Ticket(Int)\npub issue : Int -> Ticket\nissue value = Ticket(value)\n");
        tree.write("facade.ash", "pub import tickets (Ticket, issue)\n");
        let constructor = if import.contains("as Tickets") {
            "Tickets.Ticket"
        } else {
            "Ticket"
        };
        let entry = tree.write("entry.ash", &format!("{import}\nmain : Unit -> Int\nmain () = {{\nlet ignored = {constructor}(42)\n42\n}}\n"));
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_ash"))
            .args(["--message-format", "json"])
            .arg(&entry)
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some(1),
            "{import}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stdout.is_empty());
        let diagnostic: serde_json::Value = serde_json::from_slice(&output.stderr).unwrap();
        assert_eq!(diagnostic["reason"], "resolve.opaque-constructor");
        assert_eq!(diagnostic["responsibility"], "source");
        let human = std::process::Command::new(env!("CARGO_BIN_EXE_ash"))
            .args(["--message-format", "human", "--locale", "en"])
            .arg(&entry)
            .output()
            .unwrap();
        assert_eq!(human.status.code(), Some(1));
        assert!(human.stdout.is_empty());
        let message = String::from_utf8(human.stderr).unwrap();
        assert!(message.contains(
            "The constructor `Ticket` belongs to an opaque type and is not accessible here."
        ));
        assert!(message.contains("The inaccessible declaration is here."));
        assert!(message.contains("reason: resolve.opaque-constructor"));
        assert!(!message.contains("resolve.internal-state"));
    }
}

#[test]
fn module_newtype_identity_survives_facade_reexport() {
    let tree = ModuleTree::create();
    let entry = tree.write("entry.ash", "import facade (UserId)\n");
    tree.write("base.ash", "pub newtype UserId = UserId(Int)\n");
    tree.write("facade.ash", "pub import base (UserId)\n");
    let graph =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture module graph should load");

    let base = module_named(&graph, "base.ash");
    let base = resolve_fixture(&tree, &graph, base, &[]).expect("base should resolve");
    let [base_nominal] = base.registry().nominals() else {
        panic!("base should declare one nominal");
    };
    let defining_id = base_nominal.id;
    let [defining_constructor] = base_nominal.constructors.as_ref() else {
        panic!("base should declare one constructor");
    };
    let defining_constructor = *defining_constructor;
    assert_eq!(
        base_nominal.declaration_kind,
        ResolvedNominalDeclarationKind::Newtype
    );
    assert_eq!(
        base_nominal.representation.as_ref(),
        Some(&ash::types::Type::Int)
    );
    let base = check_module(base).expect("base should check");

    let facade = module_named(&graph, "facade.ash");
    assert_eq!(
        facade
            .dependencies()
            .iter()
            .filter(|edge| edge.target() == base.module())
            .count(),
        1
    );
    let facade = resolve_fixture(&tree, &graph, facade, &[&base]).expect("facade should resolve");
    let facade = check_module(facade).expect("facade should check");

    let entry = module_named(&graph, "entry.ash");
    assert_eq!(
        entry
            .dependencies()
            .iter()
            .filter(|edge| edge.target() == facade.module())
            .count(),
        1
    );
    let entry = resolve_fixture(&tree, &graph, entry, &[&facade]).expect("entry should resolve");

    let imported = entry
        .imported_facts()
        .nominal(defining_id)
        .expect("facade import should retain the defining nominal fact");
    assert_eq!(
        imported.declaration_kind,
        ResolvedNominalDeclarationKind::Newtype
    );
    assert_eq!(imported.access, ImportedTypeAccess::Transparent);
    assert_eq!(imported.parameters.len(), 0);
    assert_eq!(imported.constructors.as_ref(), &[defining_constructor]);
    assert_eq!(
        imported.representation.as_ref(),
        Some(&ash::types::Type::Int)
    );
    let constructor = entry
        .imported_facts()
        .constructor(defining_constructor)
        .expect("transparent newtype import should retain its constructor projection");
    assert_eq!(constructor.payload.as_ref(), Some(&ash::types::Type::Int));
}

#[test]
fn module_opaque_newtype_keeps_its_representation_only_for_facade_linkage() {
    let tree = ModuleTree::create();
    let entry = tree.write("entry.ash", "import facade (Token)\n");
    tree.write("base.ash", "pub opaque newtype Token = Token(Int)\n");
    tree.write("facade.ash", "pub import base (Token)\n");
    let graph =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture module graph should load");

    let base = resolve_fixture(&tree, &graph, module_named(&graph, "base.ash"), &[])
        .expect("base should resolve");
    let defining_id = base
        .registry()
        .nominals()
        .first()
        .expect("base should declare Token")
        .id;
    let base = check_module(base).expect("base should check");
    let facade = check_module(
        resolve_fixture(&tree, &graph, module_named(&graph, "facade.ash"), &[&base])
            .expect("facade should resolve"),
    )
    .expect("facade should check");
    let entry = resolve_fixture(&tree, &graph, module_named(&graph, "entry.ash"), &[&facade])
        .expect("opaque facade import should resolve");

    let imported = entry
        .imported_facts()
        .nominal(defining_id)
        .expect("entry should retain the opaque nominal");
    assert_eq!(imported.access, ImportedTypeAccess::Opaque);
    assert!(imported.representation.is_none());
    assert!(imported.constructors.is_empty());
}

#[test]
fn opaque_newtype_constructor_is_inaccessible_in_expressions_and_patterns() {
    for entry_text in [
        concat!(
            "import base (Token)\n",
            "main : Unit -> Token\n",
            "main () = Token(1)\n",
        ),
        concat!(
            "import base (Token)\n",
            "read : Token -> Int\n",
            "read (Token(value)) = value\n",
        ),
    ] {
        let tree = ModuleTree::create();
        let entry = tree.write("entry.ash", entry_text);
        tree.write("base.ash", "pub opaque newtype Token = Token(Int)\n");
        let graph = load_module_graph(&entry, &ModuleRoots::empty())
            .expect("opaque constructor module graph should load");
        let base = check_module(
            resolve_fixture(&tree, &graph, module_named(&graph, "base.ash"), &[])
                .expect("opaque defining module should resolve"),
        )
        .expect("opaque defining module should check");
        let entry_module = module_named(&graph, "entry.ash");
        let ResolveModuleError::Resolution(error) =
            resolve_fixture(&tree, &graph, entry_module, &[&base])
                .expect_err("an opaque newtype constructor should be inaccessible")
        else {
            panic!("opaque constructor access should fail during resolution");
        };
        assert_eq!(error.reason, ResolveReason::OpaqueConstructor);
    }
}

#[test]
fn module_newtype_constructor_must_repeat_its_nominal_spelling() {
    let tree = ModuleTree::create();
    let text = "newtype UserId = OtherId(Int)\n";
    let entry = tree.write("entry.ash", text);
    let graph =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture module graph should load");

    let error = resolve_fixture(&tree, &graph, module_named(&graph, "entry.ash"), &[])
        .expect_err("a differently named newtype constructor should fail resolution");
    let ResolveModuleError::Resolution(error) = error else {
        panic!("newtype constructor spelling should fail in resolution");
    };
    assert_eq!(error.reason, ResolveReason::NewtypeConstructorName);
    assert!(
        error
            .to_string()
            .starts_with("resolve.newtype-constructor-name\n")
    );
    assert_eq!(error.related.len(), 1);
    assert_eq!(
        error.primary.span().range().start(),
        u32::try_from(text.find("OtherId").expect("fixture contains constructor"))
            .expect("fixture offset fits")
    );
    assert_eq!(
        error.related[0].span().range().start(),
        u32::try_from(text.find("UserId").expect("fixture contains nominal"))
            .expect("fixture offset fits")
    );
}

#[test]
fn module_newtype_representation_cycle_is_rejected_after_kinding() {
    let tree = ModuleTree::create();
    let entry = tree.write("entry.ash", "newtype UserId = UserId(UserId)\n");
    let graph =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture module graph should load");

    let ResolveModuleError::Representation(TypeError::Source(error)) =
        resolve_fixture(&tree, &graph, module_named(&graph, "entry.ash"), &[])
            .expect_err("kind-correct representation cycles must reject before remaining kinds")
    else {
        panic!("representation recursion belongs to module checking");
    };
    assert_eq!(error.reason, TypeReason::NewtypeRecursiveRepresentation);
}

#[test]
fn module_newtype_cycle_primary_is_the_first_closing_representation_occurrence() {
    let text = "newtype Left = Left(Right)\nnewtype Right = Right((Int, Left))\n";
    let tree = ModuleTree::create();
    let entry = tree.write("entry.ash", text);
    let graph =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture module graph should load");
    let ResolveModuleError::Representation(TypeError::Source(error)) =
        resolve_fixture(&tree, &graph, module_named(&graph, "entry.ash"), &[])
            .expect_err("the mutual representation cycle should be rejected")
    else {
        panic!("the representation cycle should retain a source diagnostic");
    };
    assert_eq!(error.reason, TypeReason::NewtypeRecursiveRepresentation);
    let closing = text
        .rfind("Left))")
        .expect("the closing occurrence should remain present");
    assert_eq!(
        error.primary.span().range().start(),
        u32::try_from(closing).expect("fixture offset should fit")
    );
    assert_eq!(
        error.primary.span().range().end(),
        u32::try_from(closing + "Left".len()).expect("fixture offset should fit")
    );
    assert_eq!(error.related.len(), 2);
}

#[test]
fn module_newtype_cycle_through_effect_argument_retains_the_closing_occurrence() {
    let text = concat!(
        "effect Alpha<A> {\n",
        "    alpha : Unit -> Unit\n",
        "}\n",
        "effect Zeta<A> {\n",
        "    zeta : Unit -> Unit\n",
        "}\n",
        "newtype Left = Left(Unit -> Unit ! {Zeta<Right>, Alpha<Int>})\n",
        "newtype Right = Right(Unit -> Unit ! {Zeta<Int>, Alpha<Left>})\n",
    );
    let tree = ModuleTree::create();
    let entry = tree.write("entry.ash", text);
    let graph =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture module graph should load");
    let ResolveModuleError::Representation(TypeError::Source(error)) =
        resolve_fixture(&tree, &graph, module_named(&graph, "entry.ash"), &[])
            .expect_err("a cycle through effect arguments should be rejected")
    else {
        panic!("the effect-argument cycle should retain a source diagnostic");
    };
    assert_eq!(error.reason, TypeReason::NewtypeRecursiveRepresentation);
    let closing = text
        .rfind("Left>})")
        .expect("the closing effect argument should remain present");
    assert_eq!(
        error.primary.span().range().start(),
        u32::try_from(closing).expect("fixture offset should fit")
    );
    assert_eq!(
        error.primary.span().range().end(),
        u32::try_from(closing + "Left".len()).expect("fixture offset should fit")
    );
    assert_eq!(error.related.len(), 2);
}

#[test]
fn module_newtype_representation_kind_failure_precedes_cycle_checking() {
    let tree = ModuleTree::create();
    let entry = tree.write("entry.ash", "newtype UserId = UserId(UserId<Int>)\n");
    let graph =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture module graph should load");

    let ResolveModuleError::Kind(error) =
        resolve_fixture(&tree, &graph, module_named(&graph, "entry.ash"), &[])
            .expect_err("an ill-kinded representation must fail before module checking")
    else {
        panic!("representation kinding belongs to resolved admission");
    };
    assert_eq!(error.reason_code(), "kind.not-applicable");
}

#[test]
fn transparent_newtype_constructor_expression_wraps_its_representation() {
    let tree = ModuleTree::create();
    let entry = tree.write(
        "entry.ash",
        "newtype UserId = UserId(Int)\nmain : Unit -> UserId\nmain () = UserId(1)\n",
    );
    let graph =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture module graph should load");
    let resolved = resolve_fixture(&tree, &graph, module_named(&graph, "entry.ash"), &[])
        .expect("the newtype declaration and its constructor occurrence should resolve");

    check_module(resolved)
        .expect("an accessible newtype constructor should wrap its representation");
}

#[test]
fn module_newtype_constructors_are_first_class_across_representation_shapes() {
    let cases = [
        concat!(
            "newtype Pair = Pair((Int, Bool))\n",
            "main : Unit -> Pair\n",
            "main () = Pair((1, true))\n",
        ),
        concat!(
            "type Wrapped = Wrapped(Int)\n",
            "newtype Container = Container(Wrapped)\n",
            "main : Unit -> Container\n",
            "main () = Container(Wrapped(1))\n",
        ),
        concat!(
            "newtype Inner = Inner(Int)\n",
            "newtype Outer = Outer(Inner)\n",
            "main : Unit -> Outer\n",
            "main () = Outer(Inner(1))\n",
        ),
        concat!(
            "newtype Box<A> = Box(A)\n",
            "main : Unit -> Box<Int>\n",
            "main () = {\nlet apply = fn((function, value)) {\nfunction value\n}\napply(Box, 42)\n}\n",
        ),
        concat!(
            "newtype UserId = UserId(Int)\n",
            "main : Unit -> UserId\n",
            "main () = {\nlet make = fn(()) {\nUserId\n}\nmake()(42)\n}\n",
        ),
    ];

    for (index, text) in cases.into_iter().enumerate() {
        let tree = ModuleTree::create();
        let entry = tree.write("entry.ash", text);
        let graph = load_module_graph(&entry, &ModuleRoots::empty())
            .expect("constructor matrix module graph should load");
        let resolved = resolve_fixture(&tree, &graph, module_named(&graph, "entry.ash"), &[])
            .expect("constructor matrix case should resolve");
        check_module(resolved).unwrap_or_else(|error| {
            panic!("constructor matrix case {index} should check: {error}")
        });
    }
}

#[test]
fn annotated_callback_does_not_hide_an_erased_constructor_row() {
    let tree = ModuleTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "newtype Box<A> = Box(A)\n",
            "apply : (A -> B, A) -> B\n",
            "apply (function, value) = function value\n",
            "main : Unit -> Box<Int>\n",
            "main () = apply(Box, 42)\n",
        ),
    );
    let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    let resolved = resolve_fixture(&tree, &graph, module_named(&graph, "entry.ash"), &[]).unwrap();
    let error = check_module(resolved).expect_err("the annotated callback retains its full row");
    assert!(
        matches!(error, TypeError::Source(ref diagnostic) if diagnostic.reason == TypeReason::Argument),
        "{error:?}"
    );
}

#[test]
fn annotated_return_does_not_hide_an_erased_constructor_row() {
    let tree = ModuleTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "newtype UserId = UserId(Int)\n",
            "make : Unit -> (Int -> UserId)\n",
            "make () = UserId\n",
            "main : Unit -> UserId\n",
            "main () = make()(42)\n",
        ),
    );
    let graph = load_module_graph(&entry, &ModuleRoots::empty()).unwrap();
    let resolved = resolve_fixture(&tree, &graph, module_named(&graph, "entry.ash"), &[]).unwrap();
    let error = check_module(resolved).expect_err("the annotated result retains its full row");
    assert!(
        matches!(error, TypeError::Source(ref diagnostic) if diagnostic.reason == TypeReason::DefinitionResult),
        "{error:?}"
    );
}

#[test]
fn transparent_newtype_constructor_pattern_unwraps_its_representation() {
    let tree = ModuleTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "newtype UserId = UserId(Int)\n",
            "read : UserId -> Int\n",
            "read value = match value {\n",
            "UserId(number) => number\n",
            "}\n",
            "main : Unit -> Int\n",
            "main () = read(UserId(42))\n",
        ),
    );
    let graph =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture module graph should load");
    let resolved = resolve_fixture(&tree, &graph, module_named(&graph, "entry.ash"), &[])
        .expect("the newtype declaration and its value pattern should resolve");

    let checked = check_module(resolved)
        .expect("an accessible newtype constructor pattern should unwrap its representation");
    let mut component = tree.take_implicit_services(&graph);
    component.push(checked);
    let linked = link_modules(component, graph.entry())
        .expect("the checked newtype pattern module should link");
    let linked = validate_interface_evidence(linked)
        .expect("the newtype pattern has no unauthenticated interface evidence");
    let mut elaborator =
        EffectElaborator::for_module_program(&linked).expect("the final Core namespace should fit");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("the newtype pattern should lower through an explicit unwrap");
    let unchecked = elaborator
        .finish(typed.node)
        .expect("the explicit unwrap should finish as unvalidated Core");
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
        .expect("the canonical unwrap conversion should independently authenticate");
    let evaluation = evaluate_effect(&program).expect("the authenticated conversions should erase");
    let Value::SmallInteger(value) = evaluation.value else {
        panic!("the unwrapped representation should remain an integer");
    };
    assert_eq!(value.to_string(), "42");
}

#[test]
fn irrefutable_newtype_function_and_binding_patterns_preserve_payload_binders() {
    let tree = ModuleTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "newtype Pair = Pair((Int, Bool))\n",
            "first : Pair -> Int\n",
            "first (Pair((number, _))) = number\n",
            "main : Unit -> Int\n",
            "main () = {\n",
            "let Pair((number, _)) = Pair((42, true))\n",
            "first(Pair((number, false)))\n",
            "}\n",
        ),
    );
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("function and binding pattern module graph should load");
    let resolved = resolve_fixture(&tree, &graph, module_named(&graph, "entry.ash"), &[])
        .expect("function and binding newtype patterns should resolve");

    check_module(resolved)
        .expect("irrefutable function and binding patterns should retain payload binders");
}

#[test]
fn mixed_newtype_match_fallback_binder_keeps_the_nominal_value() {
    let tree = ModuleTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "newtype Flag = Flag(Bool)\n",
            "fallback : Flag -> Int\n",
            "fallback _ = 0\n",
            "classify : Flag -> Int\n",
            "classify value = match value {\n",
            "Flag(true) => 1\n",
            "other => fallback(other)\n",
            "}\n",
            "main : Unit -> Int\n",
            "main () = classify(Flag(false))\n",
        ),
    );
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("mixed fallback module graph should load");
    let resolved = resolve_fixture(&tree, &graph, module_named(&graph, "entry.ash"), &[])
        .expect("mixed fallback patterns should resolve");

    check_module(resolved)
        .expect("a fallback binder should retain the original nominal newtype value");
}

#[test]
fn newtype_patterns_cover_parameterized_nested_and_refutable_representations() {
    let tree = ModuleTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "type Wrapped = Wrapped(Int)\n",
            "newtype Container = Container(Wrapped)\n",
            "newtype Box<A> = Box(A)\n",
            "newtype Inner = Inner(Int)\n",
            "newtype Outer = Outer(Inner)\n",
            "newtype Flag = Flag(Bool)\n",
            "unbox : Box<A> -> A\n",
            "unbox (Box(value)) = value\n",
            "nested : Outer -> Int\n",
            "nested (Outer(Inner(value))) = value\n",
            "contained : Container -> Int\n",
            "contained (Container(Wrapped(value))) = value\n",
            "classify : Flag -> Int\n",
            "classify value = match value {\n",
            "Flag(true) => 1\n",
            "Flag(false) => 0\n",
            "}\n",
            "main : Unit -> Int\n",
            "main () = unbox(Box(nested(Outer(Inner(contained(Container(Wrapped(41)))))))) + classify(Flag(true))\n",
        ),
    );
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("pattern representation matrix module graph should load");
    let resolved = resolve_fixture(&tree, &graph, module_named(&graph, "entry.ash"), &[])
        .expect("pattern representation matrix should resolve");

    check_module(resolved)
        .expect("parameterized, nested, data, and refutable newtype patterns should check");
}

#[test]
fn newtype_nominal_mismatch_precedes_coverage_and_payload_coverage_is_retained() {
    let cases = [
        (
            concat!(
                "newtype UserId = UserId(Int)\n",
                "newtype OrderId = OrderId(Int)\n",
                "read : UserId -> Int\n",
                "read value = match value {\n",
                "OrderId(number) => number\n",
                "}\n",
            ),
            TypeReason::ConstructorOwner,
        ),
        (
            concat!(
                "newtype Flag = Flag(Bool)\n",
                "read : Flag -> Int\n",
                "read value = match value {\n",
                "Flag(true) => 1\n",
                "}\n",
            ),
            TypeReason::NonExhaustive,
        ),
    ];

    for (text, expected) in cases {
        let tree = ModuleTree::create();
        let entry = tree.write("entry.ash", text);
        let graph = load_module_graph(&entry, &ModuleRoots::empty())
            .expect("newtype diagnostic module graph should load");
        let resolved = resolve_fixture(&tree, &graph, module_named(&graph, "entry.ash"), &[])
            .expect("newtype diagnostic case should resolve");
        let TypeError::Source(error) =
            check_module(resolved).expect_err("newtype diagnostic case should be rejected")
        else {
            panic!("newtype diagnostic should remain source-owned");
        };
        assert_eq!(error.reason, expected);
    }
}

#[test]
fn module_newtype_cycle_stops_at_an_ordinary_data_boundary() {
    let tree = ModuleTree::create();
    let entry = tree.write(
        "entry.ash",
        "newtype Token = Token(Box)\ntype Box = Box(Token)\n",
    );
    let graph =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture module graph should load");
    let resolved = resolve_fixture(&tree, &graph, module_named(&graph, "entry.ash"), &[])
        .expect("the mixed declaration representations should kind-check");

    check_module(resolved)
        .expect("an ordinary data declaration must break the newtype-only cycle graph");
}

#[test]
fn module_parameterized_newtype_cycle_uses_the_applied_nominal_identity() {
    let tree = ModuleTree::create();
    let entry = tree.write("entry.ash", "newtype Loop<A> = Loop(Loop<A>)\n");
    let graph =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture module graph should load");
    let ResolveModuleError::Representation(TypeError::Source(error)) =
        resolve_fixture(&tree, &graph, module_named(&graph, "entry.ash"), &[])
            .expect_err("an applied self representation must remain a newtype cycle")
    else {
        panic!("the parameterized cycle must be a source typing diagnostic");
    };
    assert_eq!(error.reason, TypeReason::NewtypeRecursiveRepresentation);
}

#[test]
fn module_newtype_targeted_renames_merge_one_defining_fact_across_a_diamond() {
    let tree = ModuleTree::create();
    let entry = tree.write(
        "entry.ash",
        "import left (LeftId)\nimport right (RightId)\n",
    );
    tree.write("base.ash", "pub newtype UserId = UserId(Int)\n");
    tree.write("left.ash", "pub import base (UserId as LeftId)\n");
    tree.write("right.ash", "pub import base (UserId as RightId)\n");
    let graph =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture module graph should load");

    let base = resolve_fixture(&tree, &graph, module_named(&graph, "base.ash"), &[])
        .expect("base should resolve");
    let defining_id = base.registry().nominals()[0].id;
    let base = check_module(base).expect("base should check");
    let check_facade = |file_name: &str| {
        let module = module_named(&graph, file_name);
        check_module(
            resolve_fixture(&tree, &graph, module, &[&base]).expect("facade should resolve"),
        )
        .expect("facade should check")
    };
    let left = check_facade("left.ash");
    let right = check_facade("right.ash");

    let module = module_named(&graph, "entry.ash");
    assert_eq!(
        module
            .dependencies()
            .iter()
            .filter(|edge| edge.target() == left.module())
            .count(),
        1
    );
    assert_eq!(
        module
            .dependencies()
            .iter()
            .filter(|edge| edge.target() == right.module())
            .count(),
        1
    );
    let entry = resolve_fixture(&tree, &graph, module, &[&left, &right])
        .expect("diamond aliases should merge their one defining newtype fact");
    let imported = entry
        .imported_facts()
        .nominal(defining_id)
        .expect("the defining identity should be retained once");
    assert_eq!(
        imported.declaration_kind,
        ResolvedNominalDeclarationKind::Newtype
    );
    assert_eq!(imported.access, ImportedTypeAccess::Transparent);
    assert_eq!(
        imported.representation.as_ref(),
        Some(&ash::types::Type::Int)
    );
}

#[test]
fn module_parameterized_newtype_preserves_its_canonical_parameter_through_a_facade() {
    let tree = ModuleTree::create();
    let entry = tree.write("entry.ash", "import facade (Box)\n");
    tree.write("base.ash", "pub newtype Box<A> = Box(A)\n");
    tree.write("facade.ash", "pub import base (Box)\n");
    let graph =
        load_module_graph(&entry, &ModuleRoots::empty()).expect("fixture module graph should load");

    let base = resolve_fixture(&tree, &graph, module_named(&graph, "base.ash"), &[])
        .expect("base should resolve");
    let defining_id = base.registry().nominals()[0].id;
    let defining_parameter = base.registry().nominal_parameters(defining_id).unwrap()[0].id;
    let base = check_module(base).expect("base should check");
    let facade_module = module_named(&graph, "facade.ash");
    let facade = check_module(
        resolve_fixture(&tree, &graph, facade_module, &[&base]).expect("facade should resolve"),
    )
    .expect("facade should check");
    let entry_module = module_named(&graph, "entry.ash");
    let entry =
        resolve_fixture(&tree, &graph, entry_module, &[&facade]).expect("entry should resolve");
    let imported = entry.imported_facts().nominal(defining_id).unwrap();
    assert_eq!(imported.parameters.len(), 1);
    assert_eq!(imported.parameters[0].id, defining_parameter);
    assert_eq!(
        imported.representation,
        Some(ash::types::Type::Variable(defining_parameter))
    );
}
