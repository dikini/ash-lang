use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    lexer::{TokenKind, lex},
    module::{LoadGraphError, ModuleRoots, load_module_graph},
    parser::{
        ConcreteElement, ConcreteNode, ConcreteTree, Event, InternalReason, NodeKind,
        ProjectionError, ResourceFailure, STRUCTURAL_DEPTH_LIMIT, parse, project_module,
    },
    source::SourceFile,
    surface::SurfaceSyntaxCategory,
};

fn parsed(text: &str) -> (SourceFile, ConcreteTree) {
    let source = SourceFile::new("derive-parser.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    let retained = tree
        .events()
        .iter()
        .filter_map(|event| match event {
            Event::Token(index) => Some(*index),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(retained, (0..tree.tokens().len()).collect::<Vec<_>>());
    (source, tree)
}

fn valid(text: &str) -> (SourceFile, ConcreteTree) {
    let (source, tree) = parsed(text);
    assert!(tree.lexical_diagnostics().is_empty(), "{text:?}");
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{text:?}: {:?}",
        tree.parse_diagnostics()
    );
    assert_eq!(tree.resource_failure(), None, "{text:?}");
    (source, tree)
}

fn children(node: &ConcreteNode, kind: NodeKind) -> Vec<&ConcreteNode> {
    node.children
        .iter()
        .filter_map(|child| match child {
            ConcreteElement::Node(child) if child.kind == kind => Some(child),
            _ => None,
        })
        .collect()
}

fn token_indices(node: &ConcreteNode) -> Vec<usize> {
    let mut indices = Vec::new();
    let mut pending = node.children.iter().rev().collect::<Vec<_>>();
    while let Some(child) = pending.pop() {
        match child {
            ConcreteElement::Node(child) => pending.extend(child.children.iter().rev()),
            ConcreteElement::Token(index) => indices.push(*index),
            ConcreteElement::Missing { .. } | ConcreteElement::Error(_) => {
                panic!("a valid node must not contain recovery")
            }
        }
    }
    indices
}

fn token_text<'a>(source: &'a SourceFile, tree: &ConcreteTree, index: usize) -> &'a str {
    let span = tree.tokens()[index].span;
    assert_eq!(span.source(), source.id());
    let range = span.range();
    &source.text()[range.start() as usize..range.end() as usize]
}

fn node_text<'a>(source: &'a SourceFile, tree: &ConcreteTree, node: &ConcreteNode) -> &'a str {
    let indices = token_indices(node);
    let first = tree.tokens()[*indices.first().unwrap()].span;
    let last = tree.tokens()[*indices.last().unwrap()].span;
    assert_eq!(first.source(), source.id());
    assert_eq!(last.source(), source.id());
    &source.text()[first.range().start() as usize..last.range().end() as usize]
}

fn deriving_clause(subject: &ConcreteNode) -> &ConcreteNode {
    let matches = subject
        .children
        .iter()
        .filter_map(|child| match child {
            ConcreteElement::Node(child) if child.kind == NodeKind::DerivingClause => Some(child),
            _ => None,
        })
        .collect::<Vec<_>>();
    let [clause] = matches.as_slice() else {
        panic!("expected one direct deriving clause: {subject:?}");
    };
    assert!(matches!(
        subject.children.last(),
        Some(ConcreteElement::Node(last)) if std::ptr::eq(last, *clause)
    ));
    clause
}

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "ash-r1-parser-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn write(&self, name: &str, text: &str) {
        fs::write(self.0.join(name), text).unwrap();
    }

    fn entry(&self) -> PathBuf {
        self.0.join("entry.ash")
    }

    fn configuration(&self) -> RunConfiguration {
        RunConfiguration {
            entry: self.entry(),
            roots: ModuleRoots::empty(),
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn derive_headers_retain_the_contextual_form_and_optional_fixed_binding() {
    for (text, binding, template) in [
        (
            "pub syntax derive: (marker) $target:ident => {\n    type Item = Item\n}\n",
            true,
            true,
        ),
        (
            "pub syntax derive: (marker) => {\n    type Item = Item\n}\n",
            false,
            true,
        ),
        (
            "pub syntax derive: (marker) $target:ident => using expand\n",
            true,
            false,
        ),
        (
            "pub syntax derive: (marker) => using expand\n",
            false,
            false,
        ),
    ] {
        let (source, tree) = valid(text);
        let declarations = children(tree.root().unwrap(), NodeKind::SyntaxDeclaration);
        let [declaration] = declarations.as_slice() else {
            panic!("expected one syntax declaration: {text:?}");
        };
        assert_eq!(node_text(&source, &tree, declaration), text.trim_end());
        let header = token_indices(declaration)
            .into_iter()
            .take(7)
            .map(|index| token_text(&source, &tree, index))
            .collect::<Vec<_>>();
        assert_eq!(header, ["pub", "syntax", "derive", ":", "(", "marker", ")"]);
        let captures = children(declaration, NodeKind::SyntaxCapture);
        assert_eq!(captures.len(), usize::from(binding), "{text:?}");
        if binding {
            assert_eq!(node_text(&source, &tree, captures[0]), "$target:ident");
        }
        assert_eq!(
            children(declaration, NodeKind::TemplateBody).len(),
            usize::from(template),
            "{text:?}"
        );
        // Derive category admission is not part of this parser-only delivery.
        assert!(project_module(&source, &tree).is_err(), "{text:?}");
    }
}

#[test]
fn derive_and_deriving_remain_ordinary_names_outside_the_contextual_forms() {
    let old = include_str!("../docs/design/macros/fixtures/header_compat/derive_expressions.ash");
    let (source, tree) = valid(old);
    let module = project_module(&source, &tree).unwrap();
    let [syntax] = module.syntax_declarations.as_slice() else {
        panic!("expected the retained expression macro named derive");
    };
    assert_eq!(syntax.name.text, "derive");
    assert_eq!(syntax.category, SurfaceSyntaxCategory::Expression);

    let text = "type Thing = Thing\n\
                derive : Unit -> Int\n\
                derive () = 40\n\
                deriving : Unit -> Int\n\
                deriving () = 2\n\
                main : Unit -> Int\n\
                main () = derive(()) + deriving(())\n";
    let (source, tree) = valid(text);
    for name in ["derive", "deriving"] {
        assert!(
            tree.tokens().iter().any(|token| {
                matches!(&token.kind, TokenKind::Identifier(found) if found == name)
            })
        );
    }
    project_module(&source, &tree).expect("the ordinary globals still project");
    let fixture = Fixture::new();
    fixture.write("entry.ash", text);
    let program = compile_path(fixture.configuration()).unwrap();
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn deriving_clauses_retain_subjects_order_duplicates_and_exact_spans() {
    for (subject, kind, expected) in [
        (
            "type Color = Red\n    | Blue\n    deriving (marker, tagged, marker,)",
            NodeKind::TypeDeclaration,
            vec![
                "deriving", "(", "marker", ",", "tagged", ",", "marker", ",", ")",
            ],
        ),
        (
            "newtype Count = Count(Int)\n    deriving (renamed,)",
            NodeKind::NewtypeDeclaration,
            vec!["deriving", "(", "renamed", ",", ")"],
        ),
        (
            "pub opaque type Box<A> = Box(A)\n    deriving (marker)",
            NodeKind::TypeDeclaration,
            vec!["deriving", "(", "marker", ")"],
        ),
        (
            "pub opaque newtype Box<A> = Box(A)\n    deriving (\n        first,\n        second,\n    )",
            NodeKind::NewtypeDeclaration,
            vec!["deriving", "(", "first", ",", "second", ",", ")"],
        ),
    ] {
        let text = format!("{subject}\nmain : Unit -> Int\nmain () = 42\n");
        let (source, tree) = valid(&text);
        let subjects = children(tree.root().unwrap(), kind);
        let [node] = subjects.as_slice() else {
            panic!("expected one subject in {subject:?}");
        };
        let clause = deriving_clause(node);
        assert_eq!(node_text(&source, &tree, node), subject);
        let indices = token_indices(clause);
        assert_eq!(indices.len(), expected.len(), "{subject:?}");
        assert!(indices.windows(2).all(|pair| pair[0] < pair[1]));
        assert!(
            indices
                .iter()
                .all(|index| token_indices(node).contains(index))
        );
        for (index, spelling) in indices.into_iter().zip(expected) {
            assert_eq!(token_text(&source, &tree, index), spelling);
            let kind = &tree.tokens()[index].kind;
            assert!(
                match spelling {
                    "(" => matches!(kind, TokenKind::LeftParen),
                    ")" => matches!(kind, TokenKind::RightParen),
                    "," => matches!(kind, TokenKind::Comma),
                    name => matches!(kind, TokenKind::Identifier(found) if found == name),
                },
                "wrong token kind {kind:?} for {spelling:?}"
            );
        }
        assert!(project_module(&source, &tree).is_err(), "{subject:?}");
    }
}

#[test]
fn deriving_uses_the_written_local_import_name() {
    let text = "import generators (syntax marker as renamed)\n\
                type Color = Red\n\
                deriving (renamed,)\n";
    let (source, tree) = valid(text);
    let imports = children(tree.root().unwrap(), NodeKind::ImportDeclaration);
    let [import] = imports.as_slice() else {
        panic!("expected one renamed syntax import");
    };
    assert_eq!(
        node_text(&source, &tree, import),
        "import generators (syntax marker as renamed)"
    );
    let subjects = children(tree.root().unwrap(), NodeKind::TypeDeclaration);
    let [subject] = subjects.as_slice() else {
        panic!("expected one subject");
    };
    let clause = deriving_clause(subject);
    let spellings = token_indices(clause)
        .into_iter()
        .map(|index| token_text(&source, &tree, index))
        .collect::<Vec<_>>();
    assert_eq!(spellings, ["deriving", "(", "renamed", ",", ")"]);
}

#[test]
fn fixed_derive_fixtures_reach_only_the_cst_boundary() {
    let cases: &[(&str, &str, &[&[&str]])] = &[
        (
            "I09 main",
            include_str!("../docs/design/macros/fixtures/derives/main.ash"),
            &[&["marker", "tagged"], &["marker", "tagged"]],
        ),
        (
            "I09 renamed",
            include_str!("../docs/design/macros/fixtures/derives/renamed.ash"),
            &[&["renamed"]],
        ),
        (
            "I09 generic",
            include_str!("../docs/design/macros/fixtures/derives/generic.ash"),
            &[&["generic_marker"]],
        ),
        (
            "I09 opaque subject",
            include_str!("../docs/design/macros/fixtures/derives/opaque_subject.ash"),
            &[&["public_marker"]],
        ),
        (
            "I09 duplicate",
            include_str!("../docs/design/macros/fixtures/derives/duplicate.ash"),
            &[&["marker", "marker"]],
        ),
    ];
    for (label, text, expected) in cases {
        let (source, tree) = valid(text);
        let actual = tree
            .root()
            .unwrap()
            .children
            .iter()
            .filter_map(|child| match child {
                ConcreteElement::Node(node)
                    if matches!(
                        node.kind,
                        NodeKind::TypeDeclaration | NodeKind::NewtypeDeclaration
                    ) =>
                {
                    Some(deriving_clause(node))
                }
                _ => None,
            })
            .map(|clause| {
                token_indices(clause)
                    .into_iter()
                    .filter_map(|index| match &tree.tokens()[index].kind {
                        TokenKind::Identifier(name) if name != "deriving" => {
                            Some(token_text(&source, &tree, index))
                        }
                        _ => None,
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        assert_eq!(
            actual.iter().map(Vec::as_slice).collect::<Vec<_>>(),
            *expected,
            "{label}"
        );
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape
            )),
            "{label}"
        );
    }
    for text in [
        include_str!("../docs/design/macros/fixtures/derives/empty.ash"),
        include_str!("../docs/design/macros/fixtures/derives/unsupported.ash"),
    ] {
        let (source, tree) = parsed(text);
        assert!(!tree.parse_diagnostics().is_empty());
        assert!(project_module(&source, &tree).is_err());
    }
    // These definition bodies are intentionally not admitted or validated here.
    for text in [
        include_str!("../docs/design/macros/fixtures/diagnostics/malformed_derive_forms.ash"),
        include_str!("../docs/design/macros/fixtures/diagnostics/free_derive_forms.ash"),
    ] {
        let (source, tree) = valid(text);
        assert_eq!(
            children(tree.root().unwrap(), NodeKind::SyntaxDeclaration).len(),
            1
        );
        assert_eq!(
            project_module(&source, &tree),
            Err(ProjectionError::MalformedTree(
                InternalReason::UnexpectedShape
            ))
        );
    }
}

#[test]
fn derive_header_preserves_nested_quote_escape_and_mode_restoration() {
    let text = "pub syntax derive: (marker) $target:ident => {\n\
                $target () = syntax { ${ syntax { $local } } + $target }\n\
                sibling () = syntax { ${ $target } + $target }\n\
                }\n\
                probe : Unit -> Int\n\
                probe () = syntax { $outside }\n";
    let (source, tree) = valid(text);
    let mut pending = vec![tree.root().unwrap()];
    let mut found = Vec::new();
    while let Some(node) = pending.pop() {
        if matches!(
            node.kind,
            NodeKind::SyntaxQuote
                | NodeKind::SyntaxEscape
                | NodeKind::TemplateSplice
                | NodeKind::EscapeCaptureRead
                | NodeKind::QuoteHole
        ) {
            found.push(node);
        }
        pending.extend(node.children.iter().filter_map(|child| match child {
            ConcreteElement::Node(child) => Some(child),
            _ => None,
        }));
    }
    for (kind, expected) in [
        (NodeKind::SyntaxQuote, 4),
        (NodeKind::SyntaxEscape, 2),
        (NodeKind::TemplateSplice, 2),
        (NodeKind::EscapeCaptureRead, 1),
        (NodeKind::QuoteHole, 2),
    ] {
        assert_eq!(
            found.iter().filter(|node| node.kind == kind).count(),
            expected,
            "{kind:?}"
        );
    }
    let mut holes = found
        .iter()
        .filter(|node| node.kind == NodeKind::QuoteHole)
        .map(|node| node_text(&source, &tree, node))
        .collect::<Vec<_>>();
    holes.sort_unstable();
    assert_eq!(holes, ["$local", "$outside"]);
    assert!(
        found
            .iter()
            .filter(|node| node.kind == NodeKind::TemplateSplice)
            .all(|node| node_text(&source, &tree, node) == "$target")
    );
    assert_eq!(
        project_module(&source, &tree),
        Err(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape
        ))
    );
}

#[test]
fn source_sink_executes_without_clause_and_refuses_complete_clause() {
    let fixture = Fixture::new();
    fixture.write(
        "forms.ash",
        include_str!("fixtures/surface-macros/declaration-capture/forms.ash"),
    );
    for declaration in ["type Subject = Subject", "newtype Subject = Subject(Int)"] {
        for has_clause in [false, true] {
            let suffix = if has_clause {
                "\nderiving (marker)"
            } else {
                ""
            };
            fixture.write("entry.ash", &format!(
                "import forms (syntax sink)\nsink {{\n{declaration}{suffix}\n}}\nmain : Unit -> Int\nmain () = 42\n"
            ));
            let result = compile_path(fixture.configuration());
            if has_clause {
                let failure =
                    result.expect_err("an unconsumed subject must not enter the packet path");
                assert!(
                    matches!(failure.graph_failure(), Some(LoadGraphError::Projection { source, .. })
                    if source.display_path().ends_with("entry.ash")),
                    "{failure:?}"
                );
            } else {
                let program = result.expect("an ordinary source capture executes");
                assert_eq!(execute(&program).unwrap().value_display(), "42");
            }
        }
    }
}

#[test]
fn malformed_derive_headers_are_not_expression_syntax() {
    for text in [
        "pub syntax derive: () => {}\n",
        "pub syntax derive: (Marker) => {}\n",
        "pub syntax derive: (syntax) => {}\n",
        "pub syntax derive: (marker, other) => {}\n",
        "pub syntax derive: (marker => {}\n",
        "pub syntax derive: (marker) $Target:ident => {}\n",
        "pub syntax derive: (marker) $target:expr => {}\n",
        "pub syntax derive: (marker) $one:ident $two:ident => {}\n",
        "pub syntax derive: (marker) literal => {}\n",
    ] {
        let (source, tree) = parsed(text);
        assert!(
            !tree.lexical_diagnostics().is_empty() || !tree.parse_diagnostics().is_empty(),
            "accepted {text:?}"
        );
        assert!(project_module(&source, &tree).is_err(), "{text:?}");
    }
}

#[test]
fn malformed_and_unsupported_clauses_do_not_project() {
    for text in [
        "type Color = Red\nderiving ()\n",
        "type Color = Red\nderiving (, marker)\n",
        "type Color = Red\nderiving (marker,, other)\n",
        "type Color = Red\nderiving (marker other)\n",
        "type Color = Red\nderiving (Marker)\n",
        "type Color = Red\nderiving (forms.marker)\n",
        "type Color = Red\nderiving (marker(1))\n",
        "type Color = Red\nderiving (marker) (other)\n",
        "type Color = Red\nderiving (marker\n",
        "type Color = Red deriving (marker)\n",
        "type Color = Red\n#[derive(marker)]\n",
        "type Color = Red\n@derive(marker)\n",
        "interface Marker<A> {\n mark : A -> Bool\n}\nderiving (marker)\n",
        "fn answer() -> Int {\n 42\n}\nderiving (marker)\n",
    ] {
        let (source, tree) = parsed(text);
        assert!(
            !tree.lexical_diagnostics().is_empty() || !tree.parse_diagnostics().is_empty(),
            "accepted {text:?}"
        );
        assert!(project_module(&source, &tree).is_err(), "{text:?}");
    }
}

#[test]
fn malformed_closed_clause_recovers_at_the_next_declaration() {
    let text = "type First = First\nderiving (, marker)\ntype Next = Next\n";
    let (source, tree) = parsed(text);
    assert!(!tree.parse_diagnostics().is_empty());
    let subjects = children(tree.root().unwrap(), NodeKind::TypeDeclaration);
    let next = subjects
        .last()
        .expect("the next declaration remains in the tree");
    assert_eq!(node_text(&source, &tree, next), "type Next = Next");
    assert!(project_module(&source, &tree).is_err());
}

#[test]
fn local_newtypes_do_not_gain_deriving_clauses() {
    let ordinary = "main : Unit -> Int\nmain () = {\n    newtype Local = Local(Int)\n    42\n}\n";
    let (source, tree) = valid(ordinary);
    project_module(&source, &tree).expect("the retained local newtype still projects");
    let ordinary_call = "deriving : Int -> Int\nderiving value = value\n\
                         main : Unit -> Int\nmain () = {\n\
                             newtype Local = Local(Int)\n\
                             deriving(42)\n}\n";
    let (source, tree) = valid(ordinary_call);
    project_module(&source, &tree).expect("the block result remains an ordinary call");
    let fixture = Fixture::new();
    fixture.write("entry.ash", ordinary_call);
    let program = compile_path(fixture.configuration()).unwrap();
    assert_eq!(execute(&program).unwrap().value_display(), "42");
    let unsupported = "main : Unit -> Int\nmain () = {\n    newtype Local = Local(Int)\n    deriving (marker)\n    42\n}\n";
    let (source, tree) = parsed(unsupported);
    assert!(!tree.parse_diagnostics().is_empty());
    assert!(project_module(&source, &tree).is_err());
}

#[test]
fn deriving_subject_depth_and_disposal_fit_a_small_stack() {
    const CHILD: &str = "ASH_R1_DERIVING_STACK_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "deriving_subject_depth_and_disposal_fit_a_small_stack",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .output()
            .expect("the isolated stack witness should start");
        assert!(
            output.status.success(),
            "the isolated stack witness failed: {}\n{}",
            output.status,
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(stdout.contains("accepted, accepted dropped, rejected, rejected dropped"));
        print!("{stdout}");
        return;
    }
    let markers = std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(|| {
            let text = |depth| {
                format!(
                    "newtype Deep = Deep({}Int{})\nderiving (marker)\n",
                    "(".repeat(depth),
                    ")".repeat(depth)
                )
            };
            let (source, accepted) = valid(&text(STRUCTURAL_DEPTH_LIMIT));
            let subject = children(accepted.root().unwrap(), NodeKind::NewtypeDeclaration)[0];
            assert_eq!(
                node_text(&source, &accepted, deriving_clause(subject)),
                "deriving (marker)"
            );
            assert_eq!(
                project_module(&source, &accepted),
                Err(ProjectionError::MalformedTree(
                    InternalReason::UnexpectedShape
                ))
            );
            let mut markers = vec!["accepted"];
            drop(accepted);
            drop(source);
            markers.push("accepted dropped");
            let source =
                SourceFile::new("derive-depth.ash", text(STRUCTURAL_DEPTH_LIMIT + 1)).unwrap();
            let rejected = parse(lex(&source).unwrap());
            assert_eq!(
                rejected.resource_failure(),
                Some(ResourceFailure::StructuralDepth {
                    limit: STRUCTURAL_DEPTH_LIMIT
                })
            );
            markers.push("rejected");
            drop(rejected);
            drop(source);
            markers.push("rejected dropped");
            markers
        })
        .unwrap()
        .join()
        .expect("bounded parsing and disposal should fit the stack");
    assert_eq!(
        markers,
        [
            "accepted",
            "accepted dropped",
            "rejected",
            "rejected dropped"
        ]
    );
    println!("{}", markers.join(", "));
}

#[test]
fn unconsumed_clauses_stop_complete_and_staged_loading() {
    let fixture = Fixture::new();
    let subject = "type Subject = Subject\n    deriving (marker)\n";
    let main = "main : Unit -> Int\nmain () = 42\n";
    fixture.write("entry.ash", &format!("type Subject = Subject\n{main}"));
    load_module_graph(&fixture.entry(), &ModuleRoots::empty())
        .expect("the same subject without a clause loads completely");
    let control = compile_path(fixture.configuration())
        .expect("the same subject without a clause reaches staged compilation");
    assert_eq!(execute(&control).unwrap().value_display(), "42");
    fixture.write("entry.ash", &format!("{subject}{main}"));
    let failure = load_module_graph(&fixture.entry(), &ModuleRoots::empty())
        .expect_err("complete loading must not discard the clause");
    assert!(matches!(
        failure.failure(),
        LoadGraphError::Projection { .. }
    ));
    let failure = compile_path(fixture.configuration())
        .expect_err("the staged fast path must not discard the clause");
    assert!(matches!(
        failure.graph_failure(),
        Some(LoadGraphError::Projection { .. })
    ));

    fixture.write(
        "forms.ash",
        "pub syntax declaration: (stamp) $name:ident => {\n\
             pub $name : Unit -> Int\n\
             $name () = 42\n\
         }\n",
    );
    let prefix = "import forms (syntax stamp)\nstamp answer\n";
    let body = "main : Unit -> Int\nmain () = answer(())\n";
    fixture.write(
        "entry.ash",
        &format!("{prefix}type Subject = Subject\n{body}"),
    );
    let control = compile_path(fixture.configuration()).expect("stamp reaches staged expansion");
    assert_eq!(execute(&control).unwrap().value_display(), "42");
    fixture.write("entry.ash", &format!("{prefix}{subject}{body}"));
    let failure = compile_path(fixture.configuration())
        .expect_err("staged collection must not discard the handwritten clause");
    assert!(matches!(
        failure.graph_failure(),
        Some(LoadGraphError::Projection { source, .. }) if source.display_path().ends_with("entry.ash")
    ));
}

#[test]
fn deriving_clause_cst_and_selected_import_refusal() {
    let fixture = Fixture::new();
    fixture.write(
        "forms.ash",
        "pub syntax declaration: (deriving) $name:ident => {\n\
             pub $name : Unit -> Int\n\
             $name () = 42\n\
         }\n",
    );
    let prefix = "import forms (syntax deriving)\n";
    fixture.write(
        "entry.ash",
        &format!("{prefix}deriving answer\nmain : Unit -> Int\nmain () = answer(())\n"),
    );
    let control = compile_path(fixture.configuration())
        .expect("the imported unparenthesized declaration macro is selected");
    assert_eq!(execute(&control).unwrap().value_display(), "42");
    let conflict = format!(
        "{prefix}type Subject = Subject\nderiving (answer)\nmain : Unit -> Int\nmain () = 42\n"
    );
    // Public parse does not load imports. A separate in-crate test must inspect
    // the CST with the declaration syntax selected to establish precedence.
    let (source, tree) = valid(&conflict);
    let root = tree.root().unwrap();
    let subjects = children(root, NodeKind::TypeDeclaration);
    let [subject] = subjects.as_slice() else {
        panic!("expected one subject in the conflict input");
    };
    assert_eq!(
        node_text(&source, &tree, deriving_clause(subject)),
        "deriving (answer)"
    );
    assert!(children(root, NodeKind::DeclarationSyntaxInvocation).is_empty());
    fixture.write("entry.ash", &conflict);
    // This refusal alone does not distinguish the selected parser's paths.
    let failure = compile_path(fixture.configuration())
        .expect_err("the entry must stop before ordinary checking");
    assert!(
        matches!(
            failure.graph_failure(),
            Some(LoadGraphError::Projection { source, .. }) if source.display_path().ends_with("entry.ash")
        ),
        "expected an entry projection failure: {failure:?}"
    );
}
