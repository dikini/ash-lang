use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use super::*;
use crate::parser::SYNTAX_WORK_LIMIT;

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Tree(PathBuf);

impl Tree {
    fn new() -> Self {
        loop {
            let id = NEXT.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!("ash-staged-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("fixture directory: {error}"),
            }
        }
    }

    fn write(&self, name: &str, text: &str) -> PathBuf {
        let path = self.0.join(name);
        fs::write(&path, text).unwrap();
        path
    }
}

impl Drop for Tree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn fixture() -> (Tree, PathBuf) {
    let tree = Tree::new();
    let mut entry =
        String::from("import left as Left\nimport left as Alias\nimport right as Right\n");
    for index in 0..250 {
        entry.push_str(&format!(
            "value{index} : Unit -> Int\nvalue{index} () = 42\n"
        ));
    }
    let entry = tree.write("entry.ash", &entry);
    tree.write("left.ash", "import shared as Shared\n");
    tree.write("right.ash", "import shared as Shared\n");
    tree.write("shared.ash", "  \r\n");
    (tree, entry)
}

fn graph_at(entry: &Path, mode: BodyMode, limit: usize) -> Result<HeaderGraph, GraphDiagnostic> {
    discover_graph_with_budget(
        entry,
        &ModuleRoots::empty(),
        GraphBudget {
            mode,
            syntax_work: SyntaxBudget::with_limit(limit),
            ..GraphBudget::default()
        },
    )
}

#[test]
fn g1_real_matcher_paths_on_a_512k_stack() {
    const CHILD: &str = "ASH_G1_512K_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "module::staged_tests::g1_real_matcher_paths_on_a_512k_stack",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        print!("{stdout}");
        eprint!("{stderr}");
        assert!(
            output.status.success(),
            "512 KiB child failed: {}",
            output.status
        );
        for marker in [
            "g1 stack: parsed header 128 and dropped source CST",
            "g1 stack: refused header 129 and dropped source CST",
            "g1 stack: built header 128 and dropped final matcher alias",
            "g1 stack: matched and materialized 127 on the real graph",
            "g1 stack: dropped final capture alias",
            "g1 stack: mixed 127 captured and final alias dropped",
            "g1 stack: mixed live 128 refused without publication",
            "g1 stack: refused live 128 before capture and publication",
            "g1 stack: paid late failure, no graph publication, final alias dropped",
        ] {
            assert!(stderr.contains(marker), "missing marker {marker}");
        }
        assert_eq!(
            stderr
                .matches("g1 stack: matched and materialized 127 on the real graph")
                .count(),
            2
        );
        return;
    }

    std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(|| {
            use crate::{
                driver::{FileFailure, compile_staged_graph_for_test, execute},
                lexer::lex,
                parser::{G1_CAPTURE_OBSERVER, NodeKind, ResourceFailure, STRUCTURAL_DEPTH_LIMIT, parse},
                surface::{SurfaceRepeatedCapture, SurfaceSyntaxCapture, SurfaceSyntaxMatcherPart},
                syntax::MacroOrigin,
            };
            use std::{cell::{Cell, RefCell}, sync::Arc};

            std::thread_local! {
                static CAPTURE: RefCell<Option<Arc<SurfaceRepeatedCapture>>> = const { RefCell::new(None) };
                static PAID: Cell<Option<usize>> = const { Cell::new(None) };
            }
            fn observe_depth(source: &SourceFile, captures: &[SurfaceSyntaxCapture], budget: &SyntaxBudget, levels: usize) {
                assert!(source.display_path().ends_with("main.ash"));
                let [SurfaceSyntaxCapture::Repeated(root)] = captures else {
                    panic!("expected one actual repeated capture");
                };
                let alias = Arc::clone(root);
                assert!(Arc::ptr_eq(root, &alias));
                let mut value = &captures[0];
                for _ in 0..levels {
                    let SurfaceSyntaxCapture::Repeated(level) = value else { panic!("missing repeated level"); };
                    let [only] = level.values.as_slice() else { panic!("expected one iteration"); };
                    value = only;
                }
                let SurfaceSyntaxCapture::Identifier(identifier) = value else { panic!("missing source identifier"); };
                assert_eq!(identifier.name.text, "Alpha");
                assert_eq!(identifier.name.span.source(), source.id());
                assert_eq!(identifier.name.introduction, 0);
                assert!(identifier.name.written && identifier.name.diagnostic.is_none());
                assert_eq!(identifier.origin, MacroOrigin::Source(identifier.name.span));
                let range = identifier.name.span.range();
                assert_eq!(&source.text()[range.start() as usize..range.end() as usize], "Alpha");
                CAPTURE.with(|slot| *slot.borrow_mut() = Some(alias));
                PAID.set(Some(budget.consumed()));
            }
            fn observe(source: &SourceFile, captures: &[SurfaceSyntaxCapture], budget: &SyntaxBudget) {
                observe_depth(source, captures, budget, 127);
                eprintln!("g1 stack: matched and materialized 127 on the real graph");
            }
            fn observe_mixed(source: &SourceFile, captures: &[SurfaceSyntaxCapture], budget: &SyntaxBudget) {
                observe_depth(source, captures, budget, 64);
            }
            fn forms(depth: usize) -> String {
                let mut matcher = format!("{}$value:ident", "$(".repeat(depth));
                for marker in (0..depth).rev() {
                    matcher.push_str(&format!(" {marker} )+"));
                }
                format!("pub syntax declaration: (sink) {matcher} => {{}}\n")
            }
            fn invocation(depth: usize) -> String {
                let mut text = String::from("sink Alpha");
                for marker in (0..depth).rev() { text.push_str(&format!(" {marker}")); }
                text
            }
            fn mixed_forms(depth: usize) -> String {
                let mut matcher = String::new();
                for level in 0..depth {
                    matcher.push_str(if level % 2 == 0 { "$( " } else if level % 4 == 1 { "( " } else { "{ " });
                }
                matcher.push_str("$value:ident");
                for level in (0..depth).rev() {
                    if level % 2 == 0 {
                        matcher.push_str(&format!(" {level} )+"));
                    } else {
                        matcher.push_str(if level % 4 == 1 { " )" } else { " }" });
                    }
                }
                format!("pub syntax declaration: (sink) {matcher} => {{}}\n")
            }
            fn mixed_invocation(depth: usize) -> String {
                let mut text = String::from("sink");
                for level in 0..depth {
                    if level % 2 != 0 {
                        text.push_str(if level % 4 == 1 { " (" } else { " {" });
                    }
                }
                text.push_str(" Alpha");
                for level in (0..depth).rev() {
                    if level % 2 == 0 {
                        text.push_str(&format!(" {level}"));
                    } else {
                        text.push_str(if level % 4 == 1 { " )" } else { " }" });
                    }
                }
                text
            }

            eprintln!("g1 stack phase: begin header-128 lex");
            let parsed_source = SourceFile::new("g1-stack-header.ash", forms(128)).unwrap();
            let lexed = lex(&parsed_source).unwrap();
            eprintln!("g1 stack phase: begin header-128 parse");
            let tree = parse(lexed);
            eprintln!("g1 stack phase: parsed header-128");
            assert!(tree.parse_diagnostics().is_empty(), "{:?}", tree.parse_diagnostics());
            assert_eq!(tree.resource_failure(), None);
            let mut pending = vec![tree.root().unwrap()];
            let mut repeats = 0;
            while let Some(node) = pending.pop() {
                repeats += usize::from(node.kind == NodeKind::SyntaxMatcherRepeat);
                pending.extend(node.children.iter().filter_map(|child| match child {
                    crate::parser::ConcreteElement::Node(child) => Some(child),
                    _ => None,
                }));
            }
            assert_eq!(repeats, 128);
            drop(pending);
            drop(tree);
            eprintln!("g1 stack: parsed header 128 and dropped source CST");
            let over_source = SourceFile::new("g1-stack-over.ash", forms(129)).unwrap();
            let over = parse(lex(&over_source).unwrap());
            assert_eq!(over.resource_failure(), Some(ResourceFailure::StructuralDepth { limit: STRUCTURAL_DEPTH_LIMIT }));
            drop(over);
            eprintln!("g1 stack: refused header 129 and dropped source CST");

            let header_tree = Tree::new();
            header_tree.write("forms.ash", &forms(128));
            let header_entry = header_tree.write("main.ash", "import forms (syntax sink)\nmain : Unit -> Int\nmain () = 42\n");
            let mut header_graph = graph_at(&header_entry, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
            eprintln!("g1 stack phase: begin real header-128 construction");
            let header_program = compile_staged_graph_for_test(&mut header_graph).unwrap();
            eprintln!("g1 stack phase: real header-128 construction completed");
            let matcher_alias = {
                let module = header_graph.completed.as_ref().unwrap().modules().iter()
                    .find(|module| module.source().display_path().ends_with("forms.ash")).unwrap();
                let [declaration] = module.surface().syntax_declarations.as_slice() else { panic!("expected the source syntax definition"); };
                let [SurfaceSyntaxMatcherPart::Container(root)] = declaration.matcher.as_slice() else { panic!("expected one matcher root"); };
                let alias = Arc::clone(root);
                assert!(Arc::ptr_eq(root, &alias));
                alias
            };
            let matcher_weak = Arc::downgrade(&matcher_alias);
            drop(header_program);
            drop(header_graph);
            assert_eq!(Arc::strong_count(&matcher_alias), 1);
            eprintln!("g1 stack phase: begin final matcher alias drop");
            drop(matcher_alias);
            assert!(matcher_weak.upgrade().is_none());
            eprintln!("g1 stack: built header 128 and dropped final matcher alias");

            let live_tree = Tree::new();
            live_tree.write("forms.ash", &forms(127));
            let live_entry = live_tree.write("main.ash", &format!(
                "import forms (syntax sink)\n{}\nmain : Unit -> Int\nmain () = 42\n", invocation(127)
            ));
            let mut live = graph_at(&live_entry, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
            eprintln!("g1 stack phase: begin real live-127 match");
            PAID.set(None);
            G1_CAPTURE_OBSERVER.set(Some(observe));
            let live_result = compile_staged_graph_for_test(&mut live);
            G1_CAPTURE_OBSERVER.set(None);
            let live_program = live_result.unwrap();
            let at_capture = PAID.get().expect("the real materializer was observed");
            assert!(live.syntax_budget.consumed() > at_capture);
            assert_eq!(execute(&live_program).unwrap().value_display(), "42");
            let alias = CAPTURE.with(|slot| slot.borrow_mut().take().unwrap());
            let weak = Arc::downgrade(&alias);
            drop(live_program);
            drop(live);
            assert_eq!(Arc::strong_count(&alias), 1);
            eprintln!("g1 stack phase: begin final capture alias drop");
            drop(alias);
            assert!(weak.upgrade().is_none());
            eprintln!("g1 stack: dropped final capture alias");

            let mixed_tree = Tree::new();
            mixed_tree.write("forms.ash", &mixed_forms(127));
            let mixed_entry = mixed_tree.write("main.ash", &format!(
                "import forms (syntax sink)\n{}\nmain : Unit -> Int\nmain () = 42\n", mixed_invocation(127)
            ));
            let mut mixed = graph_at(&mixed_entry, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
            eprintln!("g1 stack phase: begin mixed live-127 match");
            PAID.set(None);
            G1_CAPTURE_OBSERVER.set(Some(observe_mixed));
            let mixed_result = compile_staged_graph_for_test(&mut mixed);
            G1_CAPTURE_OBSERVER.set(None);
            let mixed_program = mixed_result.unwrap();
            assert!(PAID.get().is_some());
            assert_eq!(execute(&mixed_program).unwrap().value_display(), "42");
            let alias = CAPTURE.with(|slot| slot.borrow_mut().take().unwrap());
            let weak = Arc::downgrade(&alias);
            drop(mixed_program);
            drop(mixed);
            assert_eq!(Arc::strong_count(&alias), 1);
            drop(alias);
            assert!(weak.upgrade().is_none());
            eprintln!("g1 stack: mixed 127 captured and final alias dropped");

            let mixed_over_tree = Tree::new();
            mixed_over_tree.write("forms.ash", &mixed_forms(128));
            let mixed_over_entry = mixed_over_tree.write("main.ash", &format!(
                "import forms (syntax sink)\n{}\nmain : Unit -> Int\nmain () = 42\n", mixed_invocation(128)
            ));
            let mut mixed_over = graph_at(&mixed_over_entry, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
            eprintln!("g1 stack phase: begin mixed live-128 refusal");
            PAID.set(None);
            G1_CAPTURE_OBSERVER.set(Some(observe_mixed));
            let mixed_over_result = compile_staged_graph_for_test(&mut mixed_over);
            G1_CAPTURE_OBSERVER.set(None);
            let failure = match mixed_over_result { Ok(_) => panic!("expected mixed live-depth refusal"), Err(failure) => failure };
            assert_eq!(PAID.get(), None);
            assert!(mixed_over.pending.is_empty() && mixed_over.loaded.is_empty() && mixed_over.completed.is_none());
            let FileFailure::Graph(diagnostic) = &failure else { panic!("expected graph failure: {failure:?}"); };
            let LoadGraphError::Syntax(syntax) = diagnostic.failure() else { panic!("expected structural-depth failure"); };
            assert!(syntax.source.display_path().ends_with("main.ash"));
            assert!(syntax.lexical.is_empty() && syntax.parser.is_empty());
            assert!(matches!(syntax.resource, Some(ResourceFailure::StructuralDepth { limit: STRUCTURAL_DEPTH_LIMIT })));
            drop(failure);
            drop(mixed_over);
            eprintln!("g1 stack: mixed live 128 refused without publication");

            let over_live_tree = Tree::new();
            over_live_tree.write("forms.ash", &forms(128));
            let over_live_entry = over_live_tree.write("main.ash", &format!(
                "import forms (syntax sink)\n{}\nmain : Unit -> Int\nmain () = 42\n", invocation(128)
            ));
            let mut over_live = graph_at(&over_live_entry, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
            eprintln!("g1 stack phase: begin real live-128 refusal");
            PAID.set(None);
            G1_CAPTURE_OBSERVER.set(Some(observe));
            let over_live_result = compile_staged_graph_for_test(&mut over_live);
            G1_CAPTURE_OBSERVER.set(None);
            let failure = match over_live_result { Ok(_) => panic!("expected the live-depth refusal"), Err(failure) => failure };
            assert_eq!(PAID.get(), None);
            assert!(over_live.pending.is_empty() && over_live.loaded.is_empty() && over_live.completed.is_none());
            let FileFailure::Graph(diagnostic) = &failure else { panic!("expected graph failure: {failure:?}"); };
            let LoadGraphError::Syntax(syntax) = diagnostic.failure() else { panic!("expected structural-depth failure"); };
            assert!(syntax.source.display_path().ends_with("main.ash"));
            assert!(syntax.lexical.is_empty() && syntax.parser.is_empty());
            assert!(matches!(syntax.resource, Some(ResourceFailure::StructuralDepth { limit: STRUCTURAL_DEPTH_LIMIT })));
            drop(failure);
            drop(over_live);
            eprintln!("g1 stack: refused live 128 before capture and publication");

            let mut short = graph_at(&live_entry, BodyMode::Header, at_capture).unwrap();
            eprintln!("g1 stack phase: begin real late-shortage retry");
            PAID.set(None);
            G1_CAPTURE_OBSERVER.set(Some(observe));
            let short_result = compile_staged_graph_for_test(&mut short);
            G1_CAPTURE_OBSERVER.set(None);
            let failure = match short_result { Ok(_) => panic!("expected a late shortage"), Err(failure) => failure };
            assert_eq!(PAID.get(), Some(at_capture));
            assert_eq!(short.syntax_budget.consumed(), at_capture);
            assert!(short.pending.is_empty() && short.loaded.is_empty() && short.completed.is_none());
            let FileFailure::Graph(diagnostic) = &failure else { panic!("expected graph failure: {failure:?}"); };
            let LoadGraphError::Syntax(syntax) = diagnostic.failure() else { panic!("expected syntax-work failure"); };
            assert!(syntax.source.display_path().ends_with("main.ash"));
            assert!(syntax.lexical.is_empty() && syntax.parser.is_empty());
            assert!(matches!(syntax.resource, Some(ResourceFailure::SyntaxWork { limit }) if limit == at_capture));
            let alias = CAPTURE.with(|slot| slot.borrow_mut().take().unwrap());
            let weak = Arc::downgrade(&alias);
            drop(failure);
            drop(short);
            assert_eq!(Arc::strong_count(&alias), 1);
            drop(alias);
            assert!(weak.upgrade().is_none());
            eprintln!("g1 stack: paid late failure, no graph publication, final alias dropped");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn type_real_capture_roundtrip_on_a_512k_stack() {
    const CHILD: &str = "ASH_TYPE_512K_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "module::staged_tests::type_real_capture_roundtrip_on_a_512k_stack",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        print!("{stdout}");
        eprint!("{stderr}");
        assert!(
            output.status.success(),
            "512 KiB child failed: {}",
            output.status
        );
        for marker in [
            "type stack: real group-16 graph transferred and executed 42",
            "type stack: real composed-128 graph transferred and executed 42",
            "type stack: composed-129 refused without publication",
        ] {
            assert!(stderr.contains(marker), "missing marker {marker}");
        }
        return;
    }

    std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(|| {
            use crate::{
                driver::{PipelineFailure, compile_staged_graph_for_test, execute},
                eval::{CleanupStatus, RuntimeFailure, machine_test_hooks as hooks},
                parser::STRUCTURAL_DEPTH_LIMIT,
            };

            for groups in [16usize, 126, 127] {
                let tree = Tree::new();
                let forms = tree.write(
                    "forms.ash",
                    include_str!("../tests/fixtures/surface-macros/type-host/forms.ash"),
                );
                let annotation = format!("{}Int{}", "(".repeat(groups), ")".repeat(groups));
                let entry = tree.write(
                    "main.ash",
                    &format!(
                        "import forms (syntax emit_type)\nemit_type answer as {annotation}\nmain : Unit -> Int\nmain () = answer(())\n"
                    ),
                );
                let mut graph = graph_at(&entry, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
                hooks::reset();
                eprintln!("type stack phase: compile real group-{groups} graph");
                let result = compile_staged_graph_for_test(&mut graph);
                if groups <= 126 {
                    let program = result.unwrap();
                    assert_eq!(hooks::TRANSFER_ATTEMPTS.get(), 1);
                    assert_eq!(hooks::TRANSFER_FAILURES.get(), 0);
                    assert_eq!(hooks::TRANSFORMER_DROPS.get(), 1);
                    assert_eq!(hooks::ROOT_CLOSES.get(), 1);
                    assert_eq!(execute(&program).unwrap().value_display(), "42");
                    drop(program);
                    drop(graph);
                    if groups == 16 {
                        eprintln!("type stack: real group-16 graph transferred and executed 42");
                    } else {
                        // The Type capture's contents Arc and its live prefix
                        // add two layers to these actual 126 groups.
                        assert_eq!(2 + groups, STRUCTURAL_DEPTH_LIMIT);
                        eprintln!("type stack: real composed-128 graph transferred and executed 42");
                    }
                } else {
                    assert_eq!(2 + groups, STRUCTURAL_DEPTH_LIMIT + 1);
                    let failure = result.expect_err("composed depth 129 must be refused");
                    assert!(graph.pending.is_empty() && graph.loaded.is_empty() && graph.completed.is_none());
                    let Some(PipelineFailure::SyntaxRuntime(diagnostic)) = failure.pipeline_failure()
                    else {
                        panic!("expected a host depth refusal: {failure:?}");
                    };
                    let RuntimeFailure::Report(report) = diagnostic.cause() else {
                        panic!("expected a structured host report");
                    };
                    assert_eq!(
                        report.primary.reason_code(),
                        "internal.resource.structural-depth"
                    );
                    assert!(report.primary.resource().is_none());
                    assert_eq!(report.cleanup, CleanupStatus::Complete);
                    assert!(report.teardown.is_none());

                    let source = failure
                        .sources()
                        .iter()
                        .find(|source| source.id() == diagnostic.invocation.source())
                        .expect("caller source retained in the failure catalogue");
                    assert_eq!(Path::new(source.display_path()), entry.as_path());
                    let range = diagnostic.invocation.range();
                    assert_eq!(
                        &source.text()[range.start() as usize..range.end() as usize],
                        format!("emit_type answer as {annotation}")
                    );
                    let source = failure
                        .sources()
                        .iter()
                        .find(|source| source.id() == diagnostic.definition.source())
                        .expect("definition source retained in the failure catalogue");
                    assert_eq!(Path::new(source.display_path()), forms.as_path());
                    let range = diagnostic.definition.range();
                    assert_eq!(
                        &source.text()[range.start() as usize..range.end() as usize],
                        "pub syntax declaration: (emit_type) $name:ident as $result:type => using expand"
                    );
                    drop(failure);
                    drop(graph);
                    eprintln!("type stack: composed-129 refused without publication");
                }
            }
            hooks::reset();
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn expression_host_real_source_capture_roundtrips_on_a_512k_stack() {
    const CHILD: &str = "ASH_EXPRESSION_HOST_SOURCE_512K_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "module::staged_tests::expression_host_real_source_capture_roundtrips_on_a_512k_stack",
                "--nocapture", "--test-threads=1",
            ])
            .env(CHILD, "1")
            .output().unwrap();
        print!("{}", String::from_utf8_lossy(&output.stdout));
        let stderr = String::from_utf8_lossy(&output.stderr);
        eprint!("{stderr}");
        assert!(
            output.status.success(),
            "512 KiB source child failed: {}",
            output.status
        );
        for marker in [
            "expression source stack: 64 groups reached 42",
            "expression source stack: final alias dropped",
            "expression source stack: 129 groups refused",
        ] {
            assert!(stderr.contains(marker), "missing marker {marker}");
        }
        return;
    }
    std::thread::Builder::new().stack_size(512 * 1024).spawn(|| {
        use crate::{
            driver::{RunConfiguration, compile_path, execute},
            parser::G1_CAPTURE_OBSERVER,
            surface::SurfaceSyntaxCapture,
            syntax::{MacroDelimiter, MacroOutputNode},
        };
        use std::{cell::RefCell, sync::Arc};

        std::thread_local! {
            static CONTENTS: RefCell<Option<Arc<[MacroOutputNode]>>> = const { RefCell::new(None) };
        }
        fn observe(source: &SourceFile, captures: &[SurfaceSyntaxCapture], _: &SyntaxBudget) {
            let [SurfaceSyntaxCapture::Identifier(_), SurfaceSyntaxCapture::Expression(capture)] = captures else {
                panic!("expected source Expression capture")
            };
            assert_eq!(capture.expression.span.source(), source.id());
            let mut nodes = capture.contents.as_ref();
            for _ in 0..64 {
                let [MacroOutputNode::Group(MacroDelimiter::Parentheses, children, _)] = nodes else {
                    panic!("expected a source group")
                };
                nodes = children;
            }
            assert!(matches!(nodes, [MacroOutputNode::Token(_, text, _)] if &**text == "42"));
            CONTENTS.with(|slot| assert!(slot.borrow_mut().replace(Arc::clone(&capture.contents)).is_none()));
        }

        for groups in [64usize, 129] {
            let tree = Tree::new();
            tree.write("forms.ash", include_str!("../tests/fixtures/surface-macros/expression-host/forms.ash"));
            let expression = format!("{}42{}", "(".repeat(groups), ")".repeat(groups));
            let entry = tree.write("main.ash", &format!("import forms (syntax emit_expression)\nemit_expression result yields {expression}\nmain : Unit -> Int\nmain () = result(())\n"));
            G1_CAPTURE_OBSERVER.set(Some(observe));
            let result = compile_path(RunConfiguration { entry, roots: ModuleRoots::empty() });
            G1_CAPTURE_OBSERVER.set(None);
            if groups == 64 {
                let program = result.expect("the real grouped Expression graph compiles");
                let value = execute(&program).unwrap();
                assert_eq!(value.value_display(), "42");
                assert_eq!(value.type_display(), "Int");
                eprintln!("expression source stack: 64 groups reached 42");
                let alias = CONTENTS.with(|slot| slot.borrow_mut().take().expect("capture observed"));
                let weak = Arc::downgrade(&alias);
                drop(program);
                assert_eq!(Arc::strong_count(&alias), 1);
                drop(alias);
                assert!(weak.upgrade().is_none());
                eprintln!("expression source stack: final alias dropped");
            } else {
                let failure = result.expect_err("the source graph exceeds structural depth");
                assert_eq!(failure.reason_code(), "internal.resource.structural-depth");
                assert!(CONTENTS.with(|slot| slot.borrow().is_none()));
                eprintln!("expression source stack: 129 groups refused");
            }
        }
    }).unwrap().join().unwrap();
}

#[test]
fn pattern_real_source_capture_roundtrips_on_a_512k_stack() {
    const CHILD: &str = "ASH_PATTERN_SOURCE_512K_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "module::staged_tests::pattern_real_source_capture_roundtrips_on_a_512k_stack",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        print!("{}", String::from_utf8_lossy(&output.stdout));
        let stderr = String::from_utf8_lossy(&output.stderr);
        eprint!("{stderr}");
        assert!(
            output.status.success(),
            "512 KiB child failed: {}",
            output.status
        );
        for marker in [
            "pattern source stack: fifteen groups reached identity 42",
            "pattern source stack: source contents final alias dropped",
            "pattern source stack: sixteen groups refused at source depth",
        ] {
            assert!(stderr.contains(marker), "missing marker {marker}");
        }
        return;
    }
    std::thread::Builder::new().stack_size(512 * 1024).spawn(|| {
        use crate::{
            driver::{RunConfiguration, compile_path, execute},
            parser::G1_CAPTURE_OBSERVER,
            surface::{SurfacePatternKind, SurfaceSyntaxCapture},
            syntax::{MacroDelimiter, MacroOutputNode},
        };
        use std::{cell::RefCell, sync::Arc};

        std::thread_local! {
            static CONTENTS: RefCell<Option<Arc<[MacroOutputNode]>>> = const { RefCell::new(None) };
        }
        fn observe(source: &SourceFile, captures: &[SurfaceSyntaxCapture], _: &SyntaxBudget) {
            let [_, SurfaceSyntaxCapture::Pattern(capture), _, ..] = captures else {
                panic!("expected the source Pattern capture");
            };
            let SurfacePatternKind::Binder(binder) = &capture.pattern.kind else {
                panic!("expected the captured binder");
            };
            assert_eq!(binder.name.text, "value");
            assert_eq!(binder.name.span.source(), source.id());
            let mut nodes = capture.contents.as_ref();
            for _ in 0..15 {
                let [MacroOutputNode::Group(MacroDelimiter::Parentheses, children, _)] = nodes else {
                    panic!("expected a source group");
                };
                nodes = children;
            }
            assert!(matches!(nodes, [MacroOutputNode::Identifier(name, _)] if name.text == "value"));
            CONTENTS.with(|slot| assert!(slot.borrow_mut().replace(Arc::clone(&capture.contents)).is_none()));
        }

        for groups in [15usize, 16] {
            let tree = Tree::new();
            tree.write("forms.ash", include_str!("../tests/fixtures/surface-macros/pattern-host/forms.ash"));
            let pattern = format!("{}value{}", "(".repeat(groups), ")".repeat(groups));
            let entry = tree.write("main.ash", &format!(
                "import forms (syntax emit_pattern)\nemit_pattern identity matching {pattern} yields value\nmain : Unit -> Int\nmain () = identity(42)\n"
            ));
            G1_CAPTURE_OBSERVER.set(Some(observe));
            let result = compile_path(RunConfiguration { entry, roots: ModuleRoots::empty() });
            G1_CAPTURE_OBSERVER.set(None);
            if groups == 15 {
                let program = result.expect("the real grouped Pattern graph compiles");
                assert_eq!(execute(&program).unwrap().value_display(), "42");
                eprintln!("pattern source stack: fifteen groups reached identity 42");
                let alias = CONTENTS.with(|slot| slot.borrow_mut().take().expect("capture observed"));
                let weak = Arc::downgrade(&alias);
                drop(program);
                assert_eq!(Arc::strong_count(&alias), 1);
                drop(alias);
                assert!(weak.upgrade().is_none());
                eprintln!("pattern source stack: source contents final alias dropped");
            } else {
                let failure = result.expect_err("the next source group exceeds structural depth");
                assert_eq!(failure.reason_code(), "internal.resource.structural-depth");
                assert!(CONTENTS.with(|slot| slot.borrow().is_none()));
                eprintln!("pattern source stack: sixteen groups refused at source depth");
            }
        }
    }).unwrap().join().unwrap();
}

#[test]
fn identifier_and_type_captures_can_return_pattern_nodes() {
    use crate::{
        driver::{RunConfiguration, compile_path, execute},
        parser::G1_CAPTURE_OBSERVER,
        surface::SurfaceSyntaxCapture,
    };
    use std::cell::Cell;

    std::thread_local! {
        static EXPECT_TYPE: Cell<bool> = const { Cell::new(false) };
        static OBSERVED: Cell<bool> = const { Cell::new(false) };
    }
    fn observe(_: &SourceFile, captures: &[SurfaceSyntaxCapture], _: &SyntaxBudget) {
        assert!(captures.iter().all(|capture| matches!(
            capture,
            SurfaceSyntaxCapture::Identifier(_) | SurfaceSyntaxCapture::Type(_)
        )));
        let [_, SurfaceSyntaxCapture::Identifier(binder), _, ..] = captures else {
            panic!("expected the captured binder identifier");
        };
        assert_eq!(binder.name.text, "value");
        assert_eq!(
            captures
                .iter()
                .any(|capture| matches!(capture, SurfaceSyntaxCapture::Type(_))),
            EXPECT_TYPE.with(Cell::get)
        );
        OBSERVED.with(|observed| assert!(!observed.replace(true)));
    }

    for (has_type, forms, main, forms_path) in [
        (
            false,
            include_str!("../tests/fixtures/surface-macros/pattern-host/forms.ash"),
            include_str!("../tests/fixtures/surface-macros/pattern-host/main.ash"),
            "forms.ash",
        ),
        (
            true,
            include_str!("../tests/fixtures/surface-macros/pattern-host/mixed_forms.ash"),
            include_str!("../tests/fixtures/surface-macros/pattern-host/mixed_main.ash"),
            "mixed_forms.ash",
        ),
    ] {
        let substitutions = [
            ("$pattern:pattern", "$pattern:ident"),
            (
                "Syntax.Captured(Syntax.PatternCapture(pattern))",
                "Syntax.Captured(Syntax.IdentifierCapture(pattern, pattern_origin))",
            ),
            (
                "parse_result(input, name, name_origin, pattern, read",
                "parse_result(input, name, name_origin, pattern, pattern_origin, read",
            ),
            (
                "parse_result : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.PatternFragment,",
                "parse_result : (Syntax.Input, Syntax.Identifier, Syntax.Origin, Syntax.Identifier, Syntax.Origin,",
            ),
            (
                "parse_result (input, name, name_origin, pattern, read",
                "parse_result (input, name, name_origin, pattern, pattern_origin, read",
            ),
            (
                "Syntax.pattern_syntax(pattern)",
                "Syntax.Syntax(Syntax.MoreNodes(Syntax.IdentifierNode(pattern, pattern_origin), Syntax.NoNodes))",
            ),
        ];
        let mut forms = forms.to_owned();
        for (old, new) in substitutions {
            assert_eq!(forms.matches(old).count(), 1, "fixture join {old}");
            forms = forms.replacen(old, new, 1);
        }
        let tree = Tree::new();
        tree.write(forms_path, &forms);
        let entry = tree.write("main.ash", main);
        EXPECT_TYPE.with(|value| value.set(has_type));
        OBSERVED.with(|value| value.set(false));
        G1_CAPTURE_OBSERVER.set(Some(observe));
        let result = compile_path(RunConfiguration {
            entry,
            roots: ModuleRoots::empty(),
        });
        G1_CAPTURE_OBSERVER.set(None);
        let program = result.expect("the identifier-built PatternNode compiles");
        assert!(OBSERVED.with(Cell::get));
        assert_eq!(execute(&program).unwrap().value_display(), "42");
    }
}

#[test]
fn pattern_source_capture_keeps_binder_and_read_context() {
    use crate::{
        driver::{RunConfiguration, compile_path, execute},
        parser::G1_CAPTURE_OBSERVER,
        surface::{SurfacePatternKind, SurfaceSyntaxCapture},
        syntax::{MacroOrigin, MacroOutputNode},
    };
    use std::cell::Cell;

    std::thread_local! {
        static OBSERVED: Cell<bool> = const { Cell::new(false) };
    }
    fn observe(source: &SourceFile, captures: &[SurfaceSyntaxCapture], _: &SyntaxBudget) {
        let [
            SurfaceSyntaxCapture::Identifier(_),
            SurfaceSyntaxCapture::Pattern(pattern),
            SurfaceSyntaxCapture::Identifier(read),
            ..,
        ] = captures
        else {
            panic!("expected name, Pattern and read captures");
        };
        let SurfacePatternKind::Binder(binder) = &pattern.pattern.kind else {
            panic!("expected the caller's binder pattern");
        };
        assert_eq!(binder.name.text, "value");
        assert_eq!(binder.name.text, read.name.text);
        assert_eq!(binder.name.introduction, read.name.introduction);
        assert_eq!(binder.name.introduced_at, read.name.introduced_at);
        assert_eq!(binder.name.written, read.name.written);
        assert_eq!(binder.name.introduction, 0);
        assert!(binder.name.written);
        assert_ne!(binder.name.span, read.name.span);
        for span in [binder.name.span, read.name.span] {
            assert_eq!(span.source(), source.id());
            let range = span.range();
            assert_eq!(
                &source.text()[range.start() as usize..range.end() as usize],
                "value"
            );
        }
        let [MacroOutputNode::Identifier(name, MacroOrigin::Source(origin))] =
            pattern.contents.as_ref()
        else {
            panic!("expected the original binder syntax");
        };
        assert_eq!(name.span, binder.name.span);
        assert_eq!(*origin, binder.name.span);
        assert!(matches!(&read.origin, MacroOrigin::Source(span) if *span == read.name.span));
        OBSERVED.set(true);
    }

    for fixture in ["main.ash", "mixed_main.ash"] {
        OBSERVED.set(false);
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/surface-macros/pattern-host")
            .join(fixture);
        G1_CAPTURE_OBSERVER.set(Some(observe));
        let result = compile_path(RunConfiguration {
            entry,
            roots: ModuleRoots::empty(),
        });
        G1_CAPTURE_OBSERVER.set(None);
        let program = result.expect("the imported Pattern graph compiles");
        assert!(OBSERVED.get());
        assert_eq!(execute(&program).unwrap().value_display(), "42");
    }
}

#[test]
fn type_expression_real_capture_and_alias_on_a_512k_stack() {
    const CHILD: &str = "ASH_TYPE_EXPRESSION_SOURCE_512K_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "module::staged_tests::type_expression_real_capture_and_alias_on_a_512k_stack",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        print!("{}", String::from_utf8_lossy(&output.stdout));
        let stderr = String::from_utf8_lossy(&output.stderr);
        eprint!("{stderr}");
        assert!(output.status.success(), "512 KiB child failed");
        assert_eq!(
            stderr
                .matches("type expression source: 42 and final alias dropped")
                .count(),
            2
        );
        assert!(stderr.contains("type expression source: shared loan exact/short/retry"));
        return;
    }
    std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(|| {
            use crate::{
                driver::{compile_staged_graph_for_test, execute},
                parser::G1_CAPTURE_OBSERVER,
                surface::{SurfaceSyntaxCapture, SurfaceTypeKind},
                syntax::MacroOutputNode,
            };
            use std::{cell::RefCell, sync::Arc};

            std::thread_local! {
                static CAPTURE: RefCell<Option<Arc<[MacroOutputNode]>>> = const { RefCell::new(None) };
            }
            fn observe(source: &SourceFile, captures: &[SurfaceSyntaxCapture], _: &SyntaxBudget) {
                let [SurfaceSyntaxCapture::Identifier(name), SurfaceSyntaxCapture::Type(ty)] = captures else {
                    panic!("expected the caller name and Type capture")
                };
                assert_eq!(name.name.text, "result");
                assert_eq!(name.name.introduction, 0);
                assert!(matches!(ty.ty.kind, SurfaceTypeKind::Int));
                assert_eq!(ty.ty.span.source(), source.id());
                let range = ty.ty.span.range();
                assert_eq!(&source.text()[range.start() as usize..range.end() as usize], "Int");
                CAPTURE.with(|slot| {
                    assert!(slot.borrow_mut().replace(Arc::clone(&ty.contents)).is_none());
                });
            }
            for entry in ["keep_main.ash", "twice_main.ash"] {
                let path = Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("tests/fixtures/surface-macros/type-expression-bridge")
                    .join(entry);
                let mut graph = graph_at(&path, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
                let header = graph.syntax_budget.consumed();
                graph.syntax_budget.charge_units(17).unwrap();
                G1_CAPTURE_OBSERVER.set(Some(observe));
                let result = compile_staged_graph_for_test(&mut graph);
                G1_CAPTURE_OBSERVER.set(None);
                let program = result.unwrap();
                let total = graph.syntax_budget.consumed();
                let value = execute(&program).unwrap();
                assert_eq!(value.value_display(), "42");
                assert_eq!(value.type_display(), "Int");
                let alias = CAPTURE.with(|slot| slot.borrow_mut().take().unwrap());
                let weak = Arc::downgrade(&alias);
                drop(program);
                drop(graph);
                assert_eq!(Arc::strong_count(&alias), 1);
                drop(alias);
                assert!(weak.upgrade().is_none());
                eprintln!("type expression source: 42 and final alias dropped");
                if entry == "keep_main.ash" {
                    let mut short = graph_at(&path, BodyMode::Header, total - 1).unwrap();
                    assert_eq!(short.syntax_budget.consumed(), header);
                    short.syntax_budget.charge_units(17).unwrap();
                    G1_CAPTURE_OBSERVER.set(Some(observe));
                    let failure = compile_staged_graph_for_test(&mut short)
                        .expect_err("one short must publish no program");
                    G1_CAPTURE_OBSERVER.set(None);
                    assert_eq!(failure.reason_code(), "internal.resource.syntax-work");
                    assert!(short.syntax_budget.consumed() < total);
                    let alias = CAPTURE.with(|slot| slot.borrow_mut().take().unwrap());
                    let weak = Arc::downgrade(&alias);
                    drop(failure);
                    drop(short);
                    assert_eq!(Arc::strong_count(&alias), 1);
                    drop(alias);
                    assert!(weak.upgrade().is_none());
                    for _ in 0..2 {
                        let mut exact = graph_at(&path, BodyMode::Header, total).unwrap();
                        assert_eq!(exact.syntax_budget.consumed(), header);
                        exact.syntax_budget.charge_units(17).unwrap();
                        G1_CAPTURE_OBSERVER.set(Some(observe));
                        let program = compile_staged_graph_for_test(&mut exact).unwrap();
                        G1_CAPTURE_OBSERVER.set(None);
                        assert_eq!(exact.syntax_budget.consumed(), total);
                        assert_eq!(execute(&program).unwrap().value_display(), "42");
                        let alias = CAPTURE.with(|slot| slot.borrow_mut().take().unwrap());
                        let weak = Arc::downgrade(&alias);
                        drop(program);
                        drop(exact);
                        assert_eq!(Arc::strong_count(&alias), 1);
                        drop(alias);
                        assert!(weak.upgrade().is_none());
                    }
                    eprintln!("type expression source: shared loan exact/short/retry");
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn type_expression_real_composed_depth_on_a_512k_stack() {
    const CHILD: &str = "ASH_TYPE_EXPRESSION_DEPTH_512K_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "module::staged_tests::type_expression_real_composed_depth_on_a_512k_stack",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        print!("{}", String::from_utf8_lossy(&output.stdout));
        let stderr = String::from_utf8_lossy(&output.stderr);
        eprint!("{stderr}");
        assert!(output.status.success(), "512 KiB depth child failed");
        assert!(stderr.contains("type expression depth: adjacent source graphs checked"));
        return;
    }
    std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(|| {
            use crate::{
                driver::{compile_staged_graph_for_test, execute},
                parser::G1_CAPTURE_OBSERVER,
                surface::{SurfaceSyntaxCapture, SurfaceTypeKind},
                syntax::MacroOutputNode,
            };
            use std::{cell::RefCell, sync::Arc};

            std::thread_local! {
                static CAPTURE: RefCell<Option<Arc<[MacroOutputNode]>>> = const { RefCell::new(None) };
            }
            fn observe(_: &SourceFile, captures: &[SurfaceSyntaxCapture], _: &SyntaxBudget) {
                let [SurfaceSyntaxCapture::Identifier(_), SurfaceSyntaxCapture::Type(ty)] = captures else {
                    panic!("expected the source Type capture")
                };
                assert!(matches!(ty.ty.kind, SurfaceTypeKind::Int));
                CAPTURE.with(|slot| {
                    assert!(slot.borrow_mut().replace(Arc::clone(&ty.contents)).is_none());
                });
            }
            for groups in [121usize, 122] {
                let tree = Tree::new();
                tree.write("forms.ash", include_str!("../tests/fixtures/surface-macros/type-expression-bridge/forms.ash"));
                tree.write("helper.ash", include_str!("../tests/fixtures/surface-macros/type-expression-bridge/helper.ash"));
                let annotation = format!("{}Int{}", "(".repeat(groups), ")".repeat(groups));
                let entry = tree.write(
                    "main.ash",
                    &format!("import forms (syntax emit_keep)\nemit_keep result for {annotation}\nmain : Unit -> Int\nmain () = result(())\n"),
                );
                let mut graph = graph_at(&entry, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
                G1_CAPTURE_OBSERVER.set(Some(observe));
                let result = compile_staged_graph_for_test(&mut graph);
                G1_CAPTURE_OBSERVER.set(None);
                let alias = CAPTURE.with(|slot| slot.borrow_mut().take().expect("source capture"));
                match (groups, result) {
                    (121, Ok(program)) => {
                        assert_eq!(execute(&program).unwrap().value_display(), "42");
                        drop(program);
                    }
                    (122, Err(failure)) => {
                        assert_eq!(failure.reason_code(), "internal.resource.structural-depth");
                        drop(failure);
                    }
                    (groups, _) => panic!("unexpected result for {groups} groups"),
                }
                drop(graph);
                let weak = Arc::downgrade(&alias);
                assert_eq!(Arc::strong_count(&alias), 1);
                drop(alias);
                assert!(weak.upgrade().is_none());
            }
            eprintln!("type expression depth: accepted 121, refused 122 after capture");
            eprintln!("type expression depth: adjacent source graphs checked");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn type_deep_source_capture_reaches_host_on_a_512k_stack() {
    const CHILD: &str = "ASH_TYPE_SOURCE_AST_512K_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "module::staged_tests::type_deep_source_capture_reaches_host_on_a_512k_stack",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        print!("{}", String::from_utf8_lossy(&output.stdout));
        let stderr = String::from_utf8_lossy(&output.stderr);
        eprint!("{stderr}");
        assert!(
            output.status.success(),
            "512 KiB child failed: {}",
            output.status
        );
        for marker in [
            "type source stack: matched and retained 124 function layers",
            "type source stack: host parsed capture and program executed 42",
            "type source stack: final capture contents alias dropped",
        ] {
            assert!(stderr.contains(marker), "missing marker {marker}");
        }
        return;
    }

    std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(|| {
            use crate::{
                driver::{compile_staged_graph_for_test, execute},
                parser::G1_CAPTURE_OBSERVER,
                surface::{SurfaceSyntaxCapture, SurfaceTypeKind},
                syntax::{MacroOutputNode, charge_new_type_retention},
            };
            use std::{cell::RefCell, sync::Arc};

            std::thread_local! {
                static CAPTURE: RefCell<Option<Arc<[MacroOutputNode]>>> = const { RefCell::new(None) };
            }
            fn observe(source: &SourceFile, captures: &[SurfaceSyntaxCapture], _: &SyntaxBudget) {
                assert!(source.display_path().ends_with("main.ash"));
                let [SurfaceSyntaxCapture::Type(capture)] = captures else {
                    panic!("expected the source Type capture");
                };
                let mut current = &capture.ty;
                for _ in 0..124 {
                    let SurfaceTypeKind::Function(function) = &current.kind else {
                        panic!("expected a source function layer");
                    };
                    assert!(matches!(function.domain.kind, SurfaceTypeKind::Int));
                    current = &function.codomain;
                }
                assert!(matches!(current.kind, SurfaceTypeKind::Int));
                assert!(current.diagnostic.is_none());
                assert_eq!(current.span.source(), source.id());
                let range = current.span.range();
                assert_eq!(&source.text()[range.start() as usize..range.end() as usize], "Int");
                charge_new_type_retention(capture, 0, &mut SyntaxBudget::default()).unwrap();
                CAPTURE.with(|slot| assert!(slot.borrow_mut().replace(Arc::clone(&capture.contents)).is_none()));
                eprintln!("type source stack: matched and retained 124 function layers");
            }

            let tree = Tree::new();
            tree.write("forms.ash", r#"import @builtin.compiler.syntax as Syntax

pub syntax declaration: (probe_type) $result:type => using expand

expand : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
expand input = match Syntax.capture(input, 0) {
    Syntax.Captured(Syntax.TypeCapture(result)) => parse_result(input, result)
    _ => reject(input)
}

parse_result : (Syntax.Input, Syntax.TypeFragment) -> Syntax.MacroResult ! {Syntax.Ops}
parse_result (input, result) = match Syntax.parse_type(input, Syntax.type_syntax(result)) {
    Syntax.ParsedType(_) => Syntax.Expanded(Syntax.Syntax(Syntax.NoNodes))
    _ => reject(input)
}

reject : Syntax.Input -> Syntax.MacroResult ! {Syntax.Ops}
reject input = Syntax.Rejected(Syntax.MacroDiagnostic("type capture failed", Syntax.invocation_origin(input), Syntax.NoOrigins))
"#);
            let annotation = format!("{}Int", "Int -> ".repeat(124));
            let entry = tree.write(
                "main.ash",
                &format!("import forms (syntax probe_type)\nprobe_type {annotation}\nmain : Unit -> Int\nmain () = 42\n"),
            );
            let mut graph = graph_at(&entry, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
            G1_CAPTURE_OBSERVER.set(Some(observe));
            let result = compile_staged_graph_for_test(&mut graph);
            G1_CAPTURE_OBSERVER.set(None);
            let program = result.unwrap();
            assert_eq!(execute(&program).unwrap().value_display(), "42");
            eprintln!("type source stack: host parsed capture and program executed 42");
            let alias = CAPTURE.with(|slot| slot.borrow_mut().take().expect("source capture observed"));
            let weak = Arc::downgrade(&alias);
            drop(program);
            drop(graph);
            assert_eq!(Arc::strong_count(&alias), 1);
            drop(alias);
            assert!(weak.upgrade().is_none());
            eprintln!("type source stack: final capture contents alias dropped");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn g1_actual_empty_and_literal_only_repetitions_preserve_capture_shapes() {
    use crate::{
        driver::{FileFailure, compile_staged_graph_for_test, execute},
        parser::G1_CAPTURE_OBSERVER,
        surface::{SurfaceSyntaxCapture, SurfaceSyntaxMatcherPart},
    };
    use std::cell::Cell;

    std::thread_local! {
        static SHAPE: Cell<u8> = const { Cell::new(0) };
        static OBSERVED: Cell<bool> = const { Cell::new(false) };
    }
    fn observe(source: &SourceFile, captures: &[SurfaceSyntaxCapture], _: &SyntaxBudget) {
        assert!(source.display_path().ends_with("main.ash"));
        match SHAPE.get() {
            1 => {
                let [SurfaceSyntaxCapture::Repeated(values)] = captures else {
                    panic!("expected empty outer capture");
                };
                assert!(values.values.is_empty());
            }
            2 => assert!(captures.is_empty(), "literal-only repeats create no slot"),
            3 => {
                let [SurfaceSyntaxCapture::Repeated(values)] = captures else {
                    panic!("expected one row");
                };
                let [SurfaceSyntaxCapture::Identifier(value)] = values.values.as_slice() else {
                    panic!("expected one source identifier");
                };
                assert_eq!(value.name.text, "Alpha");
                assert_eq!(value.name.span.source(), source.id());
                assert_eq!(value.origin, value.name.span.into());
            }
            4 => {
                let [
                    SurfaceSyntaxCapture::Repeated(outer),
                    SurfaceSyntaxCapture::Repeated(inner),
                ] = captures
                else {
                    panic!("expected outer and nested capture columns");
                };
                let [SurfaceSyntaxCapture::Identifier(value)] = outer.values.as_slice() else {
                    panic!("expected one outer source identifier");
                };
                assert_eq!(value.name.text, "Alpha");
                assert_eq!(value.name.span.source(), source.id());
                let [SurfaceSyntaxCapture::Repeated(empty)] = inner.values.as_slice() else {
                    panic!("expected an empty nested capture");
                };
                assert!(empty.values.is_empty());
            }
            5 => {
                let [SurfaceSyntaxCapture::Identifier(value)] = captures else {
                    panic!("expected the multiline source identifier");
                };
                assert_eq!(value.name.text, "Alpha");
                assert_eq!(value.name.span.source(), source.id());
                assert_eq!(value.origin, value.name.span.into());
            }
            _ => panic!("unexpected shape"),
        }
        OBSERVED.set(true);
    }
    fn trial(matcher: &str, invocation: &str, shape: u8) {
        let tree = Tree::new();
        tree.write(
            "forms.ash",
            &format!("pub syntax declaration: (sink) {matcher} => {{}}\n"),
        );
        let entry = tree.write(
            "main.ash",
            &format!(
                "import forms (syntax sink)\n{invocation}\nmain : Unit -> Int\nmain () = 42\n"
            ),
        );
        let mut graph = graph_at(&entry, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
        SHAPE.set(shape);
        OBSERVED.set(false);
        G1_CAPTURE_OBSERVER.set(Some(observe));
        let result = compile_staged_graph_for_test(&mut graph);
        G1_CAPTURE_OBSERVER.set(None);
        if shape != 0 {
            let program = result.unwrap();
            assert!(OBSERVED.get());
            if shape == 5 {
                let forms = graph
                    .completed
                    .as_ref()
                    .unwrap()
                    .modules()
                    .iter()
                    .find(|module| module.source().display_path().ends_with("forms.ash"))
                    .unwrap();
                let [header] = forms.surface().syntax_declarations.as_slice() else {
                    panic!("expected the multiline matcher definition");
                };
                let [SurfaceSyntaxMatcherPart::Container(group)] = header.matcher.as_slice() else {
                    panic!("expected the braced matcher");
                };
                assert!(matches!(
                    group.body.as_slice(),
                    [
                        SurfaceSyntaxMatcherPart::LineEnd,
                        SurfaceSyntaxMatcherPart::Capture { .. },
                        SurfaceSyntaxMatcherPart::LineEnd,
                    ]
                ));
            }
            assert_eq!(execute(&program).unwrap().value_display(), "42");
        } else {
            let failure = match result {
                Ok(_) => panic!("expected source matcher refusal"),
                Err(failure) => failure,
            };
            assert!(!OBSERVED.get());
            assert!(
                graph.pending.is_empty() && graph.loaded.is_empty() && graph.completed.is_none()
            );
            let FileFailure::Graph(diagnostic) = &failure else {
                panic!("expected graph failure: {failure:?}");
            };
            let LoadGraphError::Syntax(syntax) = diagnostic.failure() else {
                panic!("expected parser refusal");
            };
            assert!(syntax.source.display_path().ends_with("main.ash"));
            assert!(!syntax.parser.is_empty() && syntax.resource.is_none());
        }
    }

    trial("$( row $item:ident ),*", "sink", 1);
    trial("{ $( item $item:ident ),* }", "sink { }", 1);
    trial(
        "$( row $outer:ident $( item $inner:ident ),* );*",
        "sink row Alpha",
        4,
    );
    trial("$( word ),*", "sink word, word, word", 2);
    trial("$( row $item:ident ),+", "sink row Alpha", 3);
    trial("{\n    $item:ident\n}", "sink {\n    Alpha\n}", 5);
    trial("$( row $item:ident ),+", "sink", 0);
    trial("$( row $item:ident ),*", "sink row Alpha,", 0);
}

#[test]
fn g1_source_header_builder_runs_on_fast_and_ordered_graph_paths() {
    use crate::{
        driver::{compile_staged_graph_for_test, execute},
        lexer::{TokenKind, lex},
        parser::{ConcreteElement, NodeKind, parse},
        surface::SurfaceSyntaxMatcherPart,
    };

    let fast_tree = Tree::new();
    let fast_entry = fast_tree.write(
        "main.ash",
        "pub syntax declaration: (local) ( $value:ident ) => {}\nmain : Unit -> Int\nmain () = 42\n",
    );
    let mut fast = graph_at(&fast_entry, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
    let fast_program = compile_staged_graph_for_test(&mut fast).unwrap();
    let fast_module = fast
        .completed
        .as_ref()
        .unwrap()
        .modules()
        .iter()
        .find(|module| module.source().display_path().ends_with("main.ash"))
        .unwrap();
    let [fast_header] = fast_module.surface().syntax_declarations.as_slice() else {
        panic!("expected the source definition on the fast path");
    };
    assert_eq!(fast_header.name.text, "local");
    assert_eq!(fast_header.name.span.source(), fast_module.source().id());
    assert!(matches!(
        fast_header.matcher.as_slice(),
        [SurfaceSyntaxMatcherPart::Container(_)]
    ));
    assert_eq!(execute(&fast_program).unwrap().value_display(), "42");

    let ordered_tree = Tree::new();
    let forms_text = "pub syntax declaration: (sink) ( $input:ident ) => {\n}\n";
    let forms_source = SourceFile::new("forms.ash", forms_text).unwrap();
    let parsed = parse(lex(&forms_source).unwrap());
    assert!(parsed.parse_diagnostics().is_empty());
    let declaration = parsed
        .root()
        .unwrap()
        .children
        .iter()
        .find_map(|child| match child {
            ConcreteElement::Node(node) if node.kind == NodeKind::SyntaxDeclaration => Some(node),
            _ => None,
        })
        .unwrap();
    assert!(matches!(declaration.children.get(7),
        Some(ConcreteElement::Node(node)) if node.kind == NodeKind::SyntaxMatcherSequence));
    let Some(ConcreteElement::Node(body)) = declaration.children.get(9) else {
        panic!("expected the template body");
    };
    let [
        ConcreteElement::Token(left),
        ConcreteElement::Token(line),
        ConcreteElement::Token(right),
    ] = body.children.as_slice()
    else {
        panic!("expected braces and one logical line end");
    };
    assert_eq!(body.kind, NodeKind::TemplateBody);
    assert_eq!(parsed.tokens()[*left].kind, TokenKind::LeftBrace);
    assert_eq!(parsed.tokens()[*line].kind, TokenKind::LineEnd);
    assert_eq!(parsed.tokens()[*right].kind, TokenKind::RightBrace);
    ordered_tree.write("forms.ash", forms_text);
    let ordered_entry = ordered_tree.write(
        "main.ash",
        "import forms (syntax sink)\npub syntax declaration: (local) ( $value:ident ) => {}\nsink (Alpha)\nmain : Unit -> Int\nmain () = 42\n",
    );
    let mut ordered = graph_at(&ordered_entry, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
    let ordered_program = compile_staged_graph_for_test(&mut ordered).unwrap();
    let forms_module = ordered
        .completed
        .as_ref()
        .unwrap()
        .modules()
        .iter()
        .find(|module| module.source().display_path().ends_with("forms.ash"))
        .unwrap();
    let [imported_header] = forms_module.surface().syntax_declarations.as_slice() else {
        panic!("expected the imported source definition");
    };
    assert!(matches!(
        imported_header.matcher.as_slice(),
        [SurfaceSyntaxMatcherPart::Container(_)]
    ));
    assert!(
        imported_header
            .template_contents
            .as_deref()
            .is_some_and(<[_]>::is_empty)
    );
    let ordered_module = ordered
        .completed
        .as_ref()
        .unwrap()
        .modules()
        .iter()
        .find(|module| module.source().display_path().ends_with("main.ash"))
        .unwrap();
    let [ordered_header] = ordered_module.surface().syntax_declarations.as_slice() else {
        panic!("expected the source definition alongside a real invocation");
    };
    assert_eq!(ordered_header.name.text, "local");
    assert_eq!(
        ordered_header.name.span.source(),
        ordered_module.source().id()
    );
    assert!(matches!(
        ordered_header.matcher.as_slice(),
        [SurfaceSyntaxMatcherPart::Container(_)]
    ));
    assert_eq!(execute(&ordered_program).unwrap().value_display(), "42");
}

#[test]
fn g1_imported_graph_shares_budget_exact_short_and_fresh_retry() {
    use crate::{
        driver::{FileFailure, compile_staged_graph_for_test, execute},
        parser::G1_CAPTURE_OBSERVER,
        surface::SurfaceSyntaxCapture,
    };
    use std::cell::Cell;

    std::thread_local! {
        static AT_CAPTURE: Cell<Option<usize>> = const { Cell::new(None) };
    }

    fn observe(source: &SourceFile, captures: &[SurfaceSyntaxCapture], budget: &SyntaxBudget) {
        assert!(source.display_path().ends_with("g1-source-ident/main.ash"));
        assert_eq!(
            source.text(),
            include_str!("../tests/fixtures/surface-macros/g1-source-ident/main.ash")
        );
        let [
            SurfaceSyntaxCapture::Repeated(outer),
            SurfaceSyntaxCapture::Repeated(inner),
        ] = captures
        else {
            panic!("expected the real grouped captures");
        };
        assert_eq!(outer.values.len(), 3);
        assert_eq!(inner.values.len(), 3);
        AT_CAPTURE.set(Some(budget.consumed()));
    }

    let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/surface-macros/g1-source-ident/main.ash");
    let mut measured = graph_at(&entry, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
    let header_work = measured.syntax_budget.consumed();
    measured.syntax_budget.charge_units(17).unwrap();
    AT_CAPTURE.set(None);
    G1_CAPTURE_OBSERVER.set(Some(observe));
    let measured_result = compile_staged_graph_for_test(&mut measured);
    G1_CAPTURE_OBSERVER.set(None);
    let program = measured_result.unwrap();
    let at_capture = AT_CAPTURE.get().expect("real materializer was reached");
    let total = measured.syntax_budget.consumed();
    assert!(at_capture > header_work + 17 && total > at_capture);
    assert_eq!(execute(&program).unwrap().value_display(), "42");

    for label in ["exact", "retry"] {
        if label == "retry" {
            let mut short = graph_at(&entry, BodyMode::Header, total - 1).unwrap();
            assert_eq!(short.syntax_budget.consumed(), header_work);
            short.syntax_budget.charge_units(17).unwrap();
            AT_CAPTURE.set(None);
            G1_CAPTURE_OBSERVER.set(Some(observe));
            let result = compile_staged_graph_for_test(&mut short);
            G1_CAPTURE_OBSERVER.set(None);
            let failure = match result {
                Ok(_) => panic!("one-short graph must refuse"),
                Err(failure) => failure,
            };
            assert_eq!(AT_CAPTURE.get(), Some(at_capture));
            assert!(short.syntax_budget.consumed() >= at_capture);
            assert!(short.syntax_budget.consumed() <= total - 1);
            assert!(
                short.pending.is_empty() && short.loaded.is_empty() && short.completed.is_none()
            );
            let FileFailure::Graph(diagnostic) = &failure else {
                panic!("expected graph error: {failure:?}");
            };
            let LoadGraphError::Syntax(syntax) = diagnostic.failure() else {
                panic!("expected syntax shortage");
            };
            assert_eq!(
                syntax.resource,
                Some(ResourceFailure::SyntaxWork { limit: total - 1 })
            );
            assert!(syntax.source.display_path().ends_with("main.ash"));
            assert!(syntax.lexical.is_empty() && syntax.parser.is_empty());
        }
        let mut graph = graph_at(&entry, BodyMode::Header, total).unwrap();
        assert_eq!(graph.syntax_budget.consumed(), header_work, "{label}");
        graph.syntax_budget.charge_units(17).unwrap();
        AT_CAPTURE.set(None);
        G1_CAPTURE_OBSERVER.set(Some(observe));
        let result = compile_staged_graph_for_test(&mut graph);
        G1_CAPTURE_OBSERVER.set(None);
        let program = result.unwrap();
        assert_eq!(AT_CAPTURE.get(), Some(at_capture), "{label}");
        assert_eq!(graph.syntax_budget.consumed(), total, "{label}");
        assert_eq!(execute(&program).unwrap().value_display(), "42", "{label}");
    }
}

#[test]
fn declaration_graph_shares_budget_through_host_staging_and_retry() {
    use crate::{
        driver::{FileFailure, compile_staged_graph_for_test, execute},
        eval::machine_test_hooks as hooks,
    };

    fn observe_transfer() {
        assert_eq!(hooks::DECLARATION_CAPTURES.get(), 1);
        assert_eq!(hooks::DECLARATION_UNWRAPS.get(), 1);
        assert_eq!(hooks::TRANSFER_ATTEMPTS.get(), 1);
        assert_eq!(hooks::TRANSFER_FAILURES.get(), 0);
        assert_eq!(hooks::DECLARATION_TRANSFERS_BEFORE_DROP.get(), 1);
        assert_eq!(hooks::TRANSFORMER_DROPS.get(), 1);
        assert_eq!(hooks::ROOT_CLOSES.get(), 1);
    }

    let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("docs/design/macros/fixtures/procedural_declaration/main.ash");
    let mut measured = graph_at(&entry, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
    let header_work = measured.syntax_budget.consumed();
    measured.syntax_budget.charge_units(17).unwrap();
    hooks::reset();
    let program = compile_staged_graph_for_test(&mut measured).unwrap();
    observe_transfer();
    let total = measured.syntax_budget.consumed();
    assert!(total > header_work + 17);
    let observation = execute(&program).unwrap();
    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.type_display(), "Int");

    for label in ["exact", "retry"] {
        let mut graph = graph_at(&entry, BodyMode::Header, total).unwrap();
        assert_eq!(graph.syntax_budget.consumed(), header_work, "{label}");
        graph.syntax_budget.charge_units(17).unwrap();
        hooks::reset();
        let program = compile_staged_graph_for_test(&mut graph).unwrap();
        observe_transfer();
        assert_eq!(graph.syntax_budget.consumed(), total, "{label}");
        let observation = execute(&program).unwrap();
        assert_eq!(observation.value_display(), "42");
        assert_eq!(observation.type_display(), "Int");
        if label == "exact" {
            let mut short = graph_at(&entry, BodyMode::Header, total - 1).unwrap();
            assert_eq!(short.syntax_budget.consumed(), header_work);
            short.syntax_budget.charge_units(17).unwrap();
            hooks::reset();
            let failure = compile_staged_graph_for_test(&mut short)
                .expect_err("one short publishes no compiled program");
            observe_transfer();
            let FileFailure::Graph(diagnostic) = failure else {
                panic!("expected staged syntax refusal: {failure:?}");
            };
            let LoadGraphError::Syntax(failure) = diagnostic.failure() else {
                panic!("expected a syntax resource refusal: {diagnostic:?}");
            };
            assert_eq!(
                failure.resource,
                Some(ResourceFailure::SyntaxWork { limit: total - 1 })
            );
            assert!(short.syntax_budget.consumed() < total);
            assert!(short.pending.is_empty());
            assert!(short.loaded.is_empty());
            assert!(short.completed.is_none());
        }
    }
    hooks::reset();
    eprintln!(
        "real graph shared work: header={header_work}, pre-spent=17, total={total}; exact/short/retry"
    );
}

#[test]
fn type_graph_shares_budget_through_host_staging_and_retry() {
    use crate::{
        driver::{FileFailure, compile_staged_graph_for_test, execute},
        eval::machine_test_hooks as hooks,
    };

    fn observe_transfer() {
        assert_eq!(hooks::TRANSFER_ATTEMPTS.get(), 1);
        assert_eq!(hooks::TRANSFER_FAILURES.get(), 0);
        assert_eq!(hooks::TRANSFORMER_DROPS.get(), 1);
        assert_eq!(hooks::ROOT_CLOSES.get(), 1);
    }

    for path in [
        "tests/fixtures/surface-macros/type-host/main.ash",
        "tests/fixtures/surface-macros/expression-host/main.ash",
    ] {
        let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(path);
        let mut measured = graph_at(&entry, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
        let header_work = measured.syntax_budget.consumed();
        measured.syntax_budget.charge_units(17).unwrap();
        hooks::reset();
        let program = compile_staged_graph_for_test(&mut measured).unwrap();
        observe_transfer();
        let total = measured.syntax_budget.consumed();
        assert!(total > header_work + 17);
        let observation = execute(&program).unwrap();
        assert_eq!(observation.value_display(), "42");
        assert_eq!(observation.type_display(), "Int");

        for label in ["exact", "retry"] {
            let mut graph = graph_at(&entry, BodyMode::Header, total).unwrap();
            assert_eq!(graph.syntax_budget.consumed(), header_work, "{label}");
            graph.syntax_budget.charge_units(17).unwrap();
            hooks::reset();
            let program = compile_staged_graph_for_test(&mut graph).unwrap();
            observe_transfer();
            assert_eq!(graph.syntax_budget.consumed(), total, "{label}");
            assert_eq!(execute(&program).unwrap().value_display(), "42");

            if label == "exact" {
                let mut short = graph_at(&entry, BodyMode::Header, total - 1).unwrap();
                assert_eq!(short.syntax_budget.consumed(), header_work);
                short.syntax_budget.charge_units(17).unwrap();
                hooks::reset();
                let failure = compile_staged_graph_for_test(&mut short)
                    .expect_err("one short publishes no compiled program");
                observe_transfer();
                let FileFailure::Graph(diagnostic) = failure else {
                    panic!("expected a graph refusal: {failure:?}");
                };
                if path.contains("expression-host/") {
                    assert!(matches!(
                        diagnostic.failure(),
                        LoadGraphError::Projection {
                            error: crate::parser::ProjectionError::ResourceLimit(
                                ResourceFailure::SyntaxWork { limit }
                            ),
                            ..
                        } if *limit == total - 1
                    ));
                } else {
                    let LoadGraphError::Syntax(failure) = diagnostic.failure() else {
                        panic!("expected a syntax resource refusal: {diagnostic:?}");
                    };
                    assert_eq!(
                        failure.resource,
                        Some(ResourceFailure::SyntaxWork { limit: total - 1 })
                    );
                }
                assert!(short.syntax_budget.consumed() >= header_work + 17);
                assert!(short.syntax_budget.consumed() < total);
                assert!(short.pending.is_empty());
                assert!(short.loaded.is_empty());
                assert!(short.completed.is_none());
            }
        }
        hooks::reset();
        eprintln!("host graph budget: {path}, pre-spent=17, exact/short/retry");
    }
}

#[test]
fn transformer_pattern_recapture_is_refused_before_generated_template_execution() {
    use crate::{
        driver::{compile_staged_graph_for_test, execute},
        eval::machine_test_hooks as hooks,
    };

    let tree = Tree::new();
    tree.write(
        "helpers.ash",
        "pub syntax declaration: (sink) $name:ident as $pattern:pattern => {\n\
             pub $name : Int -> Int\n\
             $name $pattern = 42\n\
         }\n",
    );
    let legacy = tree.write(
        "legacy.ash",
        "import helpers (syntax sink)\n\
         sink answer as value\n\
         main : Unit -> Int\n\
         main () = answer(42)\n",
    );
    let mut graph = graph_at(&legacy, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
    let program = compile_staged_graph_for_test(&mut graph)
        .expect("legacy Template forwarding of the Pattern compiles");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
    eprintln!("pattern recapture: legacy Template forwarding executed 42");

    let entry = tree.write(
        "main.ash",
        "import forms (syntax dispatch)\n\
         import helpers (syntax sink)\n\
         dispatch sink as answer for value\n\
         main : Unit -> Int\n\
         main () = answer(42)\n",
    );
    for protected in [false, true] {
        let nested = if protected {
            "Syntax.Syntax(Syntax.MoreNodes(Syntax.PatternNode(item, origin), Syntax.NoNodes))"
        } else {
            "Syntax.pattern_syntax(item)"
        };
        tree.write(
            "forms.ash",
            &format!(
                "import @builtin.compiler.syntax as Syntax\n\
                 pub syntax declaration: (dispatch) $target:ident as $name:ident for $pattern:pattern => using expand\n\
                 expand : Syntax.Input -> Syntax.MacroResult ! {{Syntax.Ops}}\n\
                 expand input = {{\n\
                     let origin = Syntax.invocation_origin(input)\n\
                     match (Syntax.capture(input, 0), Syntax.capture(input, 1), Syntax.capture(input, 2), Syntax.make_token(Syntax.As, \"as\")) {{\n\
                         (Syntax.Captured(Syntax.IdentifierCapture(target, target_origin)), Syntax.Captured(Syntax.IdentifierCapture(name, name_origin)), Syntax.Captured(Syntax.PatternCapture(item)), Syntax.MadeToken(as_token)) => {{\n\
                             let nested = {nested}\n\
                             let inner = Syntax.GroupNode(Syntax.Parentheses, nested, origin)\n\
                             let inner = Syntax.Syntax(Syntax.MoreNodes(inner, Syntax.NoNodes))\n\
                             let outer = Syntax.GroupNode(Syntax.Parentheses, inner, origin)\n\
                             let rest = Syntax.MoreNodes(outer, Syntax.NoNodes)\n\
                             let rest = Syntax.MoreNodes(Syntax.TokenNode(as_token, origin), rest)\n\
                             let rest = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), rest)\n\
                             let rest = Syntax.MoreNodes(Syntax.IdentifierNode(target, target_origin), rest)\n\
                             Syntax.Expanded(Syntax.Syntax(rest))\n\
                         }}\n\
                         _ => Syntax.Rejected(Syntax.MacroDiagnostic(\"capture failed\", origin, Syntax.NoOrigins))\n\
                     }}\n\
                 }}\n"
            ),
        );
        let mut graph = graph_at(&entry, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
        hooks::reset();
        let result = compile_staged_graph_for_test(&mut graph);
        assert_eq!(hooks::TRANSFER_ATTEMPTS.get(), 1);
        assert_eq!(hooks::TRANSFER_FAILURES.get(), 0);
        assert_eq!(hooks::TRANSFORMER_DROPS.get(), 1);
        assert_eq!(hooks::ROOT_CLOSES.get(), 1);
        if protected {
            let failure = result.expect_err("generated PatternNode recapture is refused");
            assert_eq!(failure.reason_code(), "internal.projection.malformed-tree");
            assert!(graph.pending.is_empty());
            assert!(graph.loaded.is_empty());
            assert!(graph.completed.is_none());
            eprintln!("pattern recapture: generated PatternNode refused without publication");
        } else {
            let program = result.expect("generated raw Pattern reaches the imported Template");
            assert_eq!(execute(&program).unwrap().value_display(), "42");
            eprintln!("pattern recapture: generated raw Pattern control executed 42");
        }
    }
    hooks::reset();
}

#[test]
fn transformer_type_recapture_is_refused_before_generated_template_execution() {
    use crate::{
        driver::{compile_staged_graph_for_test, execute},
        eval::machine_test_hooks as hooks,
    };

    let tree = Tree::new();
    tree.write(
        "helpers.ash",
        "pub syntax declaration: (sink) $name:ident as $T:type => {\n\
             pub fn $name(value: $T) -> $T {\n\
                 value\n\
             }\n\
         }\n",
    );
    let legacy = tree.write(
        "legacy.ash",
        "import helpers (syntax sink)\n\
         sink answer as Int\n\
         main : Unit -> Int\n\
         main () = answer(42)\n",
    );
    let mut graph = graph_at(&legacy, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
    let program = compile_staged_graph_for_test(&mut graph)
        .expect("legacy Template forwarding with two Type splices compiles");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
    eprintln!("type recapture: legacy Template forwarding executed 42");

    let entry = tree.write(
        "main.ash",
        "import forms (syntax dispatch)\n\
         import helpers (syntax sink)\n\
         dispatch sink as answer for Int\n\
         main : Unit -> Int\n\
         main () = answer(42)\n",
    );
    for protected in [false, true] {
        let nested = if protected {
            "Syntax.Syntax(Syntax.MoreNodes(Syntax.TypeNode(item, origin), Syntax.NoNodes))"
        } else {
            "Syntax.type_syntax(item)"
        };
        tree.write(
            "forms.ash",
            &format!(
                "import @builtin.compiler.syntax as Syntax\n\
                 pub syntax declaration: (dispatch) $target:ident as $name:ident for $T:type => using expand\n\
                 expand : Syntax.Input -> Syntax.MacroResult ! {{Syntax.Ops}}\n\
                 expand input = {{\n\
                     let origin = Syntax.invocation_origin(input)\n\
                     match (Syntax.capture(input, 0), Syntax.capture(input, 1), Syntax.capture(input, 2), Syntax.make_token(Syntax.As, \"as\")) {{\n\
                         (Syntax.Captured(Syntax.IdentifierCapture(target, target_origin)), Syntax.Captured(Syntax.IdentifierCapture(name, name_origin)), Syntax.Captured(Syntax.TypeCapture(item)), Syntax.MadeToken(as_token)) => {{\n\
                             let nested = {nested}\n\
                             let inner = Syntax.GroupNode(Syntax.Parentheses, nested, origin)\n\
                             let inner = Syntax.Syntax(Syntax.MoreNodes(inner, Syntax.NoNodes))\n\
                             let outer = Syntax.GroupNode(Syntax.Parentheses, inner, origin)\n\
                             let rest = Syntax.MoreNodes(outer, Syntax.NoNodes)\n\
                             let rest = Syntax.MoreNodes(Syntax.TokenNode(as_token, origin), rest)\n\
                             let rest = Syntax.MoreNodes(Syntax.IdentifierNode(name, name_origin), rest)\n\
                             let rest = Syntax.MoreNodes(Syntax.IdentifierNode(target, target_origin), rest)\n\
                             Syntax.Expanded(Syntax.Syntax(rest))\n\
                         }}\n\
                         _ => Syntax.Rejected(Syntax.MacroDiagnostic(\"capture failed\", origin, Syntax.NoOrigins))\n\
                     }}\n\
                 }}\n"
            ),
        );
        let mut graph = graph_at(&entry, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
        hooks::reset();
        let result = compile_staged_graph_for_test(&mut graph);
        assert_eq!(hooks::TRANSFER_ATTEMPTS.get(), 1);
        assert_eq!(hooks::TRANSFER_FAILURES.get(), 0);
        assert_eq!(hooks::TRANSFORMER_DROPS.get(), 1);
        assert_eq!(hooks::ROOT_CLOSES.get(), 1);
        if protected {
            let failure = result.expect_err("generated TypeNode recapture is refused");
            assert_eq!(failure.reason_code(), "internal.projection.malformed-tree");
            assert!(graph.pending.is_empty());
            assert!(graph.loaded.is_empty());
            assert!(graph.completed.is_none());
            eprintln!("type recapture: generated TypeNode refused without publication");
        } else {
            let program = result.expect("generated raw Type reaches the imported Template");
            assert_eq!(execute(&program).unwrap().value_display(), "42");
            eprintln!("type recapture: generated raw Type control executed 42");
        }
    }
    hooks::reset();
}

#[test]
fn pattern_graph_transfer_shortage_keeps_injected_teardown_on_a_512k_stack() {
    const CHILD: &str = "ASH_PATTERN_TEARDOWN_512K_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "module::staged_tests::pattern_graph_transfer_shortage_keeps_injected_teardown_on_a_512k_stack",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        print!("{}", String::from_utf8_lossy(&output.stdout));
        let stderr = String::from_utf8_lossy(&output.stderr);
        eprint!("{stderr}");
        assert!(
            output.status.success(),
            "512 KiB child failed: {}",
            output.status
        );
        for marker in [
            "pattern cleanup: actual graph executed 42",
            "pattern cleanup: transfer shortage drained the graph",
            "pattern cleanup: injected teardown retained after primary",
        ] {
            assert!(stderr.contains(marker), "missing marker {marker}");
        }
        return;
    }
    std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(|| {
            use crate::{
                driver::{
                    CompiledProgram, FileFailure, PipelineFailure, compile_staged_graph_for_test,
                    execute,
                },
                eval::{
                    CleanupStatus, ResourceFailureCause, RuntimeFailure, RuntimePhase,
                    RuntimeResource, machine_test_hooks as hooks,
                },
            };

            fn trial(
                entry: &Path,
                limit: usize,
                inject_close: bool,
            ) -> (HeaderGraph, Result<CompiledProgram, FileFailure>) {
                let mut graph = graph_at(entry, BodyMode::Header, limit).unwrap();
                graph.syntax_budget.charge_units(17).unwrap();
                hooks::reset();
                hooks::FAIL_ROOT_CLOSE.set(inject_close);
                let result = compile_staged_graph_for_test(&mut graph);
                (graph, result)
            }

            fn primary(failure: &FileFailure) -> crate::eval::RuntimeFailureReport {
                let Some(PipelineFailure::SyntaxRuntime(failure)) = failure.pipeline_failure()
                else {
                    panic!("expected a syntax runtime failure: {failure:?}");
                };
                let RuntimeFailure::Report(report) = failure.cause() else {
                    panic!("expected structured failure details");
                };
                assert_eq!(
                    report.primary.reason_code(),
                    "internal.resource.syntax-work"
                );
                assert!(report.primary.resource().is_none());
                report
            }

            let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/surface-macros/pattern-host/main.ash");
            let header = graph_at(&entry, BodyMode::Header, SYNTAX_WORK_LIMIT)
                .unwrap()
                .syntax_budget
                .consumed();
            let (measured, result) = trial(&entry, SYNTAX_WORK_LIMIT, false);
            let program = result.expect("the actual Pattern graph compiles");
            let total = measured.syntax_budget.consumed();
            assert_eq!(hooks::TRANSFER_ATTEMPTS.get(), 1);
            assert_eq!(hooks::TRANSFER_FAILURES.get(), 0);
            assert_eq!(hooks::ROOT_CLOSES.get(), 1);
            assert_eq!(hooks::TRANSFORMER_DROPS.get(), 1);
            assert_eq!(execute(&program).unwrap().value_display(), "42");
            drop(program);
            drop(measured);
            eprintln!("pattern cleanup: actual graph executed 42");

            let (mut low, mut high) = (header + 17, total);
            while low < high {
                let mid = low + (high - low) / 2;
                let (_graph, _result) = trial(&entry, mid, false);
                if hooks::TRANSFER_ATTEMPTS.get() == 1 {
                    high = mid;
                } else {
                    low = mid + 1;
                }
            }
            let transfer = low;
            assert!(header + 17 < transfer && transfer < total);

            let (graph, result) = trial(&entry, transfer, false);
            let failure = result.expect_err("transfer shortage publishes no program");
            let native = primary(&failure);
            assert!(native.teardown.is_none());
            assert_eq!(native.cleanup, CleanupStatus::Complete);
            assert_eq!(hooks::TRANSFER_ATTEMPTS.get(), 1);
            assert_eq!(hooks::TRANSFER_FAILURES.get(), 1);
            assert_eq!(hooks::ROOT_CLOSES.get(), 1);
            assert_eq!(hooks::ACTIVE_ROOT_DROPS.get(), 0);
            assert_eq!(hooks::TRANSFORMER_DROPS.get(), 1);
            let native_paid = graph.syntax_budget.consumed();
            assert!(native_paid > header + 17);
            assert!(
                graph.loaded.is_empty() && graph.pending.is_empty() && graph.completed.is_none()
            );
            eprintln!("pattern cleanup: transfer shortage drained the graph");

            let (graph, result) = trial(&entry, transfer, true);
            let failure = result.expect_err("injected teardown shortage publishes no program");
            let report = primary(&failure);
            assert_eq!(report.primary, native.primary);
            let teardown = report
                .teardown
                .expect("the root-close failure remains related");
            assert_eq!(teardown.phase, RuntimePhase::Teardown);
            assert_eq!(teardown.resource, RuntimeResource::EnvironmentDisposal);
            assert_eq!(teardown.cause, ResourceFailureCause::ConfiguredCapacity);
            assert_eq!(report.cleanup, CleanupStatus::Incomplete);
            assert_eq!(hooks::TRANSFER_ATTEMPTS.get(), 1);
            assert_eq!(hooks::TRANSFER_FAILURES.get(), 1);
            assert_eq!(hooks::ROOT_CLOSES.get(), 1);
            assert_eq!(hooks::TRANSFORMER_DROPS.get(), 1);
            assert_eq!(graph.syntax_budget.consumed(), native_paid);
            assert!(
                graph.loaded.is_empty() && graph.pending.is_empty() && graph.completed.is_none()
            );
            for path in ["main.ash", "forms.ash"] {
                assert!(
                    failure
                        .sources()
                        .iter()
                        .any(|source| source.display_path().ends_with(path))
                );
            }
            hooks::reset();
            eprintln!("pattern cleanup: injected teardown retained after primary");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn declaration_graph_resource_failures_close_real_roots_and_keep_injected_teardown() {
    use crate::{
        driver::{CompiledProgram, FileFailure, PipelineFailure, compile_staged_graph_for_test},
        eval::{
            CleanupStatus, ResourceFailureCause, RuntimeFailure, RuntimePhase, RuntimeResource,
            machine_test_hooks as hooks,
        },
    };

    fn trial(
        entry: &Path,
        limit: usize,
        inject_close: bool,
    ) -> (HeaderGraph, Result<CompiledProgram, FileFailure>) {
        let mut graph = graph_at(entry, BodyMode::Header, limit).unwrap();
        graph.syntax_budget.charge_units(17).unwrap();
        hooks::reset();
        hooks::FAIL_ROOT_CLOSE.set(inject_close);
        let result = compile_staged_graph_for_test(&mut graph);
        (graph, result)
    }

    fn primary(failure: &FileFailure) -> crate::eval::RuntimeFailureReport {
        let Some(PipelineFailure::SyntaxRuntime(failure)) = failure.pipeline_failure() else {
            panic!("the host retains its syntax-work refusal: {failure:?}");
        };
        let RuntimeFailure::Report(report) = failure.cause() else {
            panic!("the host refusal has structured details");
        };
        assert_eq!(
            report.primary.reason_code(),
            "internal.resource.syntax-work"
        );
        assert!(report.primary.resource().is_none());
        report
    }

    let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("docs/design/macros/fixtures/procedural_declaration/main.ash");
    let header = graph_at(&entry, BodyMode::Header, SYNTAX_WORK_LIMIT)
        .unwrap()
        .syntax_budget
        .consumed();
    let (measured, result) = trial(&entry, SYNTAX_WORK_LIMIT, false);
    result.unwrap();
    let total = measured.syntax_budget.consumed();
    assert_eq!(hooks::TRANSFER_ATTEMPTS.get(), 1);

    let first_reaching = |observe: fn() -> bool| {
        let (mut low, mut high) = (header + 17, total);
        while low < high {
            let mid = low + (high - low) / 2;
            let (_graph, _result) = trial(&entry, mid, false);
            if observe() {
                high = mid;
            } else {
                low = mid + 1;
            }
        }
        low
    };
    let installed = first_reaching(|| hooks::TRANSFORMER_DROPS.get() == 1);
    let transfer = first_reaching(|| hooks::TRANSFER_ATTEMPTS.get() == 1);
    assert!(header + 17 < installed && installed < transfer && transfer < total);

    let (graph, failure) = trial(&entry, installed - 1, false);
    let failure = failure.expect_err("host-constructor shortage publishes no program");
    let report = primary(&failure);
    assert!(report.teardown.is_none());
    assert_eq!(report.cleanup, CleanupStatus::Complete);
    assert_eq!(hooks::TRANSFORMER_DROPS.get(), 0);
    assert_eq!(hooks::SYNTAX_REQUESTS.get(), 0);
    assert_eq!(hooks::TRANSFER_ATTEMPTS.get(), 0);
    assert_eq!(hooks::ACTIVE_ROOT_DROPS.get(), 0);
    assert_eq!(hooks::ROOT_CLOSES.get(), 0);
    assert!(graph.syntax_budget.consumed() > header + 17);
    assert!(graph.loaded.is_empty() && graph.pending.is_empty() && graph.completed.is_none());

    let (graph, failure) = trial(&entry, transfer - 1, false);
    let failure = failure.expect_err("active service shortage publishes no program");
    let report = primary(&failure);
    assert!(report.teardown.is_none());
    assert_eq!(report.cleanup, CleanupStatus::Complete);
    assert_eq!(hooks::TRANSFORMER_DROPS.get(), 1);
    assert!(hooks::SYNTAX_REQUESTS.get() > 0);
    assert_eq!(hooks::TRANSFER_ATTEMPTS.get(), 0);
    assert_eq!(hooks::ACTIVE_ROOT_DROPS.get(), 1);
    assert_eq!(hooks::ROOT_CLOSES.get(), 0);
    assert!(graph.syntax_budget.consumed() > header + 17);
    assert!(graph.loaded.is_empty() && graph.pending.is_empty() && graph.completed.is_none());

    let (graph, failure) = trial(&entry, transfer, false);
    let failure = failure.expect_err("native transfer shortage publishes no program");
    let native = primary(&failure);
    assert!(native.teardown.is_none());
    assert_eq!(native.cleanup, CleanupStatus::Complete);
    assert_eq!(hooks::TRANSFER_ATTEMPTS.get(), 1);
    assert_eq!(hooks::TRANSFER_FAILURES.get(), 1);
    assert_eq!(hooks::ROOT_CLOSES.get(), 1);
    assert_eq!(hooks::ACTIVE_ROOT_DROPS.get(), 0);
    assert_eq!(hooks::TRANSFORMER_DROPS.get(), 1);
    let native_paid = graph.syntax_budget.consumed();
    assert!(native_paid > header + 17);
    assert!(graph.loaded.is_empty() && graph.pending.is_empty() && graph.completed.is_none());

    let (graph, failure) = trial(&entry, transfer, true);
    let failure = failure.expect_err("transfer and injected teardown shortage publish no program");
    let report = primary(&failure);
    assert_eq!(report.primary, native.primary);
    let teardown = report
        .teardown
        .expect("injected root-close failure remains related");
    assert_eq!(teardown.phase, RuntimePhase::Teardown);
    assert_eq!(teardown.resource, RuntimeResource::EnvironmentDisposal);
    assert_eq!(teardown.cause, ResourceFailureCause::ConfiguredCapacity);
    assert_eq!(report.cleanup, CleanupStatus::Incomplete);
    assert_eq!(hooks::TRANSFER_ATTEMPTS.get(), 1);
    assert_eq!(hooks::TRANSFER_FAILURES.get(), 1);
    assert_eq!(hooks::ROOT_CLOSES.get(), 1);
    assert_eq!(hooks::TRANSFORMER_DROPS.get(), 1);
    assert!(graph.syntax_budget.consumed() > header + 17);
    assert_eq!(graph.syntax_budget.consumed(), native_paid);
    assert!(graph.loaded.is_empty() && graph.pending.is_empty() && graph.completed.is_none());
    assert!(
        failure
            .sources()
            .iter()
            .any(|source| source.display_path().ends_with("main.ash"))
    );
    assert!(
        failure
            .sources()
            .iter()
            .any(|source| source.display_path().ends_with("forms.ash"))
    );
    hooks::reset();
    eprintln!(
        "native constructor, active-root service and transfer refusals clean up completely; separate injected root-close failure retained: header={header}, installed={installed}, transfer={transfer}, total={total}"
    );
}

#[allow(clippy::type_complexity)] // Mirrors the inspected graph's module and edge tuples.
fn graph_shape(
    graph: &ModuleGraph,
) -> Vec<(
    String,
    crate::source::ByteRange,
    Vec<(String, crate::source::ByteRange, bool)>,
)> {
    let names = graph
        .modules()
        .iter()
        .map(|module| (module.id, module.source.display_path().to_owned()))
        .collect::<HashMap<_, _>>();
    graph
        .modules()
        .iter()
        .map(|module| {
            (
                module.source.display_path().to_owned(),
                module.surface.span.range(),
                module
                    .dependencies
                    .iter()
                    .map(|edge| {
                        (
                            names[&edge.target].clone(),
                            edge.import_span.range(),
                            edge.region_service,
                        )
                    })
                    .collect(),
            )
        })
        .collect()
}

fn refusal(entry: &Path, limit: usize) -> (String, String, bool, Option<crate::source::ByteRange>) {
    let outcome = graph_at(entry, BodyMode::Header, limit);
    let (phase, error) = match outcome {
        Err(error) => ("header", error),
        Ok(mut graph) => loop {
            match graph.next_module() {
                Ok(Some(_)) => {}
                Ok(None) => panic!("budget {limit} should be refused"),
                Err(error) => {
                    assert_eq!(graph.syntax_budget.consumed(), limit);
                    break ("body", error);
                }
            }
        },
    };
    let LoadGraphError::Syntax(failure) = error.failure() else {
        panic!("expected a syntax resource refusal: {error:?}");
    };
    assert_eq!(
        failure.resource,
        Some(ResourceFailure::SyntaxWork { limit })
    );
    (
        phase.to_owned(),
        failure.source.display_path().to_owned(),
        failure.import_span.is_some(),
        failure.import_span.map(|span| span.range()),
    )
}

#[test]
fn staged_graph_preserves_census_edges_spans_and_total_syntax_work() {
    let (_tree, entry) = fixture();
    let mut staged = graph_at(&entry, BodyMode::Header, SYNTAX_WORK_LIMIT).unwrap();
    let (paid, bytes) = staged.source_work().unwrap();
    let header_paid = staged.syntax_budget.consumed();
    assert_eq!(
        staged.pending.len(),
        6,
        "two builtins and four source modules"
    );
    assert_eq!(paid.used(), staged.pending.len() + 1);
    assert_eq!(paid.limit(), 10_000 * bytes);
    assert!(
        staged
            .pending
            .back()
            .unwrap()
            .source
            .text()
            .contains("value249")
    );
    while staged.next_module().unwrap().is_some() {}
    let total = staged.syntax_budget.consumed();
    assert!(total > header_paid);
    let staged_graph = staged.completed_graph().unwrap();
    let staged_shape = graph_shape(staged_graph);
    let (complete_work, complete_bytes) = crate::compiler_work::source_work(staged_graph).unwrap();
    assert_eq!(
        (complete_bytes, complete_work.used(), complete_work.limit()),
        (bytes, paid.used(), paid.limit())
    );

    let mut complete = graph_at(&entry, BodyMode::Complete, SYNTAX_WORK_LIMIT).unwrap();
    while complete.next_module().unwrap().is_some() {}
    assert_eq!(complete.syntax_budget.consumed(), total);
    assert_eq!(
        graph_shape(complete.completed_graph().unwrap()),
        staged_shape
    );

    let mut exact = graph_at(&entry, BodyMode::Header, total).unwrap();
    while exact.next_module().unwrap().is_some() {}
    assert_eq!(exact.syntax_budget.consumed(), total);
    let header_failure = refusal(&entry, header_paid - 1);
    assert_eq!(header_failure.0, "header");
    assert!(
        header_failure.2,
        "the final admitted dependency header has an import route"
    );
    let first_body = refusal(&entry, header_paid);
    assert_eq!(first_body.0, "body");
    assert!(first_body.2, "the builtin body's owner import is retained");
    let last_body = refusal(&entry, total - 1);
    assert_eq!(last_body.0, "body");
    assert!(last_body.1.ends_with("entry.ash"));
    assert!(!last_body.2);
    for (limit, expected) in [
        (header_paid - 1, header_failure),
        (header_paid, first_body),
        (total - 1, last_body),
    ] {
        assert_eq!(
            refusal(&entry, limit),
            expected,
            "deterministic budget {limit}"
        );
    }
}
