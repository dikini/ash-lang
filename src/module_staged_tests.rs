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
            fn observe(source: &SourceFile, captures: &[SurfaceSyntaxCapture], budget: &SyntaxBudget) {
                assert!(source.display_path().ends_with("main.ash"));
                let [SurfaceSyntaxCapture::Repeated(root)] = captures else {
                    panic!("expected one actual repeated capture");
                };
                let alias = Arc::clone(root);
                assert!(Arc::ptr_eq(root, &alias));
                let mut value = &captures[0];
                for _ in 0..127 {
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
                eprintln!("g1 stack: matched and materialized 127 on the real graph");
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
            assert!(matches!(syntax.resource, Some(ResourceFailure::SyntaxWork { .. })));
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
