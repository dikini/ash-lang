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
