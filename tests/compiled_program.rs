use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{EntryReason, PipelineFailure, RunConfiguration, compile_path, execute, run_path},
    module::ModuleRoots,
    types::Type,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct SourceTree(PathBuf);

impl SourceTree {
    fn new() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("ash-compiled-program-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("compiled-program fixture directory: {error}"),
            }
        }
    }

    fn write(&self, name: &str, source: &str) -> PathBuf {
        let path = self.0.join(name);
        fs::write(&path, source).expect("compiled-program fixture source");
        path
    }

    fn configuration(&self) -> RunConfiguration {
        RunConfiguration {
            entry: self.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        }
    }
}

impl Drop for SourceTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn compiled_pure_program_runs_after_source_replacement_without_new_compilation_work() {
    let tree = SourceTree::new();
    tree.write("entry.ash", "main : Unit -> Int\nmain () = 42\n");
    let original = run_path(tree.configuration()).expect("original source executes");
    let compiled = compile_path(tree.configuration()).expect("source compiles");
    assert_eq!(compiled.ty(), &Type::Int);
    assert_eq!(compiled.type_display(), original.type_display());
    let mut retained_work = *original.compilation_work();
    // Reusable compilation retains one record and one shared source handle for
    // this single-module graph; ordinary run_path retains neither.
    retained_work.source_checking.as_mut().unwrap().used += 2;
    assert_eq!(compiled.compilation_work(), &retained_work);

    tree.write("entry.ash", "this replacement is not an Ash program\n");
    for _ in 0..3 {
        let observation = execute(&compiled).expect("execution needs only checked Core");
        assert_eq!(observation.value_display(), "42");
        assert_eq!(observation.ty(), compiled.ty());
        assert_eq!(observation.compilation_work(), compiled.compilation_work());
    }
    assert!(run_path(tree.configuration()).is_err());
}

#[test]
fn compiled_imported_cell_program_recreates_mutable_activations_without_source_files() {
    let tree = SourceTree::new();
    tree.write(
        "helper.ash",
        concat!(
            "import @builtin.cell as Cell\n",
            "pub advance<R> : Cell.Handle<R> -> Int ! {Cell.Ops<R>} where Cell.Provider<R>\n",
            "advance value = {\n",
            "    let previous = Cell.read value\n",
            "    let _ = Cell.write (value, previous + 1)\n",
            "    Cell.read value\n",
            "}\n",
        ),
    );
    tree.write(
        "entry.ash",
        concat!(
            "import @builtin.cell as Cell\n",
            "import helper (advance)\n",
            "main : Unit -> Int\n",
            "main () = resource cell<R> value = 41 {\n",
            "    advance value\n",
            "}\n",
        ),
    );
    let compiled = compile_path(tree.configuration()).expect("imported resource program compiles");
    let work = *compiled.compilation_work();
    fs::remove_dir_all(&tree.0).expect("remove the complete source graph");

    for _ in 0..3 {
        let observation = execute(&compiled).expect("each execution owns a fresh cell");
        assert_eq!(observation.value_display(), "42");
        assert_eq!(observation.ty(), &Type::Int);
        assert_eq!(observation.compilation_work(), &work);
    }
    assert_eq!(compiled.compilation_work(), &work);
}

#[test]
fn compilation_preserves_outstanding_entry_effect_rejection_and_source_context() {
    let tree = SourceTree::new();
    tree.write(
        "entry.ash",
        concat!(
            "effect Ask {\n    ask : Unit -> Int\n}\n",
            "main : Unit -> Int ! {Ask}\n",
            "main () = perform Ask.ask ()\n",
        ),
    );
    let compiled_failure =
        compile_path(tree.configuration()).expect_err("main remains effect-free");
    let run_failure = run_path(tree.configuration()).expect_err("entry checking is unchanged");
    assert!(matches!(
        compiled_failure.pipeline_failure(),
        Some(PipelineFailure::Entry(failure)) if failure.reason() == EntryReason::MainEffects
    ));
    assert_eq!(
        compiled_failure.sources().len(),
        run_failure.sources().len()
    );
    assert!(!compiled_failure.sources().is_empty());
    assert_eq!(
        compiled_failure.compilation_work(),
        run_failure.compilation_work()
    );
}
