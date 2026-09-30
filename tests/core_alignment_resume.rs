use std::path::Path;

use ash::{
    driver::{FileFailure, Observation, RunConfiguration, run_path},
    module::ModuleRoots,
    source::SourceFile,
};

fn run_fixture(name: &str) -> Result<Observation, FileFailure> {
    run_path(RunConfiguration {
        entry: Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("docs/design/direct-effects/one-shot/fixtures")
            .join(name),
        roots: ModuleRoots::empty(),
    })
}

#[test]
fn direct_effectful_resume_operand_preserves_the_outside_owner() {
    let observation = run_fixture("open-owner-resume-operand.ash")
        .expect("the resume argument must execute before consuming the outside owner");
    assert_eq!(observation.value_display(), "17");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn bound_effectful_resume_operand_preserves_the_outside_owner() {
    let observation = run_fixture("open-owner-resume.ash")
        .expect("binding the argument must preserve the same outside owner");
    assert_eq!(observation.value_display(), "17");
    assert_eq!(observation.type_display(), "Int");
}

#[test]
fn nested_discard_cannot_abandon_the_outside_owner() {
    let failure = run_fixture("open-owner-discard.ash")
        .expect_err("discard must reject an unconsumed outside owner");
    assert!(failure.is_source_rejection());
    assert_eq!(failure.reason_code(), "effect.discard-unsafe");
}

#[test]
fn local_operand_handler_retains_nonempty_continuation_output() {
    for operand in [
        "resume (perform Operand.pong ())",
        "{\nlet ignored = perform Operand.pong ()\nresume ()\n}",
    ] {
        let source = format!(
            "effect Selected {{\nask : Unit -> Unit\n}}\n\
             effect Operand {{\npong : Unit -> Unit\n}}\n\
             effect Output {{\ntick : Unit -> Unit\n}}\n\
             main : Unit -> Int\nmain () = handle (handle {{\n\
             let ignored = perform Selected.ask ()\n\
             let ignored = perform Output.tick ()\n17\n\
             }} with Selected {{\nask ignored => handle ({operand}) with Operand {{\n\
             pong ignored => resume ()\n}}\n\
             }}) with Output {{\ntick ignored => resume ()\n}}\n"
        );
        let id = SourceFile::new("resume-output", "").unwrap().id().value();
        let path = std::env::temp_dir().join(format!(
            "ash-core-alignment-resume-output-{}-{id}.ash",
            std::process::id()
        ));
        std::fs::write(&path, source).unwrap();
        let result = run_path(RunConfiguration {
            entry: path.clone(),
            roots: ModuleRoots::empty(),
        });
        std::fs::remove_file(path).unwrap();
        let observation = result.expect("both local handlers must retain the continuation output");
        assert_eq!(observation.value_display(), "17");
        assert_eq!(observation.type_display(), "Int");
    }
}

#[test]
fn imported_summary_retains_locally_handled_resume_operand_and_output() {
    let id = SourceFile::new("resume-import", "").unwrap().id().value();
    let directory = std::env::temp_dir().join(format!(
        "ash-core-alignment-resume-import-{}-{id}",
        std::process::id()
    ));
    std::fs::create_dir(&directory).unwrap();
    std::fs::write(
        directory.join("helper.ash"),
        concat!(
            "effect Selected {\nask : Unit -> Unit\n}\n",
            "effect Operand {\npong : Unit -> Unit\n}\n",
            "pub effect Output {\ntick : Unit -> Unit\n}\n",
            "pub run : Unit -> Int ! {Output}\nrun () = handle {\n",
            "let ignored = perform Selected.ask ()\n",
            "let ignored = perform Output.tick ()\n17\n",
            "} with Selected {\nask ignored => ",
            "handle (resume (perform Operand.pong ())) with Operand {\n",
            "pong ignored => resume ()\n}\n}\n",
        ),
    )
    .unwrap();
    let entry = directory.join("entry.ash");
    std::fs::write(
        &entry,
        concat!(
            "import helper (run, Output)\n",
            "main : Unit -> Int\nmain () = handle (run ()) with Output {\n",
            "tick ignored => resume ()\n}\n",
        ),
    )
    .unwrap();
    let result = run_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    });
    std::fs::remove_dir_all(directory).unwrap();
    let observation = result.expect("checked summaries must preserve the output across imports");
    assert_eq!(observation.value_display(), "17");
    assert_eq!(observation.type_display(), "Int");
}
