use ash::{
    driver::{RunConfiguration, run_path},
    module::ModuleRoots,
    source::SourceFile,
};

fn check(source: &str) -> Result<String, String> {
    let path = std::env::temp_dir().join(format!(
        "ash-cleanup-partial-acquisition-{}-{}.ash",
        std::process::id(),
        SourceFile::new("cleanup", "").unwrap().id().value()
    ));
    std::fs::write(&path, source).unwrap();
    let result = run_path(RunConfiguration {
        entry: path.clone(),
        roots: ModuleRoots::empty(),
    });
    std::fs::remove_file(path).unwrap();
    result
        .map(|value| value.value_display())
        .map_err(|error| error.reason_code())
}

#[test]
fn abandoned_initializer_closes_only_previously_acquired_cleanup() {
    assert_eq!(
        check(
            r#"import @builtin.cell as Cell
effect Stop {
    stop : Unit -> Unit
}
main : Unit -> Int
main () = resource cell<R> trace = 0 {
    let result = handle (cleanup fn(ignored) {
        Cell.write (trace, (Cell.read trace) * 10 + 2)
    } {
        let unfinished = cleanup ({
            let entered = Cell.write (trace, (Cell.read trace) * 10 + 1)
            let stopped = perform Stop.stop ()
            let suffix = Cell.write (trace, (Cell.read trace) * 10 + 4)
            fn(ignored) {
                Cell.write (trace, (Cell.read trace) * 10 + 5)
            }
        }) {
            Cell.write (trace, (Cell.read trace) * 10 + 6)
        }
        let suffix = Cell.write (trace, (Cell.read trace) * 10 + 8)
        42
    }) with Stop {
        stop ignored => {
            let done = discard
            let continued = Cell.write (trace, (Cell.read trace) * 10 + 3)
            7
        }
    }
    result * 1000 + Cell.read trace
}
"#
        ),
        Ok("7123".into())
    );
}
