#[path = "support/source_buffer.rs"]
mod source_buffer;

use ash::{
    driver::{RunConfiguration, compile_path},
    source::SourceFile,
};

fn check(source: &str) -> Result<(), String> {
    let unique = SourceFile::new("native-buffer typing", "")
        .unwrap()
        .id()
        .value();
    let directory = std::env::temp_dir().join(format!(
        "ash-native-buffer-typing-{}-{unique}",
        std::process::id()
    ));
    std::fs::create_dir(&directory).unwrap();
    let entry = directory.join("entry.ash");
    std::fs::write(&entry, source).unwrap();
    let result = compile_path(RunConfiguration {
        entry,
        roots: source_buffer::roots(&directory),
    });
    std::fs::remove_dir_all(&directory).unwrap();
    result.map(|_| ()).map_err(|error| {
        format!(
            "{}: {:?} {:?}",
            error.reason_code(),
            error.pipeline_failure(),
            error.graph_failure()
        )
    })
}

#[test]
fn allocation_adds_one_outcome_layer_and_discharges_exact_ops() {
    for (result, body) in [
        ("Int", "Buffer.length b"),
        ("Buffer.Outcome<Int>", "Buffer.read (b, 0)"),
        ("Buffer.Outcome<Unit>", "Buffer.write (b, 0, 255)"),
    ] {
        check(&format!(
            "import @ffi.native_buffer as Buffer\nmain : Unit -> Buffer.Outcome<{result}>\nmain () = resource Buffer.Buffer<R> b = 4 {{\n{body}\n}}\n"
        ))
        .unwrap();
    }
}

#[test]
fn cell_and_buffer_imports_select_distinct_scoped_providers() {
    check("import @builtin.cell as Cell\nimport @ffi.native_buffer as Buffer\nmain : Unit -> Buffer.Outcome<Int>\nmain () = resource cell<S> c = 42 {\nresource Buffer.Buffer<R> b = 4 {\nCell.read c + Buffer.length b\n}\n}\n").unwrap();
}

#[test]
fn source_implementation_cannot_supply_resource_provider() {
    let error = check("import @ffi.native_buffer as Buffer\nimpl<R> Buffer.Provider<Buffer.Buffer<R>> {\nlength b = 0\nread pair = Buffer.Failure Buffer.InvalidIndex\nwrite triple = Buffer.Failure Buffer.InvalidIndex\n}\nmain : Unit -> Int\nmain () = 42\n").unwrap_err();
    assert!(error.contains("SealedProvider"), "{error}");
}

#[test]
fn acquisition_result_cannot_omit_its_outcome_wrapper() {
    let error = check("import @ffi.native_buffer as Buffer\nmain : Unit -> Int\nmain () = resource Buffer.Buffer<R> b = 4 {\n42\n}\n").unwrap_err();
    assert!(error.contains("DefinitionResult"), "{error}");
}

#[test]
fn ordinary_results_and_errors_are_constructible_and_exhaustive() {
    check("import @ffi.native_buffer as Buffer\nmain : Unit -> Int\nmain () = match Buffer.Success 42 {\nBuffer.Success(value) => value\nBuffer.Failure(error) => match error {\nBuffer.InvalidLength => 0\nBuffer.AllocationFailed => 1\nBuffer.InvalidIndex => 2\nBuffer.InvalidByte => 3\n}\n}\n").unwrap();
}

#[test]
fn lexical_evidence_cannot_fabricate_resource_provider() {
    let error = check("import @ffi.native_buffer as Buffer\nmain : Unit -> Buffer.Outcome<Int>\nmain () = resource Buffer.Buffer<R> b = 4 {\nwith Buffer.Provider<Buffer.Buffer<R>> {\nlength b = 0\nread pair = Buffer.Failure Buffer.InvalidIndex\nwrite triple = Buffer.Failure Buffer.InvalidIndex\n}\n42\n}\n").unwrap_err();
    assert!(error.contains("SealedProvider"), "{error}");
}

#[test]
fn native_length_and_operation_domains_are_exact() {
    for (initializer, body) in [
        ("true", "42"),
        ("4", "Buffer.read b"),
        ("4", "Buffer.write (b, 0)"),
        ("4", "Buffer.length (b, 0)"),
    ] {
        let error = check(&format!("import @ffi.native_buffer as Buffer\nmain : Unit -> Buffer.Outcome<Int>\nmain () = resource Buffer.Buffer<R> b = {initializer} {{\n{body}\n}}\n")).unwrap_err();
        assert!(
            error.contains("Mismatch")
                || error.contains("Argument")
                || error.contains("ResourceEscape"),
            "{error}"
        );
    }
}

#[test]
fn native_handle_and_capturing_closure_cannot_escape() {
    for (result, body) in [
        ("Unit", "b"),
        (
            "Unit -> Int",
            "let action : Unit -> Int = fn(ignored) {\nlet retained = b\n42\n}\naction",
        ),
    ] {
        let annotation = format!("main : Unit -> Buffer.Outcome<{result}>\nmain ()");
        let error = check(&format!("import @ffi.native_buffer as Buffer\n{annotation} = resource Buffer.Buffer<R> b = 4 {{\n{body}\n}}\n")).unwrap_err();
        assert!(error.contains("ResourceEscape"), "{error}");
    }
}

#[test]
fn outcome_projection_preserves_outer_captures() {
    let source = "import @builtin.cell as Cell\nimport @ffi.native_buffer as Buffer\nmain : Unit -> (Unit -> Int)\nmain () = resource cell<S> c = 42 {\nmatch resource Buffer.Buffer<R> b = 4 {\nlet action : Unit -> Int = fn(ignored) {\nlet retained = c\n42\n}\naction\n} {\nBuffer.Success(action) => action\nBuffer.Failure(error) => fn(ignored) {\n0\n}\n}\n}\n";
    let error = check(source).unwrap_err();
    assert!(error.contains("ResourceEscape"), "{error}");
}

#[test]
fn allocation_failure_branch_cannot_export_an_outer_capture() {
    for body in ["free", "loop ()"] {
        let source = format!(
            "import @builtin.cell as Cell\nimport @ffi.native_buffer as Buffer\nfree : Unit -> Int\nfree () = 0\nloop : Unit -> (Unit -> Int)\nloop () = loop ()\nmain : Unit -> (Unit -> Int)\nmain () = resource cell<S> c = 42 {{\nmatch resource Buffer.Buffer<R> b = 0 {{\n{body}\n}} {{\nBuffer.Success(action) => action\nBuffer.Failure(error) => fn(ignored) {{\nlet retained = c\n42\n}}\n}}\n}}\n"
        );
        let error = check(&source).unwrap_err();
        assert!(error.contains("ResourceEscape"), "{error}");
    }
}

#[test]
fn allocation_failure_reaches_suffix_even_when_successful_body_diverges() {
    let source = "import @builtin.cell as Cell\nimport @ffi.native_buffer as Buffer\neffect Send {\nsend : (Unit -> Int) -> Unit\n}\nloop : Unit -> Int\nloop () = loop ()\nmain : Unit -> Int\nmain () = handle (resource cell<S> c = 42 {\nlet ignored = resource Buffer.Buffer<R> b = 0 {\nloop ()\n}\nlet capture : Unit -> Int = fn(ignored) {\nlet retained = c\n42\n}\nlet sent = perform Send.send capture\n42\n}) with Send {\nsend capture => resume ()\n}\n";
    let error = check(source).unwrap_err();
    assert!(error.contains("ResourceEscape"), "{error}");
    let before_acquisition = source.replace("b = 0 {\nloop ()", "b = (loop ()) {\n42");
    check(&before_acquisition).unwrap();
}

#[test]
fn restored_native_success_projection_preserves_resumed_capture() {
    for body in ["let held = c\n42", "42"] {
        let source = format!(
            "import @builtin.cell as Cell\nimport @ffi.native_buffer as Buffer\neffect Ask {{\nask : Unit -> (Unit -> Int)\n}}\neffect Send {{\nsend : (Unit -> Int) -> Unit\n}}\nmain : Unit -> Int\nmain () = handle (handle ({{\nlet wrapped = resource Buffer.Buffer<R> b = 4 {{\nperform Ask.ask ()\n}}\nmatch wrapped {{\nBuffer.Success(later) => {{\nlet sent = perform Send.send later\n42\n}}\nBuffer.Failure(error) => 42\n}}\n}}) with Ask {{\nask ignored => resource cell<S> c = 41 {{\nlet later : Unit -> Int = fn(ignored) {{\n{body}\n}}\nresume later\n}}\n}}) with Send {{\nsend later => resume ()\n}}\n"
        );
        let result = check(&source);
        if body.starts_with("let") {
            let error = result.unwrap_err();
            assert!(error.contains("ResourceEscape"), "{error}");
        } else {
            result.unwrap();
        }
    }
}
