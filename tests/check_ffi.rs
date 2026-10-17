use std::{
    fs,
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    build::{BuildConfiguration, prepare_program},
    check_ffi::{CheckConfiguration, check_path},
    driver::{RunConfiguration, compile_path, run_path},
    module::ModuleRoots,
};

static IDS: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        loop {
            let path = std::env::temp_dir().join(format!(
                "ash-check-ffi-{}-{}",
                std::process::id(),
                IDS.fetch_add(1, Ordering::Relaxed)
            ));
            match fs::create_dir(&path) {
                Ok(()) => {
                    fs::write(path.join("entry.ash"), "import native as Native\nimport constants as Constants\nmain : Unit -> Int\nmain () = Constants.Answer\n").unwrap();
                    fs::write(
                        path.join("native.ash"),
                        r#"import @builtin.foreign as Foreign
pub foreign library C {
    profile "x86_64-unknown-linux-gnu"
    repr CInt = signed(32)
    symbol Abs : Int -> Foreign.Call<Int> {
        name "checked_abs"
        abi (CInt) -> CInt
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
    symbol Stop : Unit -> Foreign.Call<Unit> {
        name "checked_stop"
        abi () -> void
        outcome otherwise {}
    }
}
"#,
                    )
                    .unwrap();
                    fs::write(path.join("constants.ash"), "pub foreign library Constants {\n    profile \"x86_64-unknown-linux-gnu\"\n    repr CInt = signed(32)\n    const Answer : CInt = 42\n}\n").unwrap();
                    fs::write(
                        path.join("binding.h"),
                        "int checked_abs(int);\nvoid checked_stop(void);\n#define ANSWER 42\n",
                    )
                    .unwrap();
                    fs::write(path.join("mapping.json"), serde_json::to_vec_pretty(&serde_json::json!({
                        "version": 1,
                        "declarations": [
                            {"module":"native.ash","library":"C","kind":"representation","member":"CInt","c_type":"int"},
                            {"module":"native.ash","library":"C","kind":"symbol","member":"Abs","c_name":"checked_abs","parameters":["int"],"result":"int"},
                            {"module":"native.ash","library":"C","kind":"symbol","member":"Stop","c_name":"checked_stop","parameters":[],"result":"void"},
                            {"module":"constants.ash","library":"Constants","kind":"representation","member":"CInt","c_type":"int"},
                            {"module":"constants.ash","library":"Constants","kind":"constant","member":"Answer","c_name":"ANSWER"}
                        ]
                    })).unwrap()).unwrap();
                    return Self(path);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("check-ffi fixture: {error}"),
            }
        }
    }

    fn check(&self) -> Output {
        self.command().output().unwrap()
    }

    fn command(&self) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_ash"));
        command
            .arg("check-ffi")
            .arg("--header")
            .arg(self.0.join("binding.h"))
            .arg("--mapping")
            .arg(self.0.join("mapping.json"))
            .arg("--compiler")
            .arg("cc")
            .arg("--output")
            .arg(self.0.join("checks"))
            .arg(self.0.join("entry.ash"));
        command
    }

    fn source(&self) -> RunConfiguration {
        RunConfiguration {
            entry: self.0.join("entry.ash"),
            roots: ModuleRoots::empty(),
        }
    }

    fn configuration(&self) -> CheckConfiguration {
        let mut config = CheckConfiguration::new(
            self.0.join("mapping.json"),
            "cc".into(),
            self.0.join("checks"),
        );
        config.headers.push(self.0.join("binding.h"));
        config
    }

    fn edit_mapping(&self, edit: impl FnOnce(&mut Vec<serde_json::Value>)) {
        let path = self.0.join("mapping.json");
        let mut value: serde_json::Value =
            serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        edit(value["declarations"].as_array_mut().unwrap());
        fs::write(path, serde_json::to_vec_pretty(&value).unwrap()).unwrap();
    }

    fn log(&self) -> String {
        fs::read_to_string(self.0.join("checks/check-ffi.log")).unwrap()
    }
}

#[test]
fn signature_and_constant_mismatches_point_back_to_original_declarations() {
    for (header, member) in [
        (
            "long checked_abs(int);\nvoid checked_stop(void);\n#define ANSWER 42\n",
            "C.Abs",
        ),
        (
            "int checked_abs(int);\nvoid checked_stop(void);\n#define ANSWER 43\n",
            "Constants.Answer",
        ),
        (
            "int checked_abs(int, ...);\nvoid checked_stop(void);\n#define ANSWER 42\n",
            "C.Abs",
        ),
        (
            "int checked_abs();\nvoid checked_stop(void);\n#define ANSWER 42\n",
            "strict-prototypes",
        ),
        (
            "void checked_stop(void);\n#define ANSWER 42\n",
            "checked_abs",
        ),
    ] {
        let fixture = Fixture::new();
        fs::write(fixture.0.join("binding.h"), header).unwrap();
        let output = fixture.check();
        assert!(!output.status.success());
        assert!(String::from_utf8_lossy(&output.stderr).contains("check-ffi.mismatch"));
        assert!(fixture.log().contains(member), "{}", fixture.log());
        let index =
            fs::read_to_string(fixture.0.join("checks/check-ffi-declarations.json")).unwrap();
        assert!(index.contains("constants.ash") && index.contains("native.ash"));
    }
}

#[test]
fn cli_mismatch_json_keeps_defining_source_label_and_log() {
    let fixture = Fixture::new();
    fs::write(
        fixture.0.join("binding.h"),
        "long checked_abs(int);\nvoid checked_stop(void);\n#define ANSWER 42\n",
    )
    .unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_ash"));
    command
        .args(["--message-format", "json", "check-ffi"])
        .arg("--header")
        .arg(fixture.0.join("binding.h"))
        .arg("--mapping")
        .arg(fixture.0.join("mapping.json"))
        .arg("--compiler")
        .arg("cc")
        .arg("--output")
        .arg(fixture.0.join("checks"))
        .arg(fixture.0.join("entry.ash"));
    let output = command.output().unwrap();
    assert!(!output.status.success());
    let value: serde_json::Value = serde_json::from_slice(&output.stderr).unwrap();
    assert_eq!(value["reason"], "check-ffi.mismatch");
    let text = String::from_utf8(output.stderr).unwrap();
    assert!(
        text.contains("foreign_declaration")
            && text.contains("native.ash")
            && text.contains("compiler_log"),
        "{text}"
    );
}

#[test]
fn current_arena_and_buffer_profiles_check_pointer_results_and_void_teardown() {
    for (library_file, owner, bytes) in [
        ("arena.ash", "ArenaState", false),
        ("native_buffer.ash", "State", true),
    ] {
        let fixture = Fixture::new();
        fs::write(
            fixture.0.join("native.ash"),
            fs::read(
                PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                    .join("libraries")
                    .join(library_file),
            )
            .unwrap(),
        )
        .unwrap();
        fs::write(
            fixture.0.join("entry.ash"),
            "import native as Native\nmain : Unit -> Int\nmain () = 42\n",
        )
        .unwrap();
        fs::write(
            fixture.0.join("binding.h"),
            "#include <stdlib.h>\n#include <stdint.h>\n#define ONE 1\n#define MINUS_ONE (-1)\n",
        )
        .unwrap();
        let mut rows = vec![
            serde_json::json!({"module":"native.ash","library":"Memory","kind":"representation","member":"Size","c_type":"size_t"}),
            serde_json::json!({"module":"native.ash","library":"Memory","kind":"representation","member":"Address","c_type":"void *"}),
            serde_json::json!({"module":"native.ash","library":"Memory","kind":"owner","member":owner,"c_type":"void *"}),
            serde_json::json!({"module":"native.ash","library":"Memory","kind":"symbol","member":"Allocate","c_name":"calloc","parameters":["size_t","size_t"],"result":"void *"}),
            serde_json::json!({"module":"native.ash","library":"Memory","kind":"symbol","member":"Free","c_name":"free","parameters":["void *"],"result":"void"}),
        ];
        if bytes {
            rows.extend([
                serde_json::json!({"module":"native.ash","library":"Memory","kind":"representation","member":"Signed","c_type":"int64_t"}),
                serde_json::json!({"module":"native.ash","library":"Memory","kind":"constant","member":"One","c_name":"ONE"}),
                serde_json::json!({"module":"native.ash","library":"Memory","kind":"constant","member":"MinusOne","c_name":"MINUS_ONE"}),
            ]);
        }
        fs::write(
            fixture.0.join("mapping.json"),
            serde_json::to_vec_pretty(&serde_json::json!({"version":1,"declarations":rows}))
                .unwrap(),
        )
        .unwrap();
        let output = fixture.check();
        assert!(
            output.status.success(),
            "{library_file}: {}\n{}",
            String::from_utf8_lossy(&output.stderr),
            fixture.log()
        );
    }
}

#[test]
fn whole_scalar_profile_checks_values_and_refuses_same_width_wrong_category() {
    for c_type in ["int64_t", "double"] {
        let fixture = Fixture::new();
        fs::write(fixture.0.join("native.ash"), r#"import @builtin.foreign as Foreign
pub foreign library C {
    profile "x86_64-unknown-linux-gnu"
    repr I8 = signed(8)
    repr U8 = unsigned(8)
    repr I32 = signed(32)
    repr U32 = unsigned(32)
    repr I64 = signed(64)
    repr U64 = unsigned(64)
    repr Size = size_t
    const Minimum : I64 = -9223372036854775808
    const Maximum : U64 = 18446744073709551615
    symbol All<Before : EffectRow, T, After : EffectRow> : (Int, Int, Int, Int, Int, Int, Int) -> Foreign.Call<Int> {
        name "checked_all"
        abi (I8, U8, I32, U32, I64, U64, Size) -> I64
        operand 0 from 0 scalar
        operand 1 from 1 scalar
        operand 2 from 2 scalar
        operand 3 from 3 scalar
        operand 4 from 4 scalar
        operand 5 from 5 scalar
        operand 6 from 6 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
}
"#).unwrap();
        fs::write(fixture.0.join("binding.h"), format!("#include <stdint.h>\n#include <stddef.h>\n#define MINIMUM INT64_MIN\n#define MAXIMUM UINT64_MAX\n#define ANSWER 42\n{c_type} checked_all(int8_t, uint8_t, int32_t, uint32_t, {c_type}, uint64_t, size_t);\n")).unwrap();
        fixture.edit_mapping(|rows| {
            rows.retain(|row| row["module"] != "native.ash");
            for (member, ty) in [("I8", "int8_t"), ("U8", "uint8_t"), ("I32", "int32_t"), ("U32", "uint32_t"), ("I64", c_type), ("U64", "uint64_t"), ("Size", "size_t")] {
                rows.push(serde_json::json!({"module":"native.ash","library":"C","kind":"representation","member":member,"c_type":ty}));
            }
            for (member, name) in [("Minimum", "MINIMUM"), ("Maximum", "MAXIMUM")] {
                rows.push(serde_json::json!({"module":"native.ash","library":"C","kind":"constant","member":member,"c_name":name}));
            }
            rows.push(serde_json::json!({"module":"native.ash","library":"C","kind":"symbol","member":"All","c_name":"checked_all","parameters":["int8_t","uint8_t","int32_t","uint32_t",c_type,"uint64_t","size_t"],"result":c_type}));
        });
        let output = fixture.check();
        if c_type == "int64_t" {
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
        } else {
            assert!(
                !output.status.success(),
                "matching supplied C signature cannot authenticate a double as Ash signed(64)"
            );
            assert!(fixture.log().contains("C.I64"), "{}", fixture.log());
        }
    }
}

#[test]
fn missing_duplicate_donor_wrong_role_and_c_fragments_refuse_before_compiler() {
    for variant in 0..6 {
        let fixture = Fixture::new();
        if variant == 2 {
            fs::write(
                fixture.0.join("facade.ash"),
                "pub import constants (Answer)\n",
            )
            .unwrap();
            fs::write(fixture.0.join("entry.ash"), "import native as Native\nimport facade as Constants\nmain : Unit -> Int\nmain () = Constants.Answer\n").unwrap();
        }
        fixture.edit_mapping(|rows| match variant {
            0 => {
                rows.pop();
            }
            1 => {
                rows.push(rows[0].clone());
            }
            2 => {
                rows[4]["module"] = "facade.ash".into();
            }
            3 => {
                rows[0]["kind"] = "constant".into();
            }
            4 => {
                rows[0]["c_type"] = "int); _Static_assert(1, \"injected\"); /*".into();
            }
            5 => {
                rows[1]["c_name"] = "checked_stop".into();
            }
            _ => unreachable!(),
        });
        let mut configuration = fixture.configuration();
        configuration.compiler = fixture.0.join("compiler-must-not-run");
        let failure = check_path(fixture.source(), configuration).unwrap_err();
        assert!(
            matches!(
                failure.reason(),
                "check-ffi.missing"
                    | "check-ffi.duplicate"
                    | "check-ffi.declaration"
                    | "check-ffi.c-spelling"
                    | "check-ffi.symbol-name"
            ),
            "{failure:?}"
        );
        assert!(!fixture.0.join("checks").exists());
    }
}

#[test]
fn source_rejection_cannot_expose_a_partial_or_empty_verification_success() {
    let fixture = Fixture::new();
    fs::write(
        fixture.0.join("entry.ash"),
        "import native as Native\nmain : Unit -> Int\nmain () = true\n",
    )
    .unwrap();
    fs::write(fixture.0.join("mapping.json"), "not JSON").unwrap();
    let failure = check_path(fixture.source(), fixture.configuration()).unwrap_err();
    assert!(failure.source_failure().is_some(), "{failure:?}");
    assert!(!fixture.0.join("checks").exists());
}

#[test]
fn optional_check_inputs_cannot_change_runtime_rust_bridge_or_source_facts() {
    let fixture = Fixture::new();
    fs::write(fixture.0.join("entry.ash"), "import @builtin.foreign as Foreign\nimport native as Native\nimport constants as Constants\nmain : Unit -> Foreign.Call<Int> ! {Native.Abs}\nmain () = perform Native.Abs.call Constants.Answer\n").unwrap();
    let program = compile_path(fixture.source()).unwrap();
    let compilation_work = *program.compilation_work();
    let before =
        prepare_program(&program, BuildConfiguration::new(fixture.0.join("program"))).unwrap();
    assert!(before.generated_rust().contains("checked_abs"));
    check_path(fixture.source(), fixture.configuration()).unwrap();
    fixture.edit_mapping(|rows| {
        rows[1]["c_name"] = "some_donor".into();
    });
    assert!(check_path(fixture.source(), fixture.configuration()).is_err());
    fs::remove_dir_all(fixture.0.join("checks")).unwrap();
    fs::remove_file(fixture.0.join("binding.h")).unwrap();
    fs::remove_file(fixture.0.join("mapping.json")).unwrap();
    let after =
        prepare_program(&program, BuildConfiguration::new(fixture.0.join("program"))).unwrap();
    assert_eq!(before.generated_rust(), after.generated_rust());
    assert_eq!(before.preparation_work(), after.preparation_work());
    assert_eq!(program.compilation_work(), &compilation_work);
}

#[test]
fn missing_inputs_unsupported_target_and_cli_duplicates_are_causal() {
    let fixture = Fixture::new();
    let mut target = fixture.configuration();
    target.target = "aarch64-unknown-linux-gnu".into();
    assert_eq!(
        check_path(fixture.source(), target).unwrap_err().reason(),
        "check-ffi.target"
    );
    let mut header = fixture.configuration();
    header.headers[0] = fixture.0.join("absent.h");
    assert_eq!(
        check_path(fixture.source(), header).unwrap_err().reason(),
        "check-ffi.header"
    );
    let mut compiler = fixture.configuration();
    compiler.compiler = fixture.0.join("absent-cc");
    assert_eq!(
        check_path(fixture.source(), compiler).unwrap_err().reason(),
        "check-ffi.compiler"
    );
    let output = Command::new(env!("CARGO_BIN_EXE_ash"))
        .args(["check-ffi", "--mapping", "one", "--mapping", "two"])
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("invocation.usage"));
    assert_eq!(run_path(fixture.source()).unwrap().value_display(), "42");
}

fn sqlite_fixture() -> Fixture {
    let fixture = Fixture::new();
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("libraries/sqlite.ash");
    fs::write(fixture.0.join("sqlite.ash"), fs::read(path).unwrap()).unwrap();
    fs::write(
        fixture.0.join("entry.ash"),
        "import sqlite as SQLite\nmain : Unit -> Int\nmain () = 42\n",
    )
    .unwrap();
    // The retained upstream header checks the current source profile. This does
    // not certify correspondence with a separately supplied runtime binary.
    fs::write(
        fixture.0.join("sqlite3.h"),
        fs::read(
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("foreign-adapter/vendor/sqlite3.h"),
        )
        .unwrap(),
    )
    .unwrap();
    fs::write(fixture.0.join("binding.h"), "#include \"sqlite3.h\"\n#define ASH_RW_CREATE (SQLITE_OPEN_READWRITE | SQLITE_OPEN_CREATE)\n#define ASH_MINUS_ONE (-1)\n").unwrap();
    let mut rows = Vec::new();
    for (kind, member, c_type) in [
        ("representation", "CInt", "int"),
        ("representation", "Address", "void *"),
        ("representation", "InputAddress", "const void *"),
        ("representation", "Destructor", "sqlite3_destructor_type"),
        ("representation", "I64", "sqlite3_int64"),
        ("owner", "ConnectionState", "sqlite3 *"),
        ("owner", "StatementState", "sqlite3_stmt *"),
        ("access", "BlobView", "const void *"),
        ("access", "TextView", "const unsigned char *"),
        ("access", "DiagnosticView", "const char *"),
    ] {
        rows.push(serde_json::json!({"module":"sqlite.ash","library":"NativeSqlite","kind":kind,"member":member,"c_type":c_type}));
    }
    for (kind, member, c_name) in [
        ("constant", "NativeOk", "SQLITE_OK"),
        ("constant", "ReadWriteCreate", "ASH_RW_CREATE"),
        ("constant", "NativeRow", "SQLITE_ROW"),
        ("constant", "NativeDone", "SQLITE_DONE"),
        ("constant", "NegativeOne", "ASH_MINUS_ONE"),
        ("sentinel", "Transient", "SQLITE_TRANSIENT"),
    ] {
        rows.push(serde_json::json!({"module":"sqlite.ash","library":"NativeSqlite","kind":kind,"member":member,"c_name":c_name}));
    }
    for (member, name, parameters, result) in [
        (
            "Prepare",
            "sqlite3_prepare_v2",
            vec![
                "sqlite3 *",
                "const char *",
                "int",
                "sqlite3_stmt **",
                "const char **",
            ],
            "int",
        ),
        ("Step", "sqlite3_step", vec!["sqlite3_stmt *"], "int"),
        (
            "ColumnInt",
            "sqlite3_column_int64",
            vec!["sqlite3_stmt *", "int"],
            "sqlite3_int64",
        ),
        (
            "Finalize",
            "sqlite3_finalize",
            vec!["sqlite3_stmt *"],
            "int",
        ),
        (
            "ColumnCount",
            "sqlite3_column_count",
            vec!["sqlite3_stmt *"],
            "int",
        ),
        (
            "ColumnType",
            "sqlite3_column_type",
            vec!["sqlite3_stmt *", "int"],
            "int",
        ),
        (
            "ColumnBlob",
            "sqlite3_column_blob",
            vec!["sqlite3_stmt *", "int"],
            "const void *",
        ),
        (
            "ColumnBlobExtent",
            "sqlite3_column_bytes",
            vec!["sqlite3_stmt *", "int"],
            "int",
        ),
        (
            "ColumnText",
            "sqlite3_column_text",
            vec!["sqlite3_stmt *", "int"],
            "const unsigned char *",
        ),
        (
            "ColumnTextExtent",
            "sqlite3_column_bytes",
            vec!["sqlite3_stmt *", "int"],
            "int",
        ),
        (
            "ColumnByteLength",
            "sqlite3_column_bytes",
            vec!["sqlite3_stmt *", "int"],
            "int",
        ),
        (
            "ErrorMessage",
            "sqlite3_errmsg",
            vec!["sqlite3 *"],
            "const char *",
        ),
        ("ErrorCode", "sqlite3_errcode", vec!["sqlite3 *"], "int"),
        (
            "BindInt",
            "sqlite3_bind_int64",
            vec!["sqlite3_stmt *", "int", "sqlite3_int64"],
            "int",
        ),
        (
            "BindBlob",
            "sqlite3_bind_blob",
            vec![
                "sqlite3_stmt *",
                "int",
                "const void *",
                "int",
                "sqlite3_destructor_type",
            ],
            "int",
        ),
        (
            "BindText",
            "sqlite3_bind_text",
            vec![
                "sqlite3_stmt *",
                "int",
                "const char *",
                "int",
                "sqlite3_destructor_type",
            ],
            "int",
        ),
        (
            "BindNull",
            "sqlite3_bind_null",
            vec!["sqlite3_stmt *", "int"],
            "int",
        ),
        ("Reset", "sqlite3_reset", vec!["sqlite3_stmt *"], "int"),
        (
            "ClearBindings",
            "sqlite3_clear_bindings",
            vec!["sqlite3_stmt *"],
            "int",
        ),
        ("Initialize", "sqlite3_initialize", vec![], "int"),
        (
            "Open",
            "sqlite3_open_v2",
            vec!["const char *", "sqlite3 **", "int", "const char *"],
            "int",
        ),
        ("Close", "sqlite3_close", vec!["sqlite3 *"], "int"),
    ] {
        rows.push(serde_json::json!({"module":"sqlite.ash","library":"NativeSqlite","kind":"symbol","member":member,"c_name":name,"parameters":parameters,"result":result}));
    }
    fs::write(
        fixture.0.join("mapping.json"),
        serde_json::to_vec_pretty(&serde_json::json!({"version":1,"declarations":rows})).unwrap(),
    )
    .unwrap();
    fixture
}

#[test]
fn current_sqlite_profile_checks_owners_outputs_offset_windows_copy_and_noncallable_sentinel() {
    let fixture = sqlite_fixture();
    let output = fixture.check();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stderr),
        fs::read_to_string(fixture.0.join("checks/check-ffi.log")).unwrap_or_default()
    );
    let source = fs::read_to_string(fixture.0.join("checks/check-ffi.c")).unwrap();
    assert!(source.contains("NativeSqlite.Transient"));
    assert!(source.contains("NativeSqlite.Prepare"));
    assert!(source.contains("NativeSqlite.BlobView"));
    assert!(!fixture.0.join("checks/check-ffi.o").exists());
}

#[test]
fn noncallable_sentinel_wrong_value_and_data_pointer_category_are_rejected() {
    for bad in ["((sqlite3_destructor_type)0)", "((void *)-1)"] {
        let fixture = sqlite_fixture();
        let mut header = fs::read_to_string(fixture.0.join("binding.h")).unwrap();
        header.push_str(&format!("#define BAD_SENTINEL {bad}\n"));
        fs::write(fixture.0.join("binding.h"), header).unwrap();
        fixture.edit_mapping(|rows| {
            rows.iter_mut()
                .find(|row| row["member"] == "Transient")
                .unwrap()["c_name"] = "BAD_SENTINEL".into();
        });
        let output = fixture.check();
        assert!(!output.status.success());
        assert!(
            fixture.log().contains("NativeSqlite.Transient"),
            "{}",
            fixture.log()
        );
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn cli_checks_original_imported_symbols_and_constant_only_library_without_runtime_calls() {
    let fixture = Fixture::new();
    let output = fixture.check();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let generated = fs::read_to_string(fixture.0.join("checks/check-ffi.c")).unwrap();
    assert!(generated.contains("Constants.Answer"));
    assert!(generated.contains("C.Abs"));
    assert!(fixture.0.join("checks/check-ffi.log").is_file());
    assert!(!fixture.0.join("checks/check-ffi.o").exists());
    assert!(!output.stdout.starts_with(b"42"));
}
