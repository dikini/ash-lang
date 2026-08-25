use std::{
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{FileFailure, PipelineFailure, RunConfiguration, run_path},
    elaborate::TypeError,
    interface::InterfaceReason,
    module::ModuleRoots,
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct TempTree(PathBuf);

impl TempTree {
    fn create() -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let path =
                std::env::temp_dir().join(format!("ash-module-cli-{}-{id}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("test tree should be creatable: {error}"),
            }
        }
    }

    fn write(&self, relative: &str, text: &str) -> PathBuf {
        let path = self.path(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("fixture parent should be creatable");
        }
        fs::write(&path, text).expect("fixture should be writable");
        path
    }

    fn directory(&self, relative: &str) -> PathBuf {
        let path = self.path(relative);
        fs::create_dir_all(&path).expect("fixture directory should be creatable");
        path
    }

    fn path(&self, relative: &str) -> PathBuf {
        self.0.join(relative)
    }
}

impl Drop for TempTree {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn root_argument(name: &str, path: &Path) -> OsString {
    OsString::from(format!("{name}={}", path.display()))
}

fn ash(arguments: impl IntoIterator<Item = OsString>) -> Output {
    Command::new(env!("CARGO_BIN_EXE_ash"))
        .args(arguments)
        .output()
        .expect("the Ash executable should start")
}

fn canonicalize_source_ids(rendered: &str) -> String {
    let mut source_ids = Vec::new();
    let mut canonical = String::with_capacity(rendered.len());
    for line in rendered.split_inclusive('\n') {
        let Some(marker) = line.find("source ") else {
            canonical.push_str(line);
            continue;
        };
        let id_start = marker + "source ".len();
        let id_end = id_start
            + line[id_start..]
                .bytes()
                .take_while(u8::is_ascii_digit)
                .count();
        let source_id = &line[id_start..id_end];
        let ordinal = source_ids
            .iter()
            .position(|known| *known == source_id)
            .unwrap_or_else(|| {
                source_ids.push(source_id);
                source_ids.len() - 1
            });
        canonical.push_str(&line[..id_start]);
        canonical.push('_');
        canonical.push_str(&ordinal.to_string());
        canonical.push_str(&line[id_end..]);
    }
    canonical
}

#[test]
fn canonical_source_ids_preserve_repeated_source_relationships() {
    let first = concat!(
        "primary: source 41 bytes 0..1: first\n",
        "related: source 7 bytes 2..3: second\n",
        "related: source 41 bytes 4..5: third\n",
    );
    let second = concat!(
        "primary: source 9 bytes 0..1: first\n",
        "related: source 12 bytes 2..3: second\n",
        "related: source 12 bytes 4..5: third\n",
    );

    assert_eq!(
        canonicalize_source_ids(first),
        concat!(
            "primary: source _0 bytes 0..1: first\n",
            "related: source _1 bytes 2..3: second\n",
            "related: source _0 bytes 4..5: third\n",
        )
    );
    assert_ne!(
        canonicalize_source_ids(first),
        canonicalize_source_ids(second),
    );
}

#[test]
fn evaluates_an_entry_through_a_named_absolute_import() {
    let tree = TempTree::create();
    let entry = tree.write(
        "app/entry.ash",
        concat!(
            "import @std.answer as Answer\n",
            "main : Unit -> Int\n",
            "main () = Answer.value(())\n",
        ),
    );
    let standard = tree.directory("standard");
    tree.write(
        "standard/answer.ash",
        "pub value : Unit -> Int\nvalue () = 42\n",
    );

    let output = ash([
        OsString::from("--root"),
        root_argument("std", &standard),
        entry.into_os_string(),
    ]);

    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"42 : Int\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn accepts_repeated_root_options_with_distinct_names() {
    let tree = TempTree::create();
    let entry = tree.write(
        "app/entry.ash",
        concat!(
            "import @left.value as Left\n",
            "import @right.value as Right\n",
            "main : Unit -> Int\n",
            "main () = Left.read(()) + Right.read(())\n",
        ),
    );
    let left = tree.directory("left-root");
    let right = tree.directory("right-root");
    tree.write(
        "left-root/value.ash",
        "pub read : Unit -> Int\nread () = 20\n",
    );
    tree.write(
        "right-root/value.ash",
        "pub read : Unit -> Int\nread () = 22\n",
    );

    let output = ash([
        OsString::from("--root"),
        root_argument("left", &left),
        OsString::from("--root"),
        root_argument("right", &right),
        entry.into_os_string(),
    ]);

    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"42 : Int\n");
    assert!(output.stderr.is_empty());
}

#[test]
fn malformed_root_options_are_usage_failures() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "main : Unit -> Unit\nmain value = value\n");
    let usage = b"usage: ash [--root name=path]... <entry-file>\n";

    for arguments in [
        vec![OsString::from("--root")],
        vec![
            OsString::from("--root"),
            OsString::from("std"),
            entry.clone().into_os_string(),
        ],
        vec![
            OsString::from("--root"),
            OsString::from(format!("={}", tree.0.display())),
            entry.clone().into_os_string(),
        ],
        vec![
            OsString::from("--root"),
            OsString::from("std="),
            entry.clone().into_os_string(),
        ],
    ] {
        let output = ash(arguments);
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
        assert_eq!(output.stderr, usage);
    }
}

#[test]
fn multiple_entry_paths_are_usage_failures() {
    let tree = TempTree::create();
    let first = tree.write("first.ash", "main : Unit -> Int\nmain () = 1\n");
    let second = tree.write("second.ash", "main : Unit -> Int\nmain () = 2\n");

    let output = ash([first.into_os_string(), second.into_os_string()]);

    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    assert_eq!(
        output.stderr,
        b"usage: ash [--root name=path]... <entry-file>\n"
    );
}

#[test]
fn duplicate_root_names_are_invocation_failures() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "main : Unit -> Unit\nmain value = value\n");
    let first = tree.directory("first");
    let second = tree.directory("second");

    let output = ash([
        OsString::from("--root"),
        root_argument("std", &first),
        OsString::from("--root"),
        root_argument("std", &second),
        entry.into_os_string(),
    ]);

    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    assert_eq!(output.stderr, b"invocation.duplicate-root\nroot: std\n");
}

#[test]
fn invalid_root_names_are_invocation_failures() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "main : Unit -> Unit\nmain value = value\n");
    let root = tree.directory("root");

    let output = ash([
        OsString::from("--root"),
        root_argument("Std", &root),
        entry.into_os_string(),
    ]);

    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    assert_eq!(output.stderr, b"invocation.invalid-root-name\nroot: Std\n");
}

#[test]
fn unavailable_root_paths_are_invocation_failures() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "main : Unit -> Unit\nmain value = value\n");
    let unavailable = tree.path("missing-root");

    let output = ash([
        OsString::from("--root"),
        root_argument("std", &unavailable),
        entry.into_os_string(),
    ]);

    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    assert_eq!(
        output.stderr,
        format!(
            "invocation.root-unavailable\npath: {}\nroot: std\nio: NotFound\n",
            unavailable.display()
        )
        .as_bytes()
    );
}

#[test]
fn source_caused_module_failures_use_status_one() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import missing as Missing\n",
            "main : Unit -> Unit\n",
            "main value = value\n",
        ),
    );

    let output = ash([entry.into_os_string()]);

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).expect("diagnostics should be UTF-8");
    assert!(stderr.starts_with("module.not-found\nprimary: source "));
    assert!(stderr.contains(": this import target does not exist\n"));
    assert!(stderr.ends_with(&format!("path: {}\n", tree.path("missing.ash").display())));
}

#[test]
fn imported_input_failures_retain_the_import_cause_and_target_path() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import invalid as Invalid\n",
            "main : Unit -> Unit\n",
            "main value = value\n",
        ),
    );
    let invalid = tree.path("invalid.ash");
    fs::write(&invalid, [0xff, 0xfe]).expect("invalid UTF-8 fixture should be writable");

    let output = ash([entry.into_os_string()]);

    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).expect("diagnostics should be UTF-8");
    assert!(stderr.starts_with("input.invalid-utf8\nprimary: source "));
    assert!(stderr.contains(": this import selected the invalid UTF-8 source\n"));
    assert!(stderr.ends_with(&format!("path: {}\n", invalid.display())));
}

#[test]
fn entry_contract_failures_retain_a_causal_source_label() {
    let tree = TempTree::create();
    let entry = tree.write("entry.ash", "helper : Unit -> Unit\nhelper value = value\n");

    let output = ash([entry.into_os_string()]);

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(
        output
            .stderr
            .starts_with(b"entry.missing-main\nprimary: source ")
    );
    assert!(
        output
            .stderr
            .ends_with(b": this entry module declares no local main\n")
    );
}

#[test]
fn cli_renders_the_structured_interface_diagnostic_without_reclassifying_it() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "interface Render<A> {\nrender : A -> Int\n}\n\n",
            "main : Unit -> Int\n",
            "main () = render true\n",
        ),
    );
    let structured = run_path(RunConfiguration {
        entry: entry.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect_err("the interface obligation should remain unsatisfied");
    let FileFailure::Pipeline(PipelineFailure::Typing(TypeError::Interface(diagnostic))) =
        &structured
    else {
        panic!("the programmatic boundary should retain the structured interface diagnostic");
    };
    assert_eq!(diagnostic.reason, InterfaceReason::Unsatisfied);
    let expected = format!("{}\n", diagnostic.render_plain());

    let output = ash([entry.into_os_string()]);

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let actual = String::from_utf8(output.stderr).expect("diagnostics should be UTF-8");
    assert_eq!(
        canonicalize_source_ids(&actual),
        canonicalize_source_ids(&expected)
    );
}

#[test]
fn cli_renders_a_selected_facade_prerequisite_route_without_reclassifying_it() {
    let tree = TempTree::create();
    let entry = tree.write(
        "entry.ash",
        concat!(
            "import facade as Facade\n",
            "import facade (impl First)\n\n",
            "main : Unit -> Int\n",
            "main () = Facade.first(1)\n",
        ),
    );
    tree.write(
        "facade.ash",
        "pub import dependency (First, first, impl First)\n",
    );
    tree.write(
        "dependency.ash",
        concat!(
            "pub interface First<A> {\n",
            "first : A -> A\n",
            "}\n\n",
            "pub interface Second<A> {\n",
            "second : A -> A\n",
            "}\n\n",
            "pub impl First<Int> where Second<Int> {\n",
            "first value = value\n",
            "}\n",
        ),
    );
    let structured = run_path(RunConfiguration {
        entry: entry.clone(),
        roots: ModuleRoots::empty(),
    })
    .expect_err("the selected implementation prerequisite should remain unsatisfied");
    let FileFailure::Pipeline(PipelineFailure::Typing(TypeError::Interface(diagnostic))) =
        &structured
    else {
        panic!("the programmatic boundary should retain the facade prerequisite diagnostic");
    };
    assert_eq!(diagnostic.reason, InterfaceReason::Unsatisfied);
    assert_eq!(diagnostic.related.len(), 8);
    let expected = format!("{}\n", diagnostic.render_plain());

    let output = ash([entry.into_os_string()]);

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let actual = String::from_utf8(output.stderr).expect("diagnostics should be UTF-8");
    assert_eq!(
        canonicalize_source_ids(&actual),
        canonicalize_source_ids(&expected)
    );
}
