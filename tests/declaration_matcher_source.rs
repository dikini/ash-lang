use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{RunConfiguration, compile_path, execute},
    lexer::lex,
    module::{LoadGraphError, ModuleRoots},
    parser::{
        InternalReason, ParseReason, ProjectionError, ResourceFailure, STRUCTURAL_DEPTH_LIMIT,
        parse, project_module,
    },
    source::SourceFile,
};

#[test]
fn imported_grouped_repetitions_accept_an_empty_template() {
    let entry = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/surface-macros/g1-source-ident/main.ash");
    let program = compile_path(RunConfiguration {
        entry,
        roots: ModuleRoots::empty(),
    })
    .expect("the imported grouped matcher accepts ordered, ragged source identifiers");
    assert_eq!(execute(&program).unwrap().value_display(), "42");
}

#[test]
fn rejects_the_fixed_repetition_separator_follow_ambiguity() {
    let text = include_str!("../docs/design/macros/fixtures/captures/ambiguous_forms.ash");
    let source = SourceFile::new("ambiguous_forms.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(tree.lexical_diagnostics().is_empty());
    assert_eq!(tree.resource_failure(), None);
    let following_separator = text.rfind(", tail").unwrap();
    assert!(
        tree.parse_diagnostics().iter().any(|diagnostic| {
            diagnostic.reason == ParseReason::ExpectedForm
                && diagnostic.primary.span().range().start() as usize == following_separator
        }),
        "{:?}",
        tree.parse_diagnostics()
    );
}

#[test]
fn source_definitions_check_repeat_follow_through_nullable_parts() {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-g1-follow-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory).unwrap();
    struct Cleanup(PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    let _cleanup = Cleanup(directory.clone());
    let entry = directory.join("main.ash");
    fs::write(
        &entry,
        "import forms (syntax sink)\nmain : Unit -> Int\nmain () = 42\n",
    )
    .unwrap();

    for (matcher, accepted) in [
        ("$( $name:ident )* tail", false),
        ("$( item )* $( other )* item", false),
        ("$( item ) ,+ , tail", false),
        ("$( item ) \"a\"* \"a\"", false),
        ("$name:ident ( $name:ident )", false),
        ("$( $name:ident )* $last:ident", false),
        ("$( row $( item $x:ident );* );*", false),
        ("$( item $( item $x:ident )* )*", false),
        ("$( row $( item $x:ident )* )* item", false),
        ("$( item ) ,+ item", true),
        ("$( item ) ,* ; tail", true),
        ("$( item ) \"a\"* \"b\"", true),
        ("$( row $( item $x:ident ),* );*", true),
        ("$( row $( item $x:ident )* )*", true),
        ("$( row ( $( item $x:ident )* ) )* item", true),
    ] {
        fs::write(
            directory.join("forms.ash"),
            format!("pub syntax declaration: (sink) {matcher} => {{}}\n"),
        )
        .unwrap();
        let result = compile_path(RunConfiguration {
            entry: entry.clone(),
            roots: ModuleRoots::empty(),
        });
        if accepted {
            let program = result.unwrap_or_else(|error| panic!("{matcher}: {error:?}"));
            assert_eq!(execute(&program).unwrap().value_display(), "42");
        } else {
            let failure = match result {
                Ok(_) => panic!("accepted {matcher}"),
                Err(failure) => failure,
            };
            let ash::driver::FileFailure::Graph(graph) = failure else {
                panic!("{matcher}: {failure:?}");
            };
            let LoadGraphError::Syntax(syntax) = graph.failure() else {
                panic!("{matcher}: {graph:?}");
            };
            assert!(syntax.source.display_path().ends_with("forms.ash"));
            assert!(!syntax.parser.is_empty(), "{matcher}");
            assert!(syntax.resource.is_none(), "{matcher}");
        }
    }
}

#[test]
fn token_only_parse_does_not_admit_an_undecidable_extended_header() {
    let text = "pub syntax declaration: (sink) $( item ) \"a\"* \"a\" => {}\n";
    let source = SourceFile::new("token-only.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    assert!(matches!(
        project_module(&source, &tree),
        Err(ProjectionError::MalformedTree(
            InternalReason::UnexpectedShape
        ))
    ));
}

#[test]
fn live_repeat_lookahead_counts_the_existing_invocation_layer() {
    std::thread::Builder::new()
        .stack_size(8 * 1024 * 1024)
        .spawn(|| {
            let directory =
                std::env::temp_dir().join(format!("ash-g1-depth-{}", std::process::id()));
            fs::create_dir(&directory).unwrap();
            struct Cleanup(PathBuf);
            impl Drop for Cleanup {
                fn drop(&mut self) {
                    let _ = fs::remove_dir_all(&self.0);
                }
            }
            let _cleanup = Cleanup(directory.clone());
            let entry = directory.join("main.ash");
            for depth in [127usize, 128, 129] {
                let mut matcher = format!("{}$value:ident", "$(".repeat(depth));
                let mut invocation = String::from("sink Alpha");
                for marker in (0..depth).rev() {
                    matcher.push_str(&format!(" {marker} )+"));
                    invocation.push_str(&format!(" {marker}"));
                }
                fs::write(&entry, format!(
                    "import forms (syntax sink)\n{invocation}\nmain : Unit -> Int\nmain () = 42\n"
                )).unwrap();
                fs::write(
                    directory.join("forms.ash"),
                    format!("pub syntax declaration: (sink) {matcher} => {{}}\n"),
                )
                .unwrap();
                let result = compile_path(RunConfiguration {
                    entry: entry.clone(),
                    roots: ModuleRoots::empty(),
                });
                if depth == 127 {
                    let program =
                        result.unwrap_or_else(|failure| panic!("depth {depth}: {failure:?}"));
                    assert_eq!(execute(&program).unwrap().value_display(), "42");
                } else {
                    let failure = match result {
                        Ok(_) => panic!("accepted depth {depth}"),
                        Err(failure) => failure,
                    };
                    let ash::driver::FileFailure::Graph(graph) = failure else {
                        panic!("{depth}: {failure:?}");
                    };
                    let LoadGraphError::Syntax(syntax) = graph.failure() else {
                        panic!("{depth}: {graph:?}");
                    };
                    assert_eq!(
                        syntax.resource,
                        Some(ResourceFailure::StructuralDepth {
                            limit: STRUCTURAL_DEPTH_LIMIT
                        })
                    );
                    assert!(syntax.source.display_path().ends_with(if depth == 128 {
                        "main.ash"
                    } else {
                        "forms.ash"
                    }));
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
