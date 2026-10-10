use ash::{
    lexer::lex,
    parser::{parse, project_module},
    source::SourceFile,
    surface::{
        SurfaceDeclarationIndex, SurfaceDefinitionKind, SurfaceExprKind, SurfaceKindKind,
        SurfacePatternKind, SurfaceResourceReportCodecKind, SurfaceTypeKind,
    },
};

// Syntax evidence only: source checking authenticates all referenced roles later.
const SOURCE: &str = r"pub resource Buffer<Before : EffectRow, R, T, After : EffectRow> {
    owned R
    input (Int, Bool)
    state Native.State<R>
    data (Int, Bool)
    acquisition Acquire<Native.State<R>, (Int, Bool), Int>
    completion Finish<Native.State<R>, Int>
    result Scope<Int, Int, Answer> for <Answer>
    codec scope
    provider BufferProvider<R>
    effect BufferOps<{| Before}, R, T, {| After}>
    interpret Native.Allocate<R>, Native.Free<R>
    acquire (length, flags) => Acquired(length, flags)
    finish (native, data) => Consumed
    handlers (native, data) {
        length () => resume data
    }
}
main : Unit -> Int
main () = resource Memory.Buffer<{Left<Int>}, R, Bool, {| After}> buffer = (8, True) {
    42
}
";

#[test]
fn product_resource_projects_explicit_header_patterns_and_complete_arguments() {
    let source = SourceFile::new("resource-source.ash", SOURCE).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).unwrap();
    assert!(module.resources.is_empty());
    assert_eq!(
        module.declaration_order,
        [
            SurfaceDeclarationIndex::SourceResource(0),
            SurfaceDeclarationIndex::Global(0),
        ]
    );
    let resource = &module.source_resources[0];
    assert_eq!(
        resource
            .parameters
            .iter()
            .map(|p| p.name.text.as_str())
            .collect::<Vec<_>>(),
        ["Before", "R", "T", "After"]
    );
    assert_eq!(
        resource.parameters[0].kind.as_ref().unwrap().kind,
        SurfaceKindKind::EffectRow
    );
    assert_eq!(
        resource.parameters[3].kind.as_ref().unwrap().kind,
        SurfaceKindKind::EffectRow
    );
    assert!(resource.public);
    assert_eq!(resource.owned.text, "R");
    for (field, written) in [
        (&resource.input, "(Int, Bool)"),
        (&resource.state, "Native.State<R>"),
        (&resource.data, "(Int, Bool)"),
        (
            &resource.acquisition,
            "Acquire<Native.State<R>, (Int, Bool), Int>",
        ),
        (&resource.completion, "Finish<Native.State<R>, Int>"),
        (&resource.result, "Scope<Int, Int, Answer>"),
        (&resource.provider, "BufferProvider<R>"),
    ] {
        let range = field.span.range();
        assert_eq!(
            &source.text()[range.start() as usize..range.end() as usize],
            written
        );
    }
    assert_eq!(resource.codec.kind, SurfaceResourceReportCodecKind::Scope);
    assert_eq!(resource.result_parameters[0].name.text, "Answer");
    assert_eq!(
        resource
            .interpreted
            .iter()
            .map(|e| e.effect.member().text.as_str())
            .collect::<Vec<_>>(),
        ["Allocate", "Free"]
    );
    assert!(
        resource.interpreted[0].span.range().end() < resource.interpreted[1].span.range().start()
    );
    assert!(matches!(
        resource.acquire_pattern.kind,
        SurfacePatternKind::Tuple(_)
    ));
    assert!(matches!(
        resource.finish_pattern.kind,
        SurfacePatternKind::Tuple(_)
    ));
    assert!(matches!(
        resource.handlers_pattern.kind,
        SurfacePatternKind::Tuple(_)
    ));
    let args = &resource.provided.arguments;
    assert_eq!(args.len(), 4);
    assert!(matches!(args[0].kind, SurfaceTypeKind::RowArgument(_)));
    assert!(matches!(args[1].kind, SurfaceTypeKind::Named(_)));
    assert!(matches!(args[2].kind, SurfaceTypeKind::Named(_)));
    assert!(matches!(args[3].kind, SurfaceTypeKind::RowArgument(_)));
    let SurfaceDefinitionKind::Equational(global) = &module.definitions[0].kind else {
        panic!("expected an equation");
    };
    let SurfaceExprKind::ProviderResource(instance) = &global.equations[0].body.kind else {
        panic!("expected a resource instance");
    };
    assert_eq!(instance.arguments.len(), 4);
    assert!(matches!(
        instance.arguments[0].kind,
        SurfaceTypeKind::RowArgument(_)
    ));
    assert!(matches!(
        instance.arguments[1].kind,
        SurfaceTypeKind::Named(_)
    ));
    assert!(matches!(instance.arguments[2].kind, SurfaceTypeKind::Bool));
    assert!(matches!(
        instance.arguments[3].kind,
        SurfaceTypeKind::RowArgument(_)
    ));
    let owned = resource.owned.span.range();
    assert_eq!(
        &source.text()[owned.start() as usize..owned.end() as usize],
        "R"
    );
    let codec = resource.codec.span.range();
    assert_eq!(
        &source.text()[codec.start() as usize..codec.end() as usize],
        "scope"
    );

    let legacy = "resource Legacy<R> {\n    input Int\n    state Native.State<R>\n    result Report<T> for <T>\n    provider Provider<R>\n    effect Ops<R>\n    interpret Native.Call<R>\n    acquire input => input\n    finish state => state\n    handlers state {\n        value () => resume state\n    }\n}\n";
    let text = format!(
        "{legacy}{}",
        SOURCE
            .replace("codec scope", "codec acquired_only")
            .replace("\n    }\n}\nmain", "\n    }}\nmain")
    );
    let source = SourceFile::new("resource-channels.ash", text).unwrap();
    let tree = parse(lex(&source).unwrap());
    assert!(
        tree.parse_diagnostics().is_empty(),
        "{:?}",
        tree.parse_diagnostics()
    );
    let module = project_module(&source, &tree).unwrap();
    assert_eq!(module.resources.len(), 1);
    assert_eq!(module.source_resources.len(), 1);
    assert_eq!(
        module.source_resources[0].codec.kind,
        SurfaceResourceReportCodecKind::AcquiredOnly
    );
    assert_eq!(
        module.declaration_order[0],
        SurfaceDeclarationIndex::Resource(0)
    );
    assert_eq!(
        module.declaration_order[1],
        SurfaceDeclarationIndex::SourceResource(0)
    );
}

#[test]
fn malformed_product_headers_lists_and_patterns_cannot_project() {
    for text in [
        SOURCE.replace("    data (Int, Bool)\n", ""),
        SOURCE.replace("    owned R\n", "    owned R\n    owned T\n"),
        SOURCE.replace(
            "    input (Int, Bool)\n    state Native.State<R>",
            "    state Native.State<R>\n    input (Int, Bool)",
        ),
        SOURCE.replace("codec scope", "codec arbitrary"),
        SOURCE.replace("interpret Native.Allocate<R>, Native.Free<R>", "interpret"),
        SOURCE.replace(
            "interpret Native.Allocate<R>, Native.Free<R>",
            "interpret Native.Allocate<R>,",
        ),
        SOURCE.replace("acquire (length, flags) =>", "acquire (length,) =>"),
        SOURCE.replace("        length () => resume data\n", ""),
        SOURCE.replace(
            "    finish (native, data) =>",
            "    family<T> where Native.Layout<T> {}\n    finish (native, data) =>",
        ),
    ] {
        let source = SourceFile::new("bad-resource-source.ash", text).unwrap();
        let tree = parse(lex(&source).unwrap());
        assert!(project_module(&source, &tree).is_err(), "{}", source.text());
    }
}
