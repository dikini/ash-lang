use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    driver::{PipelineFailure, RunConfiguration, run_path},
    module::{ModuleRoots, load_module_graph},
    resolve::{ResolveReason, resolve_module},
    surface::{SurfaceNominalDeclarationKind, SurfaceTypeVisibility},
    types::{ConstructorId, NominalTypeId, Type},
};

static TEMP_IDS: AtomicU64 = AtomicU64::new(0);

struct Fixture(PathBuf);

impl Fixture {
    fn new(source: &str) -> Self {
        loop {
            let id = TEMP_IDS.fetch_add(1, Ordering::Relaxed);
            let directory = std::env::temp_dir()
                .join(format!("ash-foreign-common-{}-{id}", std::process::id()));
            match fs::create_dir(&directory) {
                Ok(()) => {
                    let entry = directory.join("entry.ash");
                    fs::write(&entry, source).expect("common-module fixture source");
                    return Self(entry);
                }
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("common-module fixture directory: {error}"),
            }
        }
    }

    fn configuration(&self) -> RunConfiguration {
        RunConfiguration {
            entry: self.0.clone(),
            roots: ModuleRoots::empty(),
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(self.0.parent().unwrap());
    }
}

#[test]
fn common_module_is_admitted_once_with_ordered_ordinary_codec_identities() {
    let fixture = Fixture::new("import @builtin.foreign as Foreign\nimport helper as Helper\n");
    fs::write(
        fixture.0.parent().unwrap().join("helper.ash"),
        "import @builtin.foreign as Foreign\n",
    )
    .unwrap();
    let graph = load_module_graph(&fixture.0, &ModuleRoots::empty()).unwrap();
    let common = graph
        .modules()
        .iter()
        .find(|module| module.canonical_path() == std::path::Path::new("@builtin.foreign"))
        .unwrap();
    assert_eq!(graph.modules().len(), 3);
    assert!(common.id().to_string().starts_with("builtin.foreign:"));
    assert!(common.dependencies().is_empty());
    assert!(common.foreign_admission().is_none());
    for module in graph
        .modules()
        .iter()
        .filter(|module| module.id() != common.id())
    {
        assert!(
            module
                .dependencies()
                .iter()
                .any(|edge| edge.target() == common.id())
        );
    }
    let declarations = &common.surface().type_declarations;
    assert_eq!(
        declarations
            .iter()
            .map(|ty| ty.name.text.as_str())
            .collect::<Vec<_>>(),
        [
            "ConversionError",
            "Call",
            "Output",
            "Nullable",
            "Disposition"
        ]
    );
    assert_eq!(
        declarations[0].visibility,
        SurfaceTypeVisibility::PublicOpaque
    );
    assert!(declarations[0].parameters.is_empty());
    for declaration in &declarations[1..] {
        assert_eq!(
            declaration.declaration_kind,
            SurfaceNominalDeclarationKind::Data
        );
        assert_eq!(
            declaration.visibility,
            SurfaceTypeVisibility::PublicTransparent
        );
        assert_eq!(declaration.parameters.len(), 1);
    }
    for (declaration, expected) in declarations[1..].iter().zip([
        &["Returned", "ConversionFailed"][..],
        &["Unreadable", "Readable"][..],
        &["Null", "NonNull"][..],
        &["Consumed", "Retained", "BlockedDependent"][..],
    ]) {
        assert_eq!(
            declaration
                .constructors
                .iter()
                .map(|ctor| ctor.name.text.as_str())
                .collect::<Vec<_>>(),
            expected
        );
        for constructor in &declaration.constructors {
            let range = constructor.name.span.range();
            assert_eq!(
                &common.source().text()[range.start() as usize..range.end() as usize],
                constructor.name.text
            );
        }
    }
    let resolved = resolve_module(common, &[]).unwrap();
    let call = NominalTypeId::new(common.id(), 1);
    assert_eq!(
        resolved.registry().nominals()[0].id,
        NominalTypeId::new(common.id(), 0)
    );
    assert_eq!(resolved.registry().nominals()[1].id, call);
    assert_eq!(
        resolved.registry().nominals()[1].constructors.as_ref(),
        [ConstructorId::new(call, 0), ConstructorId::new(call, 1)]
    );
    let conversion = resolved
        .registry()
        .constructors()
        .iter()
        .find(|ctor| ctor.id == ConstructorId::new(call, 1))
        .unwrap();
    assert_eq!(
        conversion.payload,
        Some(Type::Nominal(NominalTypeId::new(common.id(), 0)))
    );
}

#[test]
fn common_result_constructors_are_ordinary_public_ash_values() {
    let fixture = Fixture::new(concat!(
        "import @builtin.foreign as Foreign\n",
        "unwrap : Foreign.Call<Int> -> Int\n",
        "unwrap (Foreign.Returned(value)) = value\n",
        "unwrap (Foreign.ConversionFailed(error)) = 0\n",
        "output : Foreign.Output<Int> -> Int\n",
        "output Foreign.Unreadable = 0\n",
        "output (Foreign.Readable(value)) = value\n",
        "nullable : Foreign.Nullable<Int> -> Int\n",
        "nullable Foreign.Null = 0\n",
        "nullable (Foreign.NonNull(value)) = value\n",
        "disposition : Foreign.Disposition<Int> -> Int\n",
        "disposition (Foreign.Consumed(value)) = value\n",
        "disposition (Foreign.Retained(value)) = value\n",
        "disposition Foreign.BlockedDependent = 0\n",
        "main : Unit -> Int\n",
        "main () = unwrap (Foreign.Returned(10)) + output (Foreign.Readable(10)) + nullable (Foreign.NonNull(10)) + disposition (Foreign.Consumed(12))\n",
    ));
    let observation = run_path(fixture.configuration()).unwrap();
    assert_eq!(observation.value_display(), "42");
    assert_eq!(observation.ty(), &Type::Int);
}

#[test]
fn conversion_error_type_is_nameable_but_its_constructors_are_withheld() {
    let named = Fixture::new(concat!(
        "import @builtin.foreign as Foreign\n",
        "wrap : Foreign.ConversionError -> Foreign.Call<Int>\n",
        "wrap error = Foreign.ConversionFailed(error)\n",
        "main : Unit -> Int\nmain () = 42\n",
    ));
    assert_eq!(
        run_path(named.configuration()).unwrap().value_display(),
        "42"
    );
    let inaccessible = Fixture::new(concat!(
        "import @builtin.foreign as Foreign\n",
        "main : Unit -> Foreign.ConversionError\n",
        "main () = Foreign.HiddenConversionError\n",
    ));
    let failure = run_path(inaccessible.configuration()).unwrap_err();
    assert!(
        matches!(failure.pipeline_failure(), Some(PipelineFailure::Resolution(error))
        if error.reason == ResolveReason::OpaqueConstructor)
    );
}
