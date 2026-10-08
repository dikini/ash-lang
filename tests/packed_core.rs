use ash::{
    core::{
        CoreBuilder, ValidationReason, packed::Intrinsic, transform::identity_traversal, validate,
    },
    eval::{Value, evaluate},
    module::ModuleId,
    source::{ByteRange, Origin, SourceFile},
    types::Type,
};

fn fixture() -> (SourceFile, Origin) {
    let source = SourceFile::new("packed.ash", "\"a\"").unwrap();
    let origin = Origin::Source(source.span(ByteRange::new(0, 3).unwrap()).unwrap());
    (source, origin)
}

#[test]
fn packed_string_preserves_utf8_nul_and_identity_transform() {
    let (source, origin) = fixture();
    let mut builder = CoreBuilder::new();
    let root = builder
        .string("é\0z".as_bytes(), Type::String, origin)
        .unwrap();
    let program = validate(builder.finish(root).unwrap(), &[&source]).unwrap();
    let copied = identity_traversal(&program).unwrap();
    let Value::String(value) = evaluate(&validate(copied, &[&source]).unwrap())
        .unwrap()
        .value
    else {
        panic!("string value")
    };
    assert_eq!(value.as_ref(), "é\0z");
}

#[test]
fn malformed_utf8_core_is_independently_rejected() {
    let (source, origin) = fixture();
    let mut builder = CoreBuilder::new();
    let root = builder
        .string([0xff].as_slice(), Type::String, origin)
        .unwrap();
    assert_eq!(
        validate(builder.finish(root).unwrap(), &[&source])
            .unwrap_err()
            .reason(),
        ValidationReason::NodeType
    );
}

#[test]
fn string_annotation_cannot_change_its_type() {
    let (source, origin) = fixture();
    let mut builder = CoreBuilder::new();
    let root = builder
        .string(b"text".as_slice(), Type::Bytes, origin)
        .unwrap();
    assert_eq!(
        validate(builder.finish(root).unwrap(), &[&source])
            .unwrap_err()
            .reason(),
        ValidationReason::NodeType
    );
}

#[test]
fn ordinary_module_identity_cannot_forge_an_intrinsic() {
    let (source, origin) = fixture();
    let mut builder = CoreBuilder::new();
    let root = builder
        .intrinsic(
            Intrinsic::BytesEmpty,
            ModuleId::from(source.id()),
            Type::Function(Box::new(Type::Unit), Box::new(Type::Bytes)),
            origin,
        )
        .unwrap();
    assert_eq!(
        validate(builder.finish(root).unwrap(), &[&source])
            .unwrap_err()
            .reason(),
        ValidationReason::Registry
    );
}

fn builtin_fixture() -> (
    ash::module::ModuleGraph,
    std::sync::Arc<ash::resolved::ResolvedRegistry>,
) {
    use ash::{
        elaborate::{check_module, link_modules},
        module::{ModuleRoots, load_module_graph},
        resolve::{DependencyExports, resolve_module},
        resolved::CheckedModule,
    };
    let path = std::env::temp_dir().join(format!(
        "ash-packed-core-{}-{}.ash",
        std::process::id(),
        fixture().0.id().value()
    ));
    std::fs::write(&path, "import @builtin.bytes as B\nimport @builtin.string as T\nmain : Unit -> Int\nmain () = B.length (T.to_utf8 \"text\")\n").unwrap();
    let graph = load_module_graph(&path, &ModuleRoots::empty()).unwrap();
    std::fs::remove_file(path).unwrap();
    let mut checked: Vec<CheckedModule> = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                DependencyExports::new(
                    edge,
                    checked
                        .iter()
                        .find(|checked| checked.module() == edge.target())
                        .unwrap()
                        .exports(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        checked.push(check_module(resolve_module(module, &dependencies).unwrap()).unwrap());
    }
    let linked = link_modules(checked, graph.entry()).unwrap();
    (graph, std::sync::Arc::clone(linked.registry()))
}

fn validate_builtin_core(
    graph: &ash::module::ModuleGraph,
    program: ash::core::UnvalidatedProgram,
) -> Result<ash::core::ValidatedProgram, ash::core::ValidationError> {
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let relation = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    ash::core::validate_modules(program, &sources, &relation)
}

#[test]
fn builtin_intrinsic_cannot_change_its_signature() {
    let (graph, registry) = builtin_fixture();
    let builtin = &graph.modules()[0];
    let origin = Origin::Source(
        builtin
            .source()
            .span(ByteRange::new(0, 1).unwrap())
            .unwrap(),
    );
    let mut builder = CoreBuilder::with_registry(registry);
    let root = builder
        .intrinsic(
            Intrinsic::BytesEmpty,
            builtin.id(),
            Type::Function(Box::new(Type::Unit), Box::new(Type::String)),
            origin,
        )
        .unwrap();
    assert_eq!(
        validate_builtin_core(&graph, builder.finish(root).unwrap())
            .unwrap_err()
            .reason(),
        ValidationReason::NodeType
    );
}

#[test]
fn intrinsic_result_rejects_constructor_substitution() {
    use ash::types::{ConstructorId, NominalTypeId};
    let (graph, registry) = builtin_fixture();
    let bytes = &graph.modules()[0];
    let string = &graph.modules()[1];
    let origin = Origin::Source(bytes.source().span(ByteRange::new(0, 1).unwrap()).unwrap());
    let wrong_owner = NominalTypeId::new(string.id(), 0);
    let operation = Intrinsic::BytesAppendByte {
        appended: ConstructorId::new(wrong_owner, 0),
        invalid: ConstructorId::new(wrong_owner, 1),
    };
    let mut builder = CoreBuilder::with_registry(registry);
    let root = builder
        .intrinsic(
            operation,
            bytes.id(),
            Type::Function(
                Box::new(Type::Tuple(Box::new([Type::Bytes, Type::Int]))),
                Box::new(Type::Nominal(wrong_owner)),
            ),
            origin,
        )
        .unwrap();
    assert_eq!(
        validate_builtin_core(&graph, builder.finish(root).unwrap())
            .unwrap_err()
            .reason(),
        ValidationReason::Registry
    );
}

#[test]
fn pure_intrinsic_application_and_transform_preserve_packed_data() {
    let (graph, registry) = builtin_fixture();
    let builtin = &graph.modules()[1];
    let origin = Origin::Source(
        builtin
            .source()
            .span(ByteRange::new(0, 1).unwrap())
            .unwrap(),
    );
    let mut builder = CoreBuilder::with_registry(registry);
    let callable = builder
        .intrinsic(
            Intrinsic::StringToUtf8,
            builtin.id(),
            Type::Function(Box::new(Type::String), Box::new(Type::Bytes)),
            origin.clone(),
        )
        .unwrap();
    let input = builder
        .string("é\0".as_bytes(), Type::String, origin.clone())
        .unwrap();
    let root = builder
        .application(callable, input, Type::Bytes, origin)
        .unwrap();
    let program = validate_builtin_core(&graph, builder.finish(root).unwrap()).unwrap();
    let transformed = validate_builtin_core(&graph, identity_traversal(&program).unwrap()).unwrap();
    for program in [&program, &transformed] {
        let Value::Bytes(bytes) = evaluate(program).unwrap().value else {
            panic!("bytes")
        };
        assert_eq!(bytes.as_ref(), "é\0".as_bytes());
    }
}

#[test]
fn effect_core_string_constant_and_transform_preserve_utf8_nul() {
    use ash::core::{EffectCoreBuilder, transform::identity_effect_traversal, validate_effect};
    let (source, origin) = fixture();
    let mut builder = EffectCoreBuilder::with_effect_registry(std::sync::Arc::new(
        ash::resolved::ResolvedRegistry::default(),
    ));
    let root = builder
        .string("世界\0".as_bytes(), Type::String, origin)
        .unwrap();
    let program = validate_effect(builder.finish(root).unwrap(), &[&source]).unwrap();
    let transformed =
        validate_effect(identity_effect_traversal(&program).unwrap(), &[&source]).unwrap();
    for program in [&program, &transformed] {
        let Value::String(text) = ash::eval::evaluate_effect(program).unwrap().value else {
            panic!("string")
        };
        assert_eq!(text.as_ref(), "世界\0");
    }
}

#[test]
fn public_builtin_program_preserves_intrinsics_after_effect_transforms() {
    use ash::{
        core::{
            transform::{fold_effect_literal_primitives, identity_effect_traversal},
            validate_effect_modules,
        },
        elaborate::{EffectElaborator, check_module, link_modules},
        evidence_validation::validate_interface_evidence,
        resolve::{DependencyExports, resolve_module},
        resolved::CheckedModule,
    };
    let (graph, _) = builtin_fixture();
    let mut checked: Vec<CheckedModule> = Vec::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                DependencyExports::new(
                    edge,
                    checked
                        .iter()
                        .find(|checked| checked.module() == edge.target())
                        .unwrap()
                        .exports(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        checked.push(check_module(resolve_module(module, &dependencies).unwrap()).unwrap());
    }
    let linked =
        validate_interface_evidence(link_modules(checked, graph.entry()).unwrap()).unwrap();
    let mut elaborator = EffectElaborator::for_module_program(&linked).unwrap();
    let root = elaborator
        .synthesize_effect_module_program(&linked)
        .unwrap()
        .node;
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let relation = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let program =
        validate_effect_modules(elaborator.finish(root).unwrap(), &sources, &relation).unwrap();
    for transformed in [
        identity_effect_traversal(&program),
        fold_effect_literal_primitives(&program),
    ] {
        let transformed =
            validate_effect_modules(transformed.unwrap(), &sources, &relation).unwrap();
        assert_eq!(
            ash::eval::evaluate_effect(&transformed)
                .unwrap()
                .value
                .to_string(),
            "4"
        );
    }
}
