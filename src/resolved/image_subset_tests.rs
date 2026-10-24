use super::*;
use crate::source::{ByteRange, SourceFile};

fn ordinary_image_registry() -> ResolvedRegistry {
    let source = SourceFile::new("ordinary-image-subset.ash", "Tag").unwrap();
    let span = source.span(ByteRange::new(0, 3).unwrap()).unwrap();
    let nominal = NominalTypeId::new(ModuleId::new(91), 0);
    let constructor = ConstructorId::new(nominal, 0);
    ResolvedRegistry::new(
        vec![ResolvedNominalType {
            id: nominal,
            spelling: "Tag".to_owned(),
            declaration_kind: ResolvedNominalDeclarationKind::Data,
            representation: None,
            representation_provenance: None,
            constructors: Box::new([constructor]),
            origin: Origin::Source(span),
        }],
        vec![ResolvedConstructor {
            id: constructor,
            owner: nominal,
            spelling: "Tag".to_owned(),
            payload: None,
            origin: Origin::Source(span),
        }],
    )
    .with_type_parameters(vec![(nominal, Vec::new())])
}

fn ordinary_effect_registry() -> ResolvedRegistry {
    let source = SourceFile::new("ordinary-effect-image-subset.ash", "Effect").unwrap();
    let span = source.span(ByteRange::new(0, 6).unwrap()).unwrap();
    let module = ModuleId::new(92);
    let effect = EffectId::new(module, 0);
    let parameters = [Kind::Type, Kind::EffectRow]
        .into_iter()
        .enumerate()
        .map(|(index, kind)| ResolvedTypeVariable {
            id: TypeVariableId::resolved(module, u32::try_from(index).unwrap()),
            spelling: format!("Parameter{index}"),
            kind,
            origin: Origin::Source(span),
        })
        .collect::<Vec<_>>()
        .into_boxed_slice();
    let canonical_parameters = parameters.to_vec();
    ResolvedRegistry::new(Vec::new(), Vec::new()).with_effects(vec![ResolvedEffectDeclaration {
        id: effect,
        public: false,
        spelling: "Ordinary".to_owned(),
        parameters,
        operations: Box::new([ResolvedEffectOperation {
            id: OperationId::new(effect, 0),
            spelling: "request".to_owned(),
            annotation: ResolvedType {
                ty: Type::Function(Box::new(Type::Unit), Box::new(Type::Unit)),
                provenance: ResolvedTypeProvenance::new(
                    vec![ResolvedTypeProvenanceNode::Fact(span)],
                    0,
                ),
                origin: Origin::Source(span),
                span,
            },
            origin: Origin::Source(span),
            span,
        }]),
        native_contract: None,
        origin: Origin::Source(span),
        span,
    }])
    .with_image_kind_facts(
        canonical_parameters,
        Vec::new(),
        &mut TypeWorkBudget::unbounded(),
    )
    .expect("the effect fixture retains its exact canonical type and row parameters")
}

#[test]
fn ordinary_monomorphic_image_subset_preserves_exact_work_limit_and_retry() {
    let registry = ordinary_image_registry();
    let mut measured = TypeWorkBudget::unbounded();
    assert!(registry.monomorphic_image_subset(&mut measured).unwrap());
    let required = measured.used();
    for _ in 0..2 {
        let mut exact = TypeWorkBudget::with_limit(required);
        assert!(registry.monomorphic_image_subset(&mut exact).unwrap());
        assert_eq!(exact.used(), required);
        assert!(matches!(
            registry.monomorphic_image_subset(&mut TypeWorkBudget::with_limit(required - 1)),
            Err(ResolvedBuildFailure::TypeResource)
        ));
    }
}

#[test]
fn monomorphic_image_subset_refuses_effect_and_polymorphic_metadata_categories() {
    let effect_registry = ordinary_effect_registry();
    assert!(
        !effect_registry
            .monomorphic_image_subset(&mut TypeWorkBudget::unbounded())
            .unwrap()
    );
    let original = ordinary_image_registry();
    let mutations: &[fn(&mut ResolvedRegistry)] = &[
        |registry| {
            registry
                .lexical_nominal_positions
                .insert(NominalTypeId::new(ModuleId::new(91), 1), 0);
        },
        |registry| {
            registry.abstract_nominal_names.insert(
                NominalTypeId::new(ModuleId::new(91), 1),
                "Private".to_owned(),
            );
        },
        |registry| {
            let id = TypeVariableId::resolved(ModuleId::new(91), 0);
            let origin = registry.nominals[0].origin.clone();
            registry.insert_type_variable(ResolvedTypeVariable {
                id,
                spelling: "T".to_owned(),
                kind: Kind::Type,
                origin,
            });
        },
        |registry| {
            registry
                .owner_definition_positions
                .insert(OwnerId::Effect(EffectId::new(ModuleId::new(91), 0)), 0);
        },
    ];
    for (index, mutate) in mutations.iter().enumerate() {
        let mut registry = original.clone();
        mutate(&mut registry);
        assert_eq!(
            registry.monomorphic_image_subset(&mut TypeWorkBudget::unbounded()),
            Ok(false),
            "accepted unsupported metadata category {index}"
        );
    }
}

#[test]
fn native_image_subset_retains_ordinary_type_and_row_owners_with_exact_work() {
    let registry = ordinary_effect_registry();
    let mut measured = TypeWorkBudget::unbounded();
    assert!(
        registry
            .native_image_subset_with_source_scopes(&[], &[], &mut measured)
            .unwrap()
    );
    let required = measured.used();
    for _ in 0..2 {
        let mut exact = TypeWorkBudget::with_limit(required);
        assert!(
            registry
                .native_image_subset_with_source_scopes(&[], &[], &mut exact)
                .unwrap()
        );
        assert_eq!(exact.used(), required);
        assert!(matches!(
            registry.native_image_subset_with_source_scopes(
                &[],
                &[],
                &mut TypeWorkBudget::with_limit(required - 1)
            ),
            Err(ResolvedBuildFailure::TypeResource)
        ));
    }
}

#[test]
fn native_image_subset_refuses_missing_extra_or_invalid_kind_owner_records() {
    let original = ordinary_effect_registry();
    let mutations: &[fn(&mut ResolvedRegistry)] = &[
        |registry| {
            registry
                .type_variables
                .remove(&registry.effects[0].parameters[0].id);
        },
        |registry| {
            let id = TypeVariableId::resolved(ModuleId::new(92), 2);
            registry.insert_type_variable(ResolvedTypeVariable {
                id,
                spelling: "Extra".to_owned(),
                kind: Kind::Type,
                origin: registry.effects[0].origin.clone(),
            });
        },
        |registry| {
            registry.effects[0].parameters[0].kind =
                Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        },
        |registry| {
            registry.owner_definitions.pop();
        },
    ];
    for (index, mutate) in mutations.iter().enumerate() {
        let mut registry = original.clone();
        mutate(&mut registry);
        assert_eq!(
            registry.native_image_subset_with_source_scopes(
                &[],
                &[],
                &mut TypeWorkBudget::unbounded()
            ),
            Ok(false),
            "accepted malformed owner inventory {index}"
        );
    }
}
