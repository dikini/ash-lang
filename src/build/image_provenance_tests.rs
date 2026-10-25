//! Lossless original-provenance carrier and portable map ordering controls.
use super::*;
use crate::resolved::{ResolvedTypeProvenance, ResolvedTypeProvenanceNode as P};

fn encoder<'a>(source: &SourceFile, work: &'a mut TypeWorkBudget) -> Encoder<'a> {
    let encoder = Encoder {
        image: PureImage {
            effect_dialect: true,
            ..PureImage::default()
        },
        structural: HashMap::new(),
        kind_records: HashMap::new(),
        quantifier_vectors: HashMap::new(),
        modules: HashMap::new(),
        sources: HashMap::new(),
        binders: HashMap::new(),
        remapped: Vec::new(),
        prepared_libraries: HashMap::new(),
        native_symbols: HashMap::new(),

        origin_records: HashMap::new(),
        origin_spans: HashMap::new(),
        original_native_symbols: Vec::new(),
        work,
    };
    let mut encoder = encoder;
    encoder.sources.insert(source.id(), 0);
    encoder
}
fn image(
    source: &SourceFile,
    originals: &[ResolvedTypeProvenance],
    work: &mut TypeWorkBudget,
) -> Result<PureImage, ImageFailure> {
    let mut encoder = encoder(source, work);
    for original in originals {
        encoder.encode_provenance(original)?;
    }
    encoder.image.native_fact_prefixes = Some(NativeFactPrefixes::seal(&encoder.image)?);
    Ok(encoder.image)
}
fn restore(
    image: &PureImage,
    source: &SourceFile,
    work: &mut TypeWorkBudget,
) -> Result<RestoredProvenance, ImageFailure> {
    let modules = [ModuleId::from(source.id())];
    let mut decoder = Decoder {
        image,
        expected_fact_prefixes: None,
        sources: CoordinateStorage::Borrowed(std::slice::from_ref(source)),
        modules: CoordinateStorage::Borrowed(&modules),
        source_declaration_catalogs: HashMap::new(),
        decoded_types: HashMap::new(),
        decoded_rows: HashMap::new(),
        work,
    };
    decoder
        .provenance_arena()?
        .ok_or(ImageFailure::InvalidRecord)
}
fn original_views(source: &SourceFile) -> Vec<ResolvedTypeProvenance> {
    let a = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
    let b = source.span(ByteRange::new(2, 3).unwrap()).unwrap();
    let c = source.span(ByteRange::new(4, 5).unwrap()).unwrap();
    let original = ResolvedTypeProvenance::new(
        vec![
            P::Fact(a),
            P::Fact(b),
            P::Tuple {
                span: a,
                elements: vec![0, 1].into_boxed_slice(),
            },
            P::Fact(c),
        ],
        2,
    );
    // The last Fact is deliberately outside root2's reachable graph. Existing
    // complete-arena equality still observes it; this carrier must preserve it.
    let view = original
        .image_view(0, &mut TypeWorkBudget::default())
        .unwrap();
    vec![original, view]
}
#[test]
fn complete_arenas_and_occurrence_roots_reencode_without_expansion() {
    let source = SourceFile::new("complete-arena.ash", "A B C").unwrap();
    let originals = original_views(&source);
    let original = image(&source, &originals, &mut TypeWorkBudget::default()).unwrap();
    assert_eq!(original.provenance.len(), 8);
    assert_eq!(original.provenance_children.len(), 4);
    let wire = original
        .encode_bytes(&mut TypeWorkBudget::default())
        .unwrap();
    let facts = original
        .encode_native_expectations(&mut TypeWorkBudget::default())
        .unwrap();
    let decoded = PureImage::decode_bytes(&wire, &mut TypeWorkBudget::default()).unwrap();
    decoded
        .admit_expected_native_facts(&facts, &mut TypeWorkBudget::default())
        .unwrap();
    let restored = restore(&decoded, &source, &mut TypeWorkBudget::default()).unwrap();
    for (original, restored) in originals.iter().zip(&restored.views) {
        assert!(
            crate::resolved::same_resolved_type_provenance_with_budget(
                original,
                restored,
                &mut TypeWorkBudget::default()
            )
            .unwrap()
        );
        assert_eq!(restored.nodes().len(), 4);
    }
    let rebuilt = image(&source, &restored.views, &mut TypeWorkBudget::default()).unwrap();
    assert_eq!(
        rebuilt
            .encode_bytes(&mut TypeWorkBudget::default())
            .unwrap(),
        wire
    );
    assert_eq!(
        rebuilt
            .encode_native_expectations(&mut TypeWorkBudget::default())
            .unwrap(),
        facts
    );
    let mut donor = original_views(&source);
    donor[0] = ResolvedTypeProvenance::new(
        vec![
            P::Fact(source.span(ByteRange::new(0, 1).unwrap()).unwrap()),
            P::Fact(source.span(ByteRange::new(2, 3).unwrap()).unwrap()),
            P::Tuple {
                span: source.span(ByteRange::new(0, 1).unwrap()).unwrap(),
                elements: vec![0, 1].into_boxed_slice(),
            },
            P::Fact(source.span(ByteRange::new(0, 1).unwrap()).unwrap()),
        ],
        2,
    );
    assert!(
        !crate::resolved::same_resolved_type_provenance_with_budget(
            &originals[0],
            &donor[0],
            &mut TypeWorkBudget::default()
        )
        .unwrap()
    );
    let donor = image(&source, &donor, &mut TypeWorkBudget::default()).unwrap();
    assert!(matches!(
        donor.admit_expected_native_facts(&facts, &mut TypeWorkBudget::default()),
        Err(ImageFailure::InvalidRecord)
    ));
    let mut root_donor = image(&source, &originals, &mut TypeWorkBudget::default()).unwrap();
    root_donor.provenance_views[0].root = 0;
    let root_views = restore(&root_donor, &source, &mut TypeWorkBudget::default()).unwrap();
    assert!(
        !crate::resolved::same_resolved_type_provenance_with_budget(
            &originals[0],
            &root_views.views[0],
            &mut TypeWorkBudget::default()
        )
        .unwrap()
    );
    assert!(matches!(
        root_donor.admit_expected_native_facts(&facts, &mut TypeWorkBudget::default()),
        Err(ImageFailure::InvalidRecord)
    ));
}
#[test]
fn complete_arena_ranges_edges_and_coverage_refuse_malformed_data() {
    let source = SourceFile::new("complete-arena-bounds.ash", "A B C").unwrap();
    let originals = original_views(&source);
    let original = image(&source, &originals, &mut TypeWorkBudget::default()).unwrap();
    restore(&original, &source, &mut TypeWorkBudget::default()).unwrap();
    for mutation in 0..13 {
        let mut donor = image(&source, &originals, &mut TypeWorkBudget::default()).unwrap();
        match mutation {
            0 => donor.provenance_views[0].nodes.start = 1,
            1 => donor.provenance_views[0].nodes.len = 0,
            2 => donor.provenance_views[0].root = 4,
            3 => donor.provenance_views[0].children.start = 1,
            4 => donor.provenance_views[0].children.len = 3,
            5 => {
                let ProvenanceRecord::Tuple { elements, .. } = &mut donor.provenance[2] else {
                    panic!("tuple")
                };
                elements.start = 2;
            }
            6 => donor.provenance_children[0] = 4,
            7 => {
                donor.provenance_views.pop();
            }
            8 => donor.provenance_children[2] = 0,
            9 => donor.provenance_children[0] = 2,
            10 => donor.provenance_children.push(0),
            11 => donor.provenance_views.push(donor.provenance_views[0]),
            _ => donor.provenance.push(donor.provenance[0]),
        }
        assert!(
            matches!(
                restore(&donor, &source, &mut TypeWorkBudget::default()),
                Err(ImageFailure::InvalidRecord)
            ),
            "mutation{mutation}"
        );
    }
}
#[test]
fn complete_arena_reconstruction_carries_exact_short_spent_and_fresh_work() {
    let source = SourceFile::new("complete-arena-work.ash", "A B C").unwrap();
    let originals = original_views(&source);
    let original = image(&source, &originals, &mut TypeWorkBudget::default()).unwrap();
    let mut measured = TypeWorkBudget::default();
    restore(&original, &source, &mut measured).unwrap();
    let cost = measured.used();
    for prefix in [0, 7] {
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert!(matches!(
            restore(&original, &source, &mut short),
            Err(ImageFailure::Resource)
        ));
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            restore(&original, &source, &mut exact).unwrap();
            assert_eq!(exact.used(), prefix + cost);
            assert!(matches!(
                restore(&original, &source, &mut exact),
                Err(ImageFailure::Resource)
            ));
        }
    }
}
#[test]
fn portable_identity_sort_ignores_insertion_and_process_module_order() {
    fn ordered(
        raw: [u32; 2],
        reverse: bool,
        work: &mut TypeWorkBudget,
    ) -> Result<Vec<(NominalId, u32)>, ImageFailure> {
        let mut modules = HashMap::new();
        modules.insert(ModuleId::new(raw[0]), 0u32);
        modules.insert(ModuleId::new(raw[1]), 1u32);
        let mut items = Vec::new();
        for i in if reverse { [1, 0] } else { [0, 1] } {
            charge(work, 1)?;
            let portable = *modules.get(&ModuleId::new(raw[i])).unwrap();
            push(
                &mut items,
                (
                    NominalId {
                        module: portable,
                        local: 3,
                    },
                    portable + 20,
                ),
                work,
            )?;
        }
        sort_image_records(&mut items, |entry| entry.0, work)?;
        Ok(items)
    }
    let mut measured = TypeWorkBudget::default();
    let expected = ordered([100, 2], false, &mut measured).unwrap();
    assert_eq!(
        ordered([1, 200], true, &mut TypeWorkBudget::default()).unwrap(),
        expected
    );
    let cost = measured.used();
    let mut short = TypeWorkBudget::with_limit(cost - 1);
    assert!(matches!(
        ordered([100, 2], false, &mut short),
        Err(ImageFailure::Resource)
    ));
    for _ in 0..2 {
        let mut exact = TypeWorkBudget::with_limit(cost);
        assert_eq!(ordered([1, 200], true, &mut exact).unwrap(), expected);
        assert!(matches!(
            ordered([1, 200], true, &mut exact),
            Err(ImageFailure::Resource)
        ));
    }
    let resolved = TypeVariableIdentity::Resolved {
        module: 0,
        local: 3,
    };
    let generated = TypeVariableIdentity::Generated(3);
    let mut tags = [(generated, 2u32), (resolved, 1)];
    sort_image_records(&mut tags, |entry| entry.0, &mut TypeWorkBudget::default()).unwrap();
    assert_eq!(tags[0].0, resolved);
    assert_eq!(tags[1].0, generated);
}

fn portable_row_wire(raw: [u32; 2], work: &mut TypeWorkBudget) -> Result<Vec<u8>, ImageFailure> {
    use crate::types::{EffectId, EffectInstance, EffectRow, EffectRowVariable, KindedArgument};
    let source = SourceFile::new("portable-row-order.ash", "A B").unwrap();
    let modules = raw.map(ModuleId::new);
    let instance = |module| EffectInstance::new(EffectId::new(module, 0), Box::new([]));
    // The same outer effect has nested row arguments whose native ordering flips.
    let nested =
        EffectRow::closed(vec![instance(modules[0]), instance(modules[1])].into_boxed_slice());
    let first = EffectInstance::new_kinded(
        EffectId::new(modules[0], 1),
        vec![
            KindedArgument::RowArg(nested),
            KindedArgument::TypeArg(Type::Int),
        ]
        .into_boxed_slice(),
    );
    let second = EffectInstance::new_kinded(
        EffectId::new(modules[0], 1),
        vec![
            KindedArgument::RowArg(EffectRow::singleton(instance(modules[1]))),
            KindedArgument::TypeArg(Type::Bool),
        ]
        .into_boxed_slice(),
    );
    let row = EffectRow::with_tail(
        vec![first, second, instance(modules[1])].into_boxed_slice(),
        EffectRowVariable::Rigid(crate::types::TypeVariableId::Generated(7)),
        vec![instance(modules[0])].into_boxed_slice(),
    );
    let mut encoder = encoder(&source, work);
    encoder.modules.insert(modules[0], 0);
    encoder.modules.insert(modules[1], 1);
    encoder.encode_structural(StructuralInput::Row(&row))?;
    encoder.image.native_fact_prefixes = Some(NativeFactPrefixes::seal(&encoder.image)?);
    encoder.image.encode_bytes(encoder.work)
}

#[test]
fn portable_row_wire_orders_complete_nested_instances_before_interning() {
    let mut measured = TypeWorkBudget::default();
    let expected = portable_row_wire([2, 100], &mut measured).unwrap();
    assert_eq!(
        portable_row_wire([100, 2], &mut TypeWorkBudget::default()).unwrap(),
        expected
    );
    let cost = measured.used();
    let mut short = TypeWorkBudget::with_limit(cost - 1);
    assert!(matches!(
        portable_row_wire([2, 100], &mut short),
        Err(ImageFailure::Resource)
    ));
    for _ in 0..2 {
        let mut exact = TypeWorkBudget::with_limit(cost);
        assert_eq!(portable_row_wire([2, 100], &mut exact).unwrap(), expected);
        assert_eq!(exact.used(), cost);
        assert!(matches!(
            portable_row_wire([2, 100], &mut exact),
            Err(ImageFailure::Resource)
        ));
    }
}

#[test]
fn portable_row_keys_preserve_ordered_actuals_kinds_tails_and_depth() {
    use crate::types::{
        ComputationType, EffectId, EffectInstance, EffectRow, EffectRowVariable, Kind,
        KindedArgument, TypeVariableId,
    };
    let source = SourceFile::new("portable-row-keys.ash", "A B").unwrap();
    let mut work = TypeWorkBudget::default();
    let mut encoder = encoder(&source, &mut work);
    let module = ModuleId::new(4);
    encoder.modules.insert(module, 0);
    let effect = EffectId::new(module, 3);
    let key = |encoder: &mut Encoder<'_>, instance: &EffectInstance, depth| {
        encoder.row_order_key(StructuralInput::Instance(instance), depth)
    };
    let left = EffectInstance::new(effect, vec![Type::Int, Type::Bool].into_boxed_slice());
    let right = EffectInstance::new(effect, vec![Type::Bool, Type::Int].into_boxed_slice());
    assert_ne!(
        key(&mut encoder, &left, 0).unwrap(),
        key(&mut encoder, &right, 0).unwrap()
    );
    let pure = EffectInstance::new(
        effect,
        vec![Type::function(Type::Int, Type::Bool)].into_boxed_slice(),
    );
    let empty = EffectInstance::new(
        effect,
        vec![Type::EffectfulFunction(
            Box::new(Type::Int),
            Box::new(ComputationType::new(Type::Bool, EffectRow::empty())),
        )]
        .into_boxed_slice(),
    );
    assert_eq!(
        key(&mut encoder, &pure, 0).unwrap(),
        key(&mut encoder, &empty, 0).unwrap()
    );
    let quantified = |kind| {
        EffectInstance::new(
            effect,
            vec![Type::Forall(
                vec![(TypeVariableId::Generated(2), kind)].into_boxed_slice(),
                Box::new(Type::Unit),
            )]
            .into_boxed_slice(),
        )
    };
    assert_ne!(
        key(&mut encoder, &quantified(Kind::Type), 0).unwrap(),
        key(
            &mut encoder,
            &quantified(Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::EffectRow))),
            0
        )
        .unwrap()
    );
    let tail = |id| {
        EffectInstance::new_kinded(
            effect,
            vec![KindedArgument::RowArg(EffectRow::open(
                EffectRowVariable::Rigid(id),
                Box::new([]),
            ))]
            .into_boxed_slice(),
        )
    };
    assert_ne!(
        key(&mut encoder, &tail(TypeVariableId::Generated(2)), 0).unwrap(),
        key(
            &mut encoder,
            &tail(TypeVariableId::Resolved { module, local: 2 }),
            0
        )
        .unwrap()
    );
    assert!(matches!(
        key(&mut encoder, &pure, crate::core::CORE_PAYLOAD_DEPTH_LIMIT),
        Err(ImageFailure::Resource)
    ));
    let unknown = EffectInstance::new(EffectId::new(ModuleId::new(44), 0), Box::new([]));
    assert!(key(&mut encoder, &unknown, 0).is_err());
    let inference = crate::types::InferenceVariableId::new(33);
    let pending = EffectInstance::new_kinded(
        effect,
        vec![KindedArgument::RowArg(EffectRow::open(
            EffectRowVariable::Inference(inference),
            Box::new([]),
        ))]
        .into_boxed_slice(),
    );
    assert!(matches!(
        key(&mut encoder, &pending, 0),
        Err(ImageFailure::Unsupported(Unsupported::Type))
    ));
    // Source-only inference placeholders have no private-image admission route.
    assert!(matches!(
        key(&mut encoder, &pending, 0),
        Err(ImageFailure::Unsupported(Unsupported::Type))
    ));
}
