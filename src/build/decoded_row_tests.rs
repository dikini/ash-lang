//! Decoder-local structural Row values, never admission receipts.
use super::*;

fn record(image: &mut PureImage, tag: TypeTag, children: &[u32]) -> u32 {
    let start = image.type_children.len();
    image.type_children.extend_from_slice(children);
    let slot = index(image.types.len()).unwrap();
    image.types.push(TypeRecord {
        tag,
        children: Slice::of(&image.type_children, start).unwrap(),
    });
    slot
}
fn fixture(depth: usize) -> (PureImage, u32) {
    let mut image = PureImage {
        effect_dialect: true,
        ..PureImage::default()
    };
    let unit = record(&mut image, TypeTag::Unit, &[]);
    let mut ty = unit;
    for _ in 0..depth {
        ty = record(&mut image, TypeTag::Function, &[unit, ty]);
    }
    let ty = record(&mut image, TypeTag::ArgumentType, &[ty]);
    let empty = record(
        &mut image,
        TypeTag::Row {
            known: 0,
            tail: None,
        },
        &[],
    );
    let row = record(&mut image, TypeTag::ArgumentRow, &[empty]);
    let member = record(
        &mut image,
        TypeTag::Instance(EffectIdentity {
            module: 0,
            local: 7,
        }),
        &[ty, row],
    );
    let absent = record(
        &mut image,
        TypeTag::Instance(EffectIdentity {
            module: 0,
            local: 8,
        }),
        &[],
    );
    let root = record(
        &mut image,
        TypeTag::Row {
            known: 1,
            tail: Some(TypeVariableIdentity::Resolved {
                module: 0,
                local: 9,
            }),
        },
        // Wire rows retain their complete lacks vector; unlike with_tail,
        // raw reconstruction does not add known members on the caller's behalf.
        &[member, member, absent],
    );
    (image, root)
}
fn decoder<'a>(
    image: &'a PureImage,
    work: &'a mut TypeWorkBudget,
    module: ModuleId,
) -> Decoder<'a> {
    Decoder {
        image,
        expected_fact_prefixes: None,
        sources: CoordinateStorage::Owned(Vec::new()),
        modules: CoordinateStorage::Owned(vec![module]),
        source_declaration_catalogs: HashMap::new(),
        decoded_types: HashMap::new(),
        decoded_rows: HashMap::new(),
        work,
    }
}

#[test]
fn decoded_rows_keep_full_kinds_identities_and_paid_exact_replays() {
    let (image, root) = fixture(5);
    let module = ModuleId::new(401);
    fn repeated(
        image: &PureImage,
        root: u32,
        module: ModuleId,
        work: &mut TypeWorkBudget,
        cold: bool,
    ) -> Result<(), ImageFailure> {
        let mut d = decoder(image, work, module);
        if cold {
            d.expected_fact_prefixes = Some(NativeFactPrefixes::seal(image)?);
        }
        let first = d.row(root)?;
        assert_eq!(
            first.known()[0].effect(),
            crate::types::EffectId::new(module, 7)
        );
        assert!(matches!(
            first.known()[0].arguments()[0],
            crate::types::KindedArgument::TypeArg(_)
        ));
        assert!(matches!(
            first.known()[0].arguments()[1],
            crate::types::KindedArgument::RowArg(_)
        ));
        assert_eq!(
            first.tail().unwrap().variable(),
            crate::types::EffectRowVariable::Rigid(crate::types::TypeVariableId::resolved(
                module, 9
            ))
        );
        assert_eq!(first.tail().unwrap().lacks().len(), 2);
        for _ in 0..8 {
            assert_eq!(d.row(root)?, first);
        }
        assert_eq!(d.decoded_rows.len(), usize::from(!cold));
        Ok(())
    }
    let mut measured = TypeWorkBudget::default();
    repeated(&image, root, module, &mut measured, false).unwrap();
    let cost = measured.used();
    let mut cold = TypeWorkBudget::default();
    repeated(&image, root, module, &mut cold, true).unwrap();
    assert!(
        cost < cold.used(),
        "sharing removes actual raw reconstruction"
    );
    for prefix in [0, 7] {
        let mut short = TypeWorkBudget::with_limit(prefix + cost - 1);
        short.charge(prefix).unwrap();
        assert!(matches!(
            repeated(&image, root, module, &mut short, false),
            Err(ImageFailure::Resource)
        ));
        let spent = short.used();
        assert!(matches!(
            repeated(&image, root, module, &mut short, false),
            Err(ImageFailure::Resource)
        ));
        assert!(short.used() >= spent);
        for _ in 0..2 {
            let mut exact = TypeWorkBudget::with_limit(prefix + cost);
            exact.charge(prefix).unwrap();
            repeated(&image, root, module, &mut exact, false).unwrap();
            assert_eq!(exact.used(), prefix + cost);
        }
    }
    let mut first_cost = TypeWorkBudget::default();
    decoder(&image, &mut first_cost, module).row(root).unwrap();
    for limit in 0..first_cost.used() {
        let mut work = TypeWorkBudget::with_limit(limit);
        let mut d = decoder(&image, &mut work, module);
        assert!(matches!(d.row(root), Err(ImageFailure::Resource)));
        assert!(
            d.decoded_rows.is_empty(),
            "failed raw decode or caller clone cannot publish"
        );
    }
}

#[test]
fn decoded_rows_never_cross_prefix_or_coordinate_domains() {
    let (mut image, root) = fixture(2);
    let prefixes = NativeFactPrefixes::seal(&image).unwrap();
    let suffix = record(
        &mut image,
        TypeTag::Row {
            known: 0,
            tail: None,
        },
        &[],
    );
    let mut work = TypeWorkBudget::default();
    let mut d = decoder(&image, &mut work, ModuleId::new(401));
    let original = d.row(root).unwrap();
    d.row(suffix).unwrap();
    d.expected_fact_prefixes = Some(prefixes);
    assert!(matches!(d.row(suffix), Err(ImageFailure::InvalidRecord)));
    d.expected_fact_prefixes = None;
    assert!(matches!(d.row(0), Err(ImageFailure::InvalidRecord)));
    assert!(!d.decoded_rows.contains_key(&(0, 0, 1)));
    d.modules.push(ModuleId::new(402), d.work).unwrap();
    assert_eq!(d.row(root).unwrap(), original);
    assert!(d.decoded_rows.contains_key(&(root, 0, 2)));
    d.sources
        .push(SourceFile::new("row-coordinate.ash", "()").unwrap(), d.work)
        .unwrap();
    assert_eq!(d.row(root).unwrap(), original);
    assert!(d.decoded_rows.contains_key(&(root, 1, 2)));
    drop(d);
    let donor = decoder(&image, &mut work, ModuleId::new(403))
        .row(root)
        .unwrap();
    assert_ne!(
        donor, original,
        "fresh Decoder preserves distinct module identities"
    );
    let malformed = record(
        &mut image,
        TypeTag::Row {
            known: 1,
            tail: None,
        },
        &[0],
    );
    let mut d = decoder(&image, &mut work, ModuleId::new(401));
    for _ in 0..2 {
        assert!(matches!(d.row(malformed), Err(ImageFailure::InvalidRecord)));
        assert!(
            !d.decoded_rows.contains_key(&(malformed, 0, 1)),
            "malformed raw rows cannot publish a cached value"
        );
    }
}

#[test]
fn decoded_row_nested_hits_preserve_complete_depth_refusal() {
    let limit = crate::core::CORE_PAYLOAD_DEPTH_LIMIT;
    let (mut image, root) = fixture(limit);
    let enclosing = record(&mut image, TypeTag::EffectfulFunction, &[0, 0, root]);
    let mut work = TypeWorkBudget::default();
    let mut d = decoder(&image, &mut work, ModuleId::new(401));
    d.row(root).unwrap();
    assert_eq!(d.decoded_rows[&(root, 0, 1)].depth, limit);
    for _ in 0..2 {
        assert!(matches!(d.ty(enclosing), Err(ImageFailure::Resource)));
        assert!(!d.decoded_types.contains_key(&(enclosing, 0, 1)));
    }
    assert!(
        d.work.remaining() > d.work.limit() / 2,
        "depth refusal is not exhaustion"
    );
}
