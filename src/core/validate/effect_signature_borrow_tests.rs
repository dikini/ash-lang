//! Local Type replacements borrow an already freshly checked effect instance.
use super::*;
use crate::resolved::{
    ResolvedEffectDeclaration, ResolvedEffectOperation, ResolvedType, ResolvedTypeProvenance,
    ResolvedTypeProvenanceNode, ResolvedTypeVariable,
};

fn row(effect: crate::types::EffectId) -> EffectRow {
    EffectRow::closed(Box::new([EffectInstance::new(effect, Box::new([]))]))
}
fn compound(effect: crate::types::EffectId) -> Type {
    Type::Tuple(Box::new([
        Type::function(Type::Int, Type::Int),
        Type::EffectfulFunction(
            Box::new(Type::Unit),
            Box::new(crate::types::ComputationType::new(Type::Unit, row(effect))),
        ),
    ]))
}
fn fixture() -> (
    SourceFile,
    crate::core::UnvalidatedEffectProgram,
    NodeId,
    crate::types::EffectId,
    crate::types::EffectId,
) {
    let file = SourceFile::new("borrowed-signature.ash", "effect Ask").unwrap();
    let span = file
        .span(crate::source::ByteRange::new(0, 10).unwrap())
        .unwrap();
    let origin = Origin::Source(span);
    let module = ModuleId::from(file.id());
    let effect = crate::types::EffectId::new(module, 0);
    let marker = crate::types::EffectId::new(module, 1);
    let t = crate::types::TypeVariableId::resolved(module, 0);
    let r = crate::types::TypeVariableId::resolved(module, 1);
    let parameters = vec![
        ResolvedTypeVariable {
            id: t,
            spelling: "T".into(),
            kind: Kind::Type,
            origin: origin.clone(),
        },
        ResolvedTypeVariable {
            id: r,
            spelling: "R".into(),
            kind: Kind::EffectRow,
            origin: origin.clone(),
        },
    ];
    let operation = ResolvedEffectOperation {
        id: OperationId::new(effect, 0),
        spelling: "ask".into(),
        annotation: ResolvedType {
            ty: Type::Function(
                Box::new(Type::Variable(t)),
                Box::new(Type::EffectfulFunction(
                    Box::new(Type::Variable(t)),
                    Box::new(crate::types::ComputationType::new(
                        Type::Variable(t),
                        EffectRow::open(crate::types::EffectRowVariable::Rigid(r), Box::new([])),
                    )),
                )),
            ),
            provenance: ResolvedTypeProvenance::new(
                vec![ResolvedTypeProvenanceNode::Fact(span)],
                0,
            ),
            origin: origin.clone(),
            span,
        },
        origin: origin.clone(),
        span,
    };
    let registry = crate::resolved::ResolvedRegistry::default()
        .with_effects(vec![
            ResolvedEffectDeclaration {
                native_contract: None,
                id: effect,
                public: false,
                spelling: "Ask".into(),
                parameters: parameters.clone().into_boxed_slice(),
                operations: Box::new([operation]),
                origin: origin.clone(),
                span,
            },
            ResolvedEffectDeclaration {
                native_contract: None,
                id: marker,
                public: false,
                spelling: "Marker".into(),
                parameters: Box::new([]),
                operations: Box::new([]),
                origin: origin.clone(),
                span,
            },
        ])
        .with_additional_type_variables(parameters);
    let mut builder = crate::core::EffectCoreBuilder::with_effect_registry(Arc::new(registry));
    let root = builder.unit(Type::Unit, origin).unwrap();
    (file, builder.finish(root).unwrap(), root, effect, marker)
}
fn instance(effect: crate::types::EffectId, marker: crate::types::EffectId) -> EffectInstance {
    EffectInstance::new_kinded(
        effect,
        Box::new([
            crate::types::KindedArgument::TypeArg(compound(marker)),
            crate::types::KindedArgument::RowArg(row(marker)),
        ]),
    )
}

#[test]
fn borrowed_effect_signature_keeps_full_type_row_outputs_and_refusals() {
    let (file, program, root, effect, marker) = fixture();
    let binders = HashMap::new();
    let canonical = instance(effect, marker);
    let validator = Validator::new(&program, &[&file]);
    let (domain, result) = validator
        .effect_signature(&canonical, OperationId::new(effect, 0), root, &binders)
        .unwrap();
    drop(canonical);
    assert_eq!(&*domain, &compound(marker));
    assert_eq!(
        &*result,
        &Type::EffectfulFunction(
            Box::new(compound(marker)),
            Box::new(crate::types::ComputationType::new(
                compound(marker),
                row(marker)
            ))
        )
    );
    let canonical = instance(effect, marker);
    for (actual, operation, cause) in [
        (
            canonical.clone(),
            OperationId::new(marker, 0),
            ValidationCause::CoreOperationOwner,
        ),
        (
            canonical.clone(),
            OperationId::new(effect, 1),
            ValidationCause::UnknownCoreOperation,
        ),
        (
            EffectInstance::new(effect, Box::new([])),
            OperationId::new(effect, 0),
            ValidationCause::CoreEffectArgumentCount,
        ),
        (
            EffectInstance::new_kinded(
                effect,
                Box::new([
                    crate::types::KindedArgument::RowArg(row(marker)),
                    crate::types::KindedArgument::TypeArg(Type::Unit),
                ]),
            ),
            OperationId::new(effect, 0),
            ValidationCause::CoreEffectArgumentKind,
        ),
        (
            EffectInstance::new_kinded(
                effect,
                Box::new([
                    crate::types::KindedArgument::TypeArg(Type::Application(
                        Box::new(Type::Int),
                        Box::new(Type::Int),
                    )),
                    crate::types::KindedArgument::RowArg(row(marker)),
                ]),
            ),
            OperationId::new(effect, 0),
            ValidationCause::CoreEffectInvalidArgument,
        ),
    ] {
        // Fresh canonical signature first; the hostile cannot obtain credit
        // from a malformed fixture or from spending the positive's meter.
        Validator::new(&program, &[&file])
            .effect_signature(&canonical, OperationId::new(effect, 0), root, &binders)
            .unwrap();
        let error = Validator::new(&program, &[&file])
            .effect_signature(&actual, operation, root, &binders)
            .err()
            .unwrap();
        assert_eq!(error.cause, Some(cause));
    }
}

#[test]
fn borrowed_effect_signature_keeps_exact_prefix_short_spent_and_fresh_work() {
    let (file, program, root, effect, marker) = fixture();
    let actual = instance(effect, marker);
    let binders = HashMap::new();
    let measured = Validator::new(&program, &[&file]);
    measured
        .effect_signature(&actual, OperationId::new(effect, 0), root, &binders)
        .unwrap();
    let cost = measured.type_work.get();
    assert!(cost > 0);
    for prefix in [0, 7] {
        let mut short = Validator::new(&program, &[&file]);
        short.type_work_limit = prefix + cost - 1;
        short.type_work.set(prefix);
        let error = short
            .effect_signature(&actual, OperationId::new(effect, 0), root, &binders)
            .err()
            .unwrap();
        assert_eq!(error.reason(), ValidationReason::Resource);
        let spent = short.type_work.get();
        assert_eq!(
            short
                .effect_signature(&actual, OperationId::new(effect, 0), root, &binders)
                .err()
                .unwrap()
                .reason(),
            ValidationReason::Resource
        );
        assert!(short.type_work.get() >= spent);
        for _ in 0..2 {
            let mut exact = Validator::new(&program, &[&file]);
            exact.type_work_limit = prefix + cost;
            exact.type_work.set(prefix);
            let (domain, result) = exact
                .effect_signature(&actual, OperationId::new(effect, 0), root, &binders)
                .unwrap();
            assert_eq!(&*domain, &compound(marker));
            assert!(matches!(&*result, Type::EffectfulFunction(..)));
            assert_eq!(exact.type_work.get(), prefix + cost);
        }
    }
}
