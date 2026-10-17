//! Preparation of a scalar status and one initialized opaque owner-output slot.

use super::{
    ForeignContractError, ForeignContractReason, PreparedAbiResult, PreparedAddressRepresentation,
    PreparedForeignCall, PreparedForeignLibrary, PreparedForeignOperand, PreparedForeignSymbol,
    PreparedNativePosition, PreparedOffsetOutput, PreparedOperandSource, PreparedOwnerCall,
    PreparedRepresentation, SurfaceForeignContract, SurfaceForeignOperandRoleKind,
    SurfaceForeignOperandSource, SurfaceForeignOutcomeCondition, SurfaceForeignOutcomeFactKind,
    SurfaceForeignOutcomeTest, SurfaceForeignOutputRoleKind, SurfaceForeignSymbol, SurfaceType,
    SurfaceTypeKind, TypeWorkBudget, abi_result, charge, constant, failure, native_position,
    owner_application, owner_source_path, reserve, source_path,
};
use crate::{source::Origin, surface::SurfaceForeignInputDiscipline};

pub(super) fn prepare(
    library: &PreparedForeignLibrary,
    source: &SurfaceForeignSymbol,
    mut symbol: PreparedForeignSymbol,
    domain: &SurfaceType,
    work: &mut TypeWorkBudget,
) -> Result<PreparedForeignSymbol, ForeignContractError> {
    if !matches!(symbol.result, PreparedAbiResult::Scalar(_)) {
        return Err(failure(ForeignContractReason::OutputRole, source.span));
    }
    charge(work, source.abi_operands.len(), source.span)?;
    let mut mappings = Vec::new();
    reserve(&mut mappings, source.abi_operands.len(), source.span)?;
    mappings.resize_with(source.abi_operands.len(), || None);
    let mut owner = None;
    let mut scalar = None;
    let mut offset_role = None;
    let mut cases = Vec::new();
    reserve(&mut cases, 2, source.span)?;
    for contract in &source.contracts {
        charge(work, 1, source.span)?;
        match contract {
            SurfaceForeignContract::DestructionOperand { .. } => {}
            SurfaceForeignContract::Operand {
                position,
                source: input,
                span,
            } => {
                let PreparedNativePosition::Argument(index) = native_position(position, work)?
                else {
                    return Err(failure(ForeignContractReason::OperandCoverage, *span));
                };
                let slot = mappings
                    .get_mut(index)
                    .ok_or_else(|| failure(ForeignContractReason::OperandCoverage, *span))?;
                if slot.replace(input).is_some() {
                    return Err(failure(ForeignContractReason::OperandCoverage, *span));
                }
            }
            SurfaceForeignContract::Output {
                position,
                role,
                span,
            } => match (native_position(position, work)?, &role.kind) {
                (PreparedNativePosition::Result, SurfaceForeignOutputRoleKind::Scalar)
                    if scalar.is_none() =>
                {
                    scalar = Some(*span);
                }
                (
                    PreparedNativePosition::Argument(index),
                    SurfaceForeignOutputRoleKind::Owner(ty),
                ) if owner.is_none() => {
                    owner = Some((index, owner_application(library, &symbol, ty, work)?, *span));
                }
                (
                    PreparedNativePosition::Argument(index),
                    SurfaceForeignOutputRoleKind::OffsetInto(position),
                ) if offset_role.is_none() => {
                    offset_role = Some((index, position, *span));
                }
                _ => return Err(failure(ForeignContractReason::OutputCoverage, *span)),
            },
            SurfaceForeignContract::Outcome { test, facts, span } => {
                if cases.len() == 2 {
                    return Err(failure(ForeignContractReason::UnimplementedContract, *span));
                }
                cases.push((test, facts.as_slice(), *span));
            }
            SurfaceForeignContract::RetainedDependentsBlock { span } => {
                return Err(failure(ForeignContractReason::OperandRole, *span));
            }
        }
    }
    let scalar_output_span =
        scalar.ok_or_else(|| failure(ForeignContractReason::OutputCoverage, source.span))?;
    let (output_operand, application, output_span) =
        owner.ok_or_else(|| failure(ForeignContractReason::OutputCoverage, source.span))?;
    let Some(output) = source.abi_operands.get(output_operand) else {
        return Err(failure(ForeignContractReason::OutputCoverage, output_span));
    };
    if !output.output
        || abi_result(library, &output.representation, work)?
            != PreparedAbiResult::Address(PreparedAddressRepresentation::Opaque)
        || library.owners[application.owner].representation != PreparedAddressRepresentation::Opaque
    {
        return Err(failure(ForeignContractReason::OutputRole, output_span));
    }
    let (test, facts, outcome_span) = cases
        .first()
        .copied()
        .ok_or_else(|| failure(ForeignContractReason::OutcomeCoverage, source.span))?;
    let (readable_spans, offset_readable) = readability(
        facts,
        output_operand,
        offset_role.map(|(index, _, _)| (index, true)),
        outcome_span,
        work,
    )?;
    let mut offset = if let Some((operand, position, output_span)) = offset_role {
        let Some(abi) = source.abi_operands.get(operand) else {
            return Err(failure(ForeignContractReason::OutputCoverage, output_span));
        };
        if operand <= output_operand
            || !abi.output
            || abi_result(library, &abi.representation, work)?
                != PreparedAbiResult::Address(PreparedAddressRepresentation::Bytes)
            || cases.len() != 2
            || !matches!(cases[1].0, SurfaceForeignOutcomeTest::Otherwise(_))
        {
            return Err(failure(ForeignContractReason::OutputRole, output_span));
        }
        let SurfaceForeignOutcomeTest::All(atoms) = test else {
            return Err(failure(
                ForeignContractReason::OutcomeCoverage,
                outcome_span,
            ));
        };
        let [atom] = atoms.as_slice() else {
            return Err(failure(
                ForeignContractReason::OutcomeCoverage,
                outcome_span,
            ));
        };
        let SurfaceForeignOutcomeCondition::Equal(reference) = &atom.condition else {
            return Err(failure(ForeignContractReason::OutcomeCoverage, atom.span));
        };
        let (_, value) = constant(library, reference, work)?;
        if native_position(&atom.position, work)? != PreparedNativePosition::Result
            || symbol.result != PreparedAbiResult::Scalar(value.representation)
        {
            return Err(failure(ForeignContractReason::OutcomeCoverage, atom.span));
        }
        let (otherwise, unreadable) = readability(
            cases[1].1,
            output_operand,
            Some((operand, false)),
            cases[1].2,
            work,
        )?;
        Some((
            PreparedOffsetOutput {
                operand,
                input_operand: 0,
                output_span,
                status: value.value,
                condition_span: atom.span,
                readable_span: offset_readable
                    .ok_or_else(|| failure(ForeignContractReason::Readability, outcome_span))?,
                otherwise_span: cases[1].2,
                otherwise_readable_spans: [
                    otherwise[0],
                    otherwise[1],
                    unreadable
                        .ok_or_else(|| failure(ForeignContractReason::Readability, cases[1].2))?,
                ],
            },
            position,
        ))
    } else {
        if cases.len() != 1 || !matches!(test, SurfaceForeignOutcomeTest::Otherwise(_)) {
            return Err(failure(
                ForeignContractReason::OutcomeCoverage,
                outcome_span,
            ));
        }
        None
    };
    reserve(&mut symbol.operands, source.abi_operands.len(), source.span)?;
    for (index, operand) in source.abi_operands.iter().enumerate() {
        charge(work, 1, operand.span)?;
        let representation = abi_result(library, &operand.representation, work)?;
        let (representation, input) = if operand.output {
            if mappings[index].is_some() {
                return Err(failure(ForeignContractReason::OutputCoverage, operand.span));
            }
            if index == output_operand {
                (
                    PreparedRepresentation::Address(PreparedAddressRepresentation::Opaque),
                    PreparedOperandSource::OwnerOutput,
                )
            } else if offset
                .as_ref()
                .is_some_and(|(offset, _)| offset.operand == index)
            {
                (
                    PreparedRepresentation::Address(PreparedAddressRepresentation::Bytes),
                    PreparedOperandSource::OffsetOutput,
                )
            } else {
                return Err(failure(ForeignContractReason::OutputCoverage, operand.span));
            }
        } else {
            let input = mappings[index]
                .ok_or_else(|| failure(ForeignContractReason::OperandCoverage, operand.span))?;
            match (representation, input) {
                (
                    PreparedAbiResult::Scalar(representation),
                    SurfaceForeignOperandSource::Source { position, role },
                ) if matches!(role.kind, SurfaceForeignOperandRoleKind::Scalar) => (
                    PreparedRepresentation::Scalar(representation),
                    PreparedOperandSource::Source(source_path(position, domain, work)?),
                ),
                (
                    PreparedAbiResult::Scalar(representation),
                    SurfaceForeignOperandSource::Constant(reference),
                ) => {
                    let (index, value) = constant(library, reference, work)?;
                    if value.representation != representation {
                        return Err(failure(ForeignContractReason::OperandRole, reference.span));
                    }
                    (
                        PreparedRepresentation::Scalar(representation),
                        PreparedOperandSource::Constant(index),
                    )
                }
                (
                    PreparedAbiResult::Address(PreparedAddressRepresentation::Bytes),
                    SurfaceForeignOperandSource::Source { position, role },
                ) if matches!(
                    role.kind,
                    SurfaceForeignOperandRoleKind::Nul(SurfaceForeignInputDiscipline::CallBorrow(
                        _
                    ))
                ) =>
                {
                    let (path, ty) = owner_source_path(position, domain, work)?;
                    if !matches!(ty.kind, SurfaceTypeKind::String) {
                        return Err(failure(
                            ForeignContractReason::SourcePosition,
                            position.span,
                        ));
                    }
                    (
                        PreparedRepresentation::Address(PreparedAddressRepresentation::Bytes),
                        PreparedOperandSource::Nul(path),
                    )
                }
                (
                    PreparedAbiResult::Address(representation),
                    SurfaceForeignOperandSource::Null(_),
                ) => (
                    PreparedRepresentation::Address(representation),
                    PreparedOperandSource::Null,
                ),
                (
                    PreparedAbiResult::Address(representation),
                    SurfaceForeignOperandSource::Source { position, role },
                ) if matches!(role.kind, SurfaceForeignOperandRoleKind::Enclosing) => (
                    PreparedRepresentation::Address(representation),
                    PreparedOperandSource::Enclosing(owner_source_path(position, domain, work)?.0),
                ),
                (PreparedAbiResult::Void, _) => {
                    return Err(failure(ForeignContractReason::VoidPosition, operand.span));
                }
                _ => {
                    return Err(failure(
                        ForeignContractReason::UnimplementedContract,
                        operand.span,
                    ));
                }
            }
        };
        symbol.operands.push(PreparedForeignOperand {
            representation,
            source: input,
            origin: Origin::Source(operand.span),
        });
    }
    if let Some((offset, position)) = &mut offset {
        let (path, ty) = owner_source_path(position, domain, work)?;
        if !matches!(ty.kind, SurfaceTypeKind::String) {
            return Err(failure(
                ForeignContractReason::SourcePosition,
                position.span,
            ));
        }
        let mut selected = None;
        charge(work, symbol.operands.len(), position.span)?;
        for (index, operand) in symbol.operands.iter().enumerate() {
            if matches!(&operand.source, PreparedOperandSource::Nul(input) if *input == path)
                && selected.replace(index).is_some()
            {
                return Err(failure(
                    ForeignContractReason::OperandCoverage,
                    position.span,
                ));
            }
        }
        offset.input_operand = selected
            .ok_or_else(|| failure(ForeignContractReason::SourcePosition, position.span))?;
    }
    symbol.call = PreparedForeignCall::Owner(PreparedOwnerCall::OutputAcquire {
        application,
        output_operand,
        output_span,
        scalar_output_span,
        outcome_span,
        readable_spans,
        offset: offset.map(|(offset, _)| offset),
    });
    Ok(symbol)
}

fn readability(
    facts: &[super::SurfaceForeignOutcomeFact],
    owner: usize,
    offset: Option<(usize, bool)>,
    span: crate::source::Span,
    work: &mut TypeWorkBudget,
) -> Result<([crate::source::Span; 2], Option<crate::source::Span>), ForeignContractError> {
    let mut spans = [None; 3];
    charge(work, facts.len(), span)?;
    for fact in facts {
        let (position, readable) = match &fact.kind {
            SurfaceForeignOutcomeFactKind::Readable(position) => {
                (native_position(position, work)?, true)
            }
            SurfaceForeignOutcomeFactKind::Unreadable(position) => {
                (native_position(position, work)?, false)
            }
            _ => return Err(failure(ForeignContractReason::Readability, fact.span)),
        };
        let index = match position {
            PreparedNativePosition::Result if readable => 0,
            PreparedNativePosition::Argument(index) if index == owner && readable => 1,
            PreparedNativePosition::Argument(index) if offset == Some((index, readable)) => 2,
            _ => return Err(failure(ForeignContractReason::Readability, fact.span)),
        };
        if spans[index].replace(fact.span).is_some() {
            return Err(failure(ForeignContractReason::Readability, fact.span));
        }
    }
    let [Some(scalar), Some(owner), tail] = spans else {
        return Err(failure(ForeignContractReason::Readability, span));
    };
    if tail.is_some() != offset.is_some() {
        return Err(failure(ForeignContractReason::Readability, span));
    }
    Ok(([scalar, owner], tail))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        foreign::source_contract::prepare_foreign_library_with_budget,
        lexer::lex,
        module::ModuleId,
        parser::{parse, project_module},
        source::SourceFile,
    };

    #[test]
    fn opaque_output_preparation_has_exact_short_prefix_and_fresh_retries() {
        let source =
            SourceFile::new("sqlite.ash", include_str!("../../libraries/sqlite.ash")).unwrap();
        let surface = project_module(&source, &parse(lex(&source).unwrap())).unwrap();
        let authored = &surface.foreign_libraries[0];
        let module = ModuleId::from(source.id());
        let mut measured = TypeWorkBudget::default();
        prepare_foreign_library_with_budget(module, authored, &mut measured).unwrap();
        let exact = measured.used();
        for prefix in [0, 23] {
            for _ in 0..2 {
                let mut short = TypeWorkBudget::with_limit(prefix + exact - 1);
                short.charge(prefix).unwrap();
                assert_eq!(
                    prepare_foreign_library_with_budget(module, authored, &mut short)
                        .unwrap_err()
                        .reason(),
                    ForeignContractReason::WorkExhausted
                );
                assert!(short.used() >= prefix && short.used() < prefix + exact);
                let mut work = TypeWorkBudget::with_limit(prefix + exact);
                work.charge(prefix).unwrap();
                prepare_foreign_library_with_budget(module, authored, &mut work).unwrap();
                assert_eq!(work.used(), prefix + exact);
            }
        }
    }
}
