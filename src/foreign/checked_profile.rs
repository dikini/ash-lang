//! Checked-profile metadata on the existing canonical prepared library.
//!
//! These facts select original members/formals. They confer no resolved
//! operation, host activation, executable binding or native truth.

use super::*;

/// An unavoidable premise of a checked native operation, not discharged by text.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CheckedNativeAssumption {
    CompilerAndRuntimeIntegrity,
    AuthorizedBuildCorrespondence,
    /// Integrity of the trusted execution roles for the eventual admitted mode.
    /// Isolated mode means parent, kernel and launcher authority, never integrity
    /// of the faulty worker or its monitor. In-process mode additionally relies
    /// on native execution preserving host memory and authority. This passive
    /// premise neither selects a mode nor proves its realization.
    ExecutorIntegrity,
    NativeAbiAndOutcomeTruth,
    NativeInputIntervalValidity,
    NativeInputNonRetention,
    /// The native implementation makes the independently retained copy promised by `copy`.
    NativeIndependentInputCopy,
    /// Native accesses obey declared aliasing and do not interfere with live intervals.
    NativeAliasingAndNonInterference,
    NativeOutputIntervalValidity,
    NativeOwnerLifetimeAndDisposition,
    SerializedNativeAccess,
}

/// One assumption declaration at its original library-member coordinate.
#[derive(Debug)]
pub struct PreparedForeignAssumption {
    member_index: usize,
    name: String,
    description: String,
    origin: Origin,
}

impl PreparedForeignAssumption {
    #[must_use]
    pub const fn member_index(&self) -> usize {
        self.member_index
    }
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
    #[must_use]
    pub fn description(&self) -> &str {
        &self.description
    }
    #[must_use]
    pub const fn origin(&self) -> &Origin {
        &self.origin
    }
}

/// Checked host selection for one original owner; signatures remain in the library.
#[derive(Debug)]
pub struct PreparedCheckedOwnerContract {
    member_index: usize,
    host_parameter: usize,
}
impl PreparedCheckedOwnerContract {
    #[must_use]
    pub const fn member_index(&self) -> usize {
        self.member_index
    }
    #[must_use]
    pub const fn host_parameter(&self) -> usize {
        self.host_parameter
    }
}

/// Checked metadata for one original symbol, without a second signature inventory.
#[derive(Debug)]
pub struct PreparedCheckedSymbolContract {
    member_index: usize,
    host_parameter: usize,
    assumption_members: Vec<usize>,
    minimum_assumptions: Vec<CheckedNativeAssumption>,
}
impl PreparedCheckedSymbolContract {
    #[must_use]
    pub const fn member_index(&self) -> usize {
        self.member_index
    }
    #[must_use]
    pub const fn host_parameter(&self) -> usize {
        self.host_parameter
    }
    #[must_use]
    pub fn assumption_members(&self) -> &[usize] {
        &self.assumption_members
    }
    #[must_use]
    pub fn minimum_assumptions(&self) -> &[CheckedNativeAssumption] {
        &self.minimum_assumptions
    }
}

/// Immutable checked-profile projection of the same prepared library's originals.
///
/// Coordinates refer to that library and its complete ordered parameter vectors.
/// Resolved module identities, exports, host effects and execution need their
/// later independent admission; this projection is not their authority.
#[derive(Debug)]
pub struct PreparedCheckedForeignContract {
    assumptions: Vec<PreparedForeignAssumption>,
    owners: Vec<PreparedCheckedOwnerContract>,
    symbols: Vec<PreparedCheckedSymbolContract>,
}
impl PreparedCheckedForeignContract {
    #[must_use]
    pub fn assumptions(&self) -> &[PreparedForeignAssumption] {
        &self.assumptions
    }
    #[must_use]
    pub fn owners(&self) -> &[PreparedCheckedOwnerContract] {
        &self.owners
    }
    #[must_use]
    pub fn symbols(&self) -> &[PreparedCheckedSymbolContract] {
        &self.symbols
    }
}

fn invalid(span: Span) -> ForeignContractError {
    failure(ForeignContractReason::InvalidCheckedContract, span)
}

fn host_parameter(
    selections: &[crate::surface::SurfaceName],
    parameters: &[PreparedForeignParameter],
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<usize, ForeignContractError> {
    charge(work, selections.len().saturating_add(1), span)?;
    let [selection] = selections else {
        return Err(invalid(span));
    };
    let mut found = None;
    for (index, parameter) in parameters.iter().enumerate() {
        if names_equal(parameter.name(), &selection.text, selection.span, work)? {
            if parameter.kind() != &Kind::Type {
                return Err(invalid(selection.span));
            }
            found = Some(index);
        }
    }
    found.ok_or_else(|| invalid(selection.span))
}

fn check_application(
    contract: &PreparedCheckedForeignContract,
    application: &PreparedOwnerApplication,
    host: usize,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignContractError> {
    charge(work, 2, application.span())?;
    let owner = contract
        .owners
        .get(application.owner())
        .ok_or_else(|| invalid(application.span()))?;
    if application.arguments().get(owner.host_parameter())
        != Some(&PreparedOwnerArgument::Type(host))
    {
        return Err(invalid(application.span()));
    }
    Ok(())
}

fn add_minimum(
    facts: &mut Vec<CheckedNativeAssumption>,
    assumption: CheckedNativeAssumption,
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignContractError> {
    charge(work, facts.len().saturating_add(1), span)?;
    if !facts.contains(&assumption) {
        reserve(facts, 1, span)?;
        facts.push(assumption);
    }
    Ok(())
}

fn minimum_assumptions(
    symbol: &PreparedForeignSymbol,
    work: &mut TypeWorkBudget,
) -> Result<Vec<CheckedNativeAssumption>, ForeignContractError> {
    use CheckedNativeAssumption::*;
    let span = symbol.origin().primary_span();
    let mut result = Vec::new();
    for premise in [
        CompilerAndRuntimeIntegrity,
        AuthorizedBuildCorrespondence,
        ExecutorIntegrity,
        NativeAbiAndOutcomeTruth,
    ] {
        add_minimum(&mut result, premise, span, work)?;
    }
    for operand in symbol.operands() {
        charge(work, 1, span)?;
        match operand.source() {
            PreparedOperandSource::Nul(_) | PreparedOperandSource::Bytes { .. } => {
                add_minimum(&mut result, NativeInputIntervalValidity, span, work)?;
                add_minimum(&mut result, NativeInputNonRetention, span, work)?;
                add_minimum(&mut result, NativeAliasingAndNonInterference, span, work)?;
                if matches!(
                    operand.source(),
                    PreparedOperandSource::Bytes { copy: true, .. }
                ) {
                    add_minimum(&mut result, NativeIndependentInputCopy, span, work)?;
                }
            }
            PreparedOperandSource::Current(_) | PreparedOperandSource::Enclosing(_) => {
                add_minimum(&mut result, NativeOwnerLifetimeAndDisposition, span, work)?;
                add_minimum(&mut result, SerializedNativeAccess, span, work)?;
                add_minimum(&mut result, NativeAliasingAndNonInterference, span, work)?;
            }
            _ => {}
        }
    }
    if symbol.owner_call().is_some() {
        add_minimum(&mut result, NativeOwnerLifetimeAndDisposition, span, work)?;
    }
    if symbol.access_result().is_some()
        || matches!(
            symbol.owner_call(),
            Some(PreparedOwnerCall::Acquire {
                initialized_bytes: Some(_),
                ..
            })
        )
    {
        add_minimum(&mut result, NativeOutputIntervalValidity, span, work)?;
        add_minimum(&mut result, NativeAliasingAndNonInterference, span, work)?;
        add_minimum(&mut result, SerializedNativeAccess, span, work)?;
    }
    Ok(result)
}

pub(super) fn prepare(
    library: &PreparedForeignLibrary,
    source: &SurfaceForeignLibrary,
    work: &mut TypeWorkBudget,
) -> Result<PreparedCheckedForeignContract, ForeignContractError> {
    let mut result = PreparedCheckedForeignContract {
        assumptions: Vec::new(),
        owners: Vec::new(),
        symbols: Vec::new(),
    };
    charge(work, source.members.len(), source.span)?;
    for (member_index, member) in source.members.iter().enumerate() {
        if let SurfaceForeignMember::Assumption(assumption) = member {
            reserve(&mut result.assumptions, 1, assumption.span)?;
            result.assumptions.push(PreparedForeignAssumption {
                member_index,
                name: text(&assumption.name.text, assumption.name.span, work)?,
                description: text(
                    &assumption.description.value,
                    assumption.description.span,
                    work,
                )?,
                origin: Origin::Source(assumption.span),
            });
        }
    }
    reserve(&mut result.owners, library.owners().len(), source.span)?;
    for owner in library.owners() {
        charge(work, 1, source.span)?;
        let Some(SurfaceForeignMember::Owner(original)) = source.members.get(owner.member_index())
        else {
            return Err(invalid(source.span));
        };
        let host = host_parameter(
            &original.host_bindings,
            owner.parameters(),
            original.span,
            work,
        )?;
        charge(
            work,
            owner.retained_parameters().len().saturating_add(1),
            original.span,
        )?;
        if host == owner.owned_parameter() || owner.retained_parameters().contains(&host) {
            return Err(invalid(original.span));
        }
        result.owners.push(PreparedCheckedOwnerContract {
            member_index: owner.member_index(),
            host_parameter: host,
        });
    }
    reserve(&mut result.symbols, library.symbols().len(), source.span)?;
    for symbol in library.symbols() {
        charge(work, 1, source.span)?;
        let Some(SurfaceForeignMember::Symbol(original)) =
            source.members.get(symbol.member_index())
        else {
            return Err(invalid(source.span));
        };
        let host = host_parameter(
            &original.host_bindings,
            symbol.parameters(),
            original.span,
            work,
        )?;
        charge(
            work,
            original.assumption_sets.len().saturating_add(1),
            original.span,
        )?;
        let [references] = original.assumption_sets.as_slice() else {
            return Err(invalid(original.span));
        };
        let mut members = Vec::new();
        charge(work, references.references.len(), references.span)?;
        reserve(&mut members, references.references.len(), references.span)?;
        for reference in &references.references {
            if let Some(qualifier) = &reference.module
                && !names_equal(&qualifier.text, library.name(), qualifier.span, work)?
            {
                return Err(invalid(reference.span));
            }
            let mut selected = None;
            for declaration in &result.assumptions {
                if names_equal(
                    declaration.name(),
                    &reference.name.text,
                    reference.span,
                    work,
                )? {
                    selected = Some(declaration.member_index());
                }
            }
            let member = selected.ok_or_else(|| invalid(reference.span))?;
            charge(work, members.len().saturating_add(1), reference.span)?;
            if members.contains(&member) {
                return Err(invalid(reference.span));
            }
            members.push(member);
        }
        if let Some(call) = symbol.owner_call() {
            check_application(&result, call.application(), host, work)?;
        }
        let SurfaceTypeKind::Function(function) = &original.ty.kind else {
            return Err(invalid(original.ty.span));
        };
        for clause in &original.contracts {
            charge(work, 1, original.span)?;
            if let SurfaceForeignContract::Operand {
                source: SurfaceForeignOperandSource::Source { position, role },
                ..
            } = clause
                && matches!(
                    role.kind,
                    SurfaceForeignOperandRoleKind::Current
                        | SurfaceForeignOperandRoleKind::Enclosing
                )
            {
                let (_, state) = owner_source_path(position, &function.domain, work)?;
                let application = owner_application(library, symbol, state, work)?;
                check_application(&result, &application, host, work)?;
            }
        }
        result.symbols.push(PreparedCheckedSymbolContract {
            member_index: symbol.member_index(),
            host_parameter: host,
            assumption_members: members,
            minimum_assumptions: minimum_assumptions(symbol, work)?,
        });
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        lexer::lex,
        parser::{parse, project_module},
        source::SourceFile,
    };

    const CHECKED: &str = r#"foreign checked library Native {
    profile "x86_64-unknown-linux-gnu"
    assumption Behavior "Native execution obeys the declared outcome contract."
    repr CInt = signed(32)
    symbol Abs<A, H, Delta : EffectRow> : Int -> Foreign.CheckedCall<Int> {
        name "abs"
        abi (CInt) -> CInt
        host H
        assumes {Behavior}
        operand 0 from 0 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
}
"#;

    fn source(text: &str) -> (ModuleId, crate::surface::SurfaceModule) {
        let source = SourceFile::new("checked-profile-work.ash", text).unwrap();
        let tree = parse(lex(&source).unwrap());
        assert!(
            tree.parse_diagnostics().is_empty(),
            "{:?}",
            tree.parse_diagnostics()
        );
        (
            ModuleId::from(source.id()),
            project_module(&source, &tree).unwrap(),
        )
    }

    #[test]
    fn checked_profile_charges_assumption_reference_cardinality_before_selection() {
        let (module, mut surface) = source(CHECKED);
        let library =
            prepare_checked_foreign_library(module, &surface.foreign_libraries[0]).unwrap();
        let SurfaceForeignMember::Symbol(symbol) = &mut surface.foreign_libraries[0].members[3]
        else {
            panic!("symbol");
        };
        let mut missing = symbol.assumption_sets[0].references[0].clone();
        missing.name.text = "Missing".into();
        symbol.assumption_sets[0].references = vec![missing; 4096];
        // Without the up-front cardinality charge the first unknown name would
        // report InvalidCheckedContract after an attacker-sized reservation.
        let error = prepare(
            &library,
            &surface.foreign_libraries[0],
            &mut TypeWorkBudget::with_limit(1024),
        )
        .unwrap_err();
        assert_eq!(error.reason(), ForeignContractReason::WorkExhausted);
    }

    #[test]
    fn checked_profile_preparation_charges_exact_cumulative_work_and_refuses_one_short() {
        let (module, surface) = source(CHECKED);
        let source = &surface.foreign_libraries[0];
        let mut measured = TypeWorkBudget::default();
        let original =
            prepare_checked_foreign_library_with_budget(module, source, &mut measured).unwrap();
        let exact = measured.used();
        assert!(exact > 0);
        for prefix in [0, 17] {
            let mut short = TypeWorkBudget::with_limit(prefix + exact - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                prepare_checked_foreign_library_with_budget(module, source, &mut short)
                    .unwrap_err()
                    .reason(),
                ForeignContractReason::WorkExhausted
            );
            let mut enough = TypeWorkBudget::with_limit(prefix + exact);
            enough.charge(prefix).unwrap();
            let fresh =
                prepare_checked_foreign_library_with_budget(module, source, &mut enough).unwrap();
            assert_eq!(enough.used(), prefix + exact);
            assert_eq!(
                fresh.checked_contract().unwrap().symbols()[0].host_parameter(),
                original.checked_contract().unwrap().symbols()[0].host_parameter()
            );
        }
    }

    #[test]
    fn checked_profile_metadata_cannot_be_erased_by_legacy_private_reconstruction() {
        let (module, surface) = source(CHECKED);
        let original =
            prepare_checked_foreign_library(module, &surface.foreign_libraries[0]).unwrap();
        let candidate = super::super::owner_normalization_tests::parts(&original);
        assert!(
            !same_prepared_library_parts(&original, &candidate, &mut TypeWorkBudget::default())
                .unwrap()
        );
        // The legacy format requires contiguous originals; an assumption gap is
        // not a valid legacy reconstruction either. Use a genuine legacy donor.
        let legacy_text = CHECKED.replace("foreign checked library", "foreign library")
            .replace("    assumption Behavior \"Native execution obeys the declared outcome contract.\"\n", "")
            .replace("        host H\n", "")
            .replace("        assumes {Behavior}\n", "");
        let (legacy_id, legacy_surface) = source(&legacy_text);
        let legacy =
            prepare_foreign_library(legacy_id, &legacy_surface.foreign_libraries[0]).unwrap();
        let restored = restore_prepared_library(
            super::super::owner_normalization_tests::parts(&legacy),
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        assert!(restored.checked_contract().is_none());
        // Decoding an ABI-shaped donor does not grant original checked authority.
        let donor = super::super::owner_normalization_tests::parts(&restored);
        assert!(
            !same_prepared_library_parts(&original, &donor, &mut TypeWorkBudget::default())
                .unwrap()
        );
    }

    #[test]
    fn checked_profile_assumption_description_copy_uses_the_same_work_meter() {
        let short_text =
            CHECKED.replace("Native execution obeys the declared outcome contract.", "x");
        let long_text = CHECKED.replace(
            "Native execution obeys the declared outcome contract.",
            &"x".repeat(4096),
        );
        let (short_id, short_surface) = source(&short_text);
        let (long_id, long_surface) = source(&long_text);
        let mut short = TypeWorkBudget::default();
        let mut long = TypeWorkBudget::default();
        prepare_checked_foreign_library_with_budget(
            short_id,
            &short_surface.foreign_libraries[0],
            &mut short,
        )
        .unwrap();
        prepare_checked_foreign_library_with_budget(
            long_id,
            &long_surface.foreign_libraries[0],
            &mut long,
        )
        .unwrap();
        assert_eq!(long.used() - short.used(), 4095);
    }
}
