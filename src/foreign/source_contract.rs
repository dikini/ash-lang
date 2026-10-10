//! ABI preparation for source-authored foreign libraries.
//!
//! Prepared facts have no resolved operation or constructor authority. Ordinary
//! module checking must bind them to their defining identities and source types.
//! This first slice admits owner-free scalar calls; other contract forms reject
//! explicitly rather than publishing partially checked native authority.
//! Higher-kinded symbol parameters await the resolved binding phase; ordinary
//! Ash higher-kinded types are unaffected by this preparation subset.

use std::{error::Error, fmt};

use crate::{
    module::ModuleId,
    source::{Origin, Span},
    surface::*,
    types::{Kind, TypeWorkBudget},
};

const PROFILE: &str = "x86_64-unknown-linux-gnu";

/// The cause of source foreign ABI preparation refusal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ForeignContractReason {
    MissingProfile,
    DuplicateProfile,
    UnsupportedProfile,
    DuplicateMember,
    UnsupportedRepresentation,
    UnknownMember,
    ConstantRange,
    VoidPosition,
    OperandCoverage,
    OperandRole,
    SourcePosition,
    SourceSignature,
    OutputCoverage,
    OutputRole,
    OutcomeCoverage,
    OverlappingOutcomes,
    Readability,
    InvalidParameters,
    InvalidNativeName,
    UnimplementedContract,
    WorkExhausted,
    StorageRefused,
}

/// A causal source location and preparation refusal, without native side effects.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ForeignContractError {
    reason: ForeignContractReason,
    span: Span,
}

impl ForeignContractError {
    #[must_use]
    pub const fn reason(self) -> ForeignContractReason {
        self.reason
    }
    #[must_use]
    pub const fn span(self) -> Span {
        self.span
    }
    #[must_use]
    pub const fn is_resource_exhaustion(self) -> bool {
        matches!(
            self.reason,
            ForeignContractReason::WorkExhausted | ForeignContractReason::StorageRefused
        )
    }
}

impl fmt::Display for ForeignContractError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self.reason {
            ForeignContractReason::MissingProfile => {
                "foreign library requires an explicit target profile"
            }
            ForeignContractReason::DuplicateProfile => {
                "foreign library declares its profile more than once"
            }
            ForeignContractReason::UnsupportedProfile => "foreign target profile is unsupported",
            ForeignContractReason::DuplicateMember => {
                "foreign library members must have disjoint names"
            }
            ForeignContractReason::UnsupportedRepresentation => {
                "foreign scalar representation is unsupported"
            }
            ForeignContractReason::UnknownMember => {
                "foreign member reference has no matching local declaration"
            }
            ForeignContractReason::ConstantRange => {
                "foreign constant is outside its declared representation"
            }
            ForeignContractReason::VoidPosition => "void is legal only as a foreign result",
            ForeignContractReason::OperandCoverage => {
                "foreign input positions require exactly one operand mapping"
            }
            ForeignContractReason::OperandRole => {
                "foreign operand role disagrees with its representation"
            }
            ForeignContractReason::SourcePosition => {
                "foreign source position does not select an integer leaf"
            }
            ForeignContractReason::SourceSignature => {
                "foreign symbol requires a pure source function signature"
            }
            ForeignContractReason::OutputCoverage => {
                "foreign outputs require exactly one result role"
            }
            ForeignContractReason::OutputRole => {
                "foreign output role disagrees with its representation"
            }
            ForeignContractReason::OutcomeCoverage => {
                "foreign outcomes require one final otherwise alternative"
            }
            ForeignContractReason::OverlappingOutcomes => {
                "foreign outcome alternatives overlap or contradict themselves"
            }
            ForeignContractReason::Readability => {
                "foreign outcome must declare every scalar result readable exactly once"
            }
            ForeignContractReason::InvalidParameters => {
                "foreign symbol parameters have duplicate names or unsupported kinds"
            }
            ForeignContractReason::InvalidNativeName => {
                "foreign symbol name must be nonempty and contain no NUL"
            }
            ForeignContractReason::UnimplementedContract => {
                "foreign contract form is not implemented by this scalar preparation slice"
            }
            ForeignContractReason::WorkExhausted => "foreign contract preparation work exhausted",
            ForeignContractReason::StorageRefused => "foreign contract preparation storage refused",
        })
    }
}
impl Error for ForeignContractError {}

fn failure(reason: ForeignContractReason, span: Span) -> ForeignContractError {
    ForeignContractError { reason, span }
}
fn charge(work: &mut TypeWorkBudget, units: usize, span: Span) -> Result<(), ForeignContractError> {
    work.charge(units)
        .map_err(|()| failure(ForeignContractReason::WorkExhausted, span))
}
fn reserve<T>(values: &mut Vec<T>, count: usize, span: Span) -> Result<(), ForeignContractError> {
    values
        .try_reserve_exact(count)
        .map_err(|_| failure(ForeignContractReason::StorageRefused, span))
}
fn text(
    source: &str,
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<String, ForeignContractError> {
    charge(work, source.len(), span)?;
    let mut result = String::new();
    result
        .try_reserve(source.len())
        .map_err(|_| failure(ForeignContractReason::StorageRefused, span))?;
    result.push_str(source);
    Ok(result)
}

fn names_equal(
    left: &str,
    right: &str,
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<bool, ForeignContractError> {
    // Unequal lengths reject without inspecting contents. Equal lengths may
    // scan every byte, including a long shared prefix, so pay before comparing.
    let bytes = if left.len() == right.len() {
        left.len()
    } else {
        0
    };
    charge(work, bytes.saturating_add(1), span)?;
    Ok(left == right)
}

/// A scalar ABI representation; these are not new ordinary Ash value types.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PreparedScalarRepresentation {
    Signed(u8),
    Unsigned(u8),
    SizeT,
}

/// A source-authored scalar value retained without mathematical narrowing.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PreparedScalarValue {
    pub negative: bool,
    pub magnitude: u64,
}

/// One unresolved representation declaration after profile checking.
#[derive(Debug)]
pub struct PreparedForeignRepresentation {
    name: String,
    representation: PreparedScalarRepresentation,
    origin: Origin,
}
impl PreparedForeignRepresentation {
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
    #[must_use]
    pub const fn representation(&self) -> PreparedScalarRepresentation {
        self.representation
    }
    #[must_use]
    pub const fn origin(&self) -> &Origin {
        &self.origin
    }
}

/// One executable scalar literal supplied by Ash rather than a header check.
#[derive(Debug)]
pub struct PreparedForeignConstant {
    name: String,
    representation: PreparedScalarRepresentation,
    value: PreparedScalarValue,
    origin: Origin,
}
impl PreparedForeignConstant {
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
    #[must_use]
    pub const fn representation(&self) -> PreparedScalarRepresentation {
        self.representation
    }
    #[must_use]
    pub const fn value(&self) -> PreparedScalarValue {
        self.value
    }
    #[must_use]
    pub const fn origin(&self) -> &Origin {
        &self.origin
    }
}

/// One complete source parameter; native projection never reinterprets a row.
#[derive(Debug)]
pub struct PreparedForeignParameter {
    name: String,
    kind: Kind,
    origin: Origin,
}
impl PreparedForeignParameter {
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
    #[must_use]
    pub const fn kind(&self) -> &Kind {
        &self.kind
    }
    #[must_use]
    pub const fn origin(&self) -> &Origin {
        &self.origin
    }
}

/// Scalar input selection, retaining source paths separately from ABI positions.
#[derive(Debug)]
pub enum PreparedOperandSource {
    Source(Vec<usize>),
    Constant(usize),
}

/// One ABI input in exact native order.
#[derive(Debug)]
pub struct PreparedForeignOperand {
    representation: PreparedScalarRepresentation,
    source: PreparedOperandSource,
    origin: Origin,
}
impl PreparedForeignOperand {
    #[must_use]
    pub const fn representation(&self) -> PreparedScalarRepresentation {
        self.representation
    }
    #[must_use]
    pub const fn source(&self) -> &PreparedOperandSource {
        &self.source
    }
    #[must_use]
    pub const fn origin(&self) -> &Origin {
        &self.origin
    }
}

/// The position-sensitive ABI result in the implemented scalar slice.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PreparedAbiResult {
    Void,
    Scalar(PreparedScalarRepresentation),
}

/// A raw native position, independent of an Ash source argument path.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PreparedNativePosition {
    Argument(usize),
    Result,
}

/// One checked scalar equality in a finite raw-outcome conjunction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PreparedOutcomePredicate {
    pub position: PreparedNativePosition,
    pub value: PreparedScalarValue,
}

/// A finite outcome rule. An empty predicate vector is the final otherwise rule.
#[derive(Debug)]
pub struct PreparedForeignOutcome {
    predicates: Vec<PreparedOutcomePredicate>,
    origin: Origin,
}
impl PreparedForeignOutcome {
    #[must_use]
    pub fn predicates(&self) -> &[PreparedOutcomePredicate] {
        &self.predicates
    }
    #[must_use]
    pub const fn origin(&self) -> &Origin {
        &self.origin
    }
}

/// Prepared ABI facts for one owner-free symbol, before resolved type checking.
#[derive(Debug)]
pub struct PreparedForeignSymbol {
    name: String,
    native_name: String,
    parameters: Vec<PreparedForeignParameter>,
    native_type_projection: Vec<usize>,
    operands: Vec<PreparedForeignOperand>,
    result: PreparedAbiResult,
    outcomes: Vec<PreparedForeignOutcome>,
    origin: Origin,
}
impl PreparedForeignSymbol {
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
    #[must_use]
    pub fn native_name(&self) -> &str {
        &self.native_name
    }
    #[must_use]
    pub fn parameters(&self) -> &[PreparedForeignParameter] {
        &self.parameters
    }
    #[must_use]
    pub fn native_type_projection(&self) -> &[usize] {
        &self.native_type_projection
    }
    #[must_use]
    pub fn operands(&self) -> &[PreparedForeignOperand] {
        &self.operands
    }
    #[must_use]
    pub const fn result(&self) -> PreparedAbiResult {
        self.result
    }
    #[must_use]
    pub fn outcomes(&self) -> &[PreparedForeignOutcome] {
        &self.outcomes
    }
    #[must_use]
    pub const fn origin(&self) -> &Origin {
        &self.origin
    }
}

/// Immutable source ABI preparation, not resolved foreign operation authority.
#[derive(Debug)]
pub struct PreparedForeignLibrary {
    module: ModuleId,
    name: String,
    public: bool,
    representations: Vec<PreparedForeignRepresentation>,
    constants: Vec<PreparedForeignConstant>,
    symbols: Vec<PreparedForeignSymbol>,
    origin: Origin,
}
impl PreparedForeignLibrary {
    #[must_use]
    pub const fn module(&self) -> ModuleId {
        self.module
    }
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
    #[must_use]
    pub const fn public(&self) -> bool {
        self.public
    }
    #[must_use]
    pub const fn profile(&self) -> &'static str {
        PROFILE
    }
    #[must_use]
    pub fn representations(&self) -> &[PreparedForeignRepresentation] {
        &self.representations
    }
    #[must_use]
    pub fn constants(&self) -> &[PreparedForeignConstant] {
        &self.constants
    }
    #[must_use]
    pub fn symbols(&self) -> &[PreparedForeignSymbol] {
        &self.symbols
    }
    #[must_use]
    pub const fn origin(&self) -> &Origin {
        &self.origin
    }
}

/// Prepares ABI structure without loading native code or resolving Ash identities.
///
/// # Errors
/// Rejects inconsistent scalar contracts, unsupported forms and exhausted work
/// or storage. Foreign behavioral assumptions are checked for consistency only.
pub fn prepare_foreign_library(
    module: ModuleId,
    source: &SurfaceForeignLibrary,
) -> Result<PreparedForeignLibrary, ForeignContractError> {
    prepare_foreign_library_with_budget(module, source, &mut TypeWorkBudget::default())
}

pub(crate) fn prepare_foreign_library_with_budget(
    module: ModuleId,
    source: &SurfaceForeignLibrary,
    work: &mut TypeWorkBudget,
) -> Result<PreparedForeignLibrary, ForeignContractError> {
    charge(work, source.members.len(), source.span)?;
    let mut profile = false;
    let mut representation_count = 0;
    let mut constant_count = 0;
    let mut symbol_count = 0;
    let mut names: Vec<&str> = Vec::new();
    reserve(&mut names, source.members.len(), source.span)?;
    for member in &source.members {
        let name = match member {
            SurfaceForeignMember::Profile(value) => {
                if profile {
                    return Err(failure(ForeignContractReason::DuplicateProfile, value.span));
                }
                if value.target.value != PROFILE {
                    return Err(failure(
                        ForeignContractReason::UnsupportedProfile,
                        value.target.span,
                    ));
                }
                profile = true;
                continue;
            }
            SurfaceForeignMember::Representation(value) => {
                representation_count += 1;
                &value.name
            }
            SurfaceForeignMember::Constant(value) => {
                constant_count += 1;
                &value.name
            }
            SurfaceForeignMember::Sentinel(value) => &value.name,
            SurfaceForeignMember::Owner(value) => &value.name,
            SurfaceForeignMember::Access(value) => &value.name,
            SurfaceForeignMember::Symbol(value) => {
                symbol_count += 1;
                &value.name
            }
        };
        for previous in &names {
            if names_equal(previous, &name.text, name.span, work)? {
                return Err(failure(ForeignContractReason::DuplicateMember, name.span));
            }
        }
        names.push(&name.text);
    }
    if !profile {
        return Err(failure(ForeignContractReason::MissingProfile, source.span));
    }
    let mut prepared = PreparedForeignLibrary {
        module,
        name: text(&source.name.text, source.name.span, work)?,
        public: source.public,
        representations: Vec::new(),
        constants: Vec::new(),
        symbols: Vec::new(),
        origin: Origin::Source(source.span),
    };
    reserve(
        &mut prepared.representations,
        representation_count,
        source.span,
    )?;
    reserve(&mut prepared.constants, constant_count, source.span)?;
    reserve(&mut prepared.symbols, symbol_count, source.span)?;
    for member in &source.members {
        charge(work, 1, source.span)?;
        match member {
            SurfaceForeignMember::Representation(value) => {
                let representation = match &value.representation {
                    SurfaceForeignRepresentation::Signed(width)
                    | SurfaceForeignRepresentation::Unsigned(width) => {
                        let width_value = position_integer(width, work)?;
                        if !matches!(width_value, 8 | 32 | 64) {
                            return Err(failure(
                                ForeignContractReason::UnsupportedRepresentation,
                                width.span,
                            ));
                        }
                        if matches!(
                            &value.representation,
                            SurfaceForeignRepresentation::Signed(_)
                        ) {
                            PreparedScalarRepresentation::Signed(width_value as u8)
                        } else {
                            PreparedScalarRepresentation::Unsigned(width_value as u8)
                        }
                    }
                    SurfaceForeignRepresentation::SizeT(_) => PreparedScalarRepresentation::SizeT,
                    _ => {
                        return Err(failure(
                            ForeignContractReason::UnimplementedContract,
                            value.span,
                        ));
                    }
                };
                prepared
                    .representations
                    .push(PreparedForeignRepresentation {
                        name: text(&value.name.text, value.name.span, work)?,
                        representation,
                        origin: Origin::Source(value.span),
                    });
            }
            SurfaceForeignMember::Sentinel(value) => {
                return Err(failure(
                    ForeignContractReason::UnimplementedContract,
                    value.span,
                ));
            }
            SurfaceForeignMember::Owner(value) => {
                return Err(failure(
                    ForeignContractReason::UnimplementedContract,
                    value.span,
                ));
            }
            SurfaceForeignMember::Access(value) => {
                return Err(failure(
                    ForeignContractReason::UnimplementedContract,
                    value.span,
                ));
            }
            _ => {}
        }
    }
    for member in &source.members {
        charge(work, 1, source.span)?;
        if let SurfaceForeignMember::Constant(value) = member {
            let representation = representation(&prepared, &value.representation, work)?;
            let scalar = scalar_value(&value.value, representation, work)?;
            prepared.constants.push(PreparedForeignConstant {
                name: text(&value.name.text, value.name.span, work)?,
                representation,
                value: scalar,
                origin: Origin::Source(value.span),
            });
        }
    }
    for member in &source.members {
        charge(work, 1, source.span)?;
        if let SurfaceForeignMember::Symbol(value) = member {
            let symbol = prepare_symbol(&prepared, value, work)?;
            prepared.symbols.push(symbol);
        }
    }
    Ok(prepared)
}

fn local_reference(reference: &SurfaceForeignReference) -> Result<&str, ForeignContractError> {
    if reference.module.is_some() {
        return Err(failure(
            ForeignContractReason::UnimplementedContract,
            reference.span,
        ));
    }
    Ok(&reference.name.text)
}
fn representation(
    library: &PreparedForeignLibrary,
    reference: &SurfaceForeignReference,
    work: &mut TypeWorkBudget,
) -> Result<PreparedScalarRepresentation, ForeignContractError> {
    let name = local_reference(reference)?;
    for value in &library.representations {
        if names_equal(&value.name, name, reference.span, work)? {
            return Ok(value.representation);
        }
    }
    Err(failure(
        ForeignContractReason::UnknownMember,
        reference.span,
    ))
}
fn constant<'a>(
    library: &'a PreparedForeignLibrary,
    reference: &SurfaceForeignReference,
    work: &mut TypeWorkBudget,
) -> Result<(usize, &'a PreparedForeignConstant), ForeignContractError> {
    let name = local_reference(reference)?;
    for (index, value) in library.constants.iter().enumerate() {
        if names_equal(&value.name, name, reference.span, work)? {
            return Ok((index, value));
        }
    }
    Err(failure(
        ForeignContractReason::UnknownMember,
        reference.span,
    ))
}
fn position_integer(
    value: &SurfaceForeignInteger,
    work: &mut TypeWorkBudget,
) -> Result<usize, ForeignContractError> {
    charge(
        work,
        usize::try_from(value.magnitude.magnitude_byte_length())
            .unwrap_or(usize::MAX)
            .saturating_add(1),
        value.span,
    )?;
    if value.negative {
        return Err(failure(ForeignContractReason::SourcePosition, value.span));
    }
    value
        .magnitude
        .to_usize()
        .ok_or_else(|| failure(ForeignContractReason::SourcePosition, value.span))
}
fn scalar_value(
    value: &SurfaceForeignInteger,
    representation: PreparedScalarRepresentation,
    work: &mut TypeWorkBudget,
) -> Result<PreparedScalarValue, ForeignContractError> {
    charge(
        work,
        usize::try_from(value.magnitude.magnitude_byte_length())
            .unwrap_or(usize::MAX)
            .saturating_add(1),
        value.span,
    )?;
    let magnitude = value
        .magnitude
        .to_u64()
        .ok_or_else(|| failure(ForeignContractReason::ConstantRange, value.span))?;
    let negative = value.negative && magnitude != 0;
    let admitted = match representation {
        PreparedScalarRepresentation::Signed(bits) => {
            let boundary = 1_u64 << (bits - 1);
            if negative {
                magnitude <= boundary
            } else {
                magnitude < boundary
            }
        }
        PreparedScalarRepresentation::Unsigned(bits) => {
            !negative && (bits == 64 || magnitude < (1_u64 << bits))
        }
        PreparedScalarRepresentation::SizeT => !negative,
    };
    if !admitted {
        return Err(failure(ForeignContractReason::ConstantRange, value.span));
    }
    Ok(PreparedScalarValue {
        negative,
        magnitude,
    })
}
fn abi_result(
    library: &PreparedForeignLibrary,
    value: &SurfaceForeignAbiRepresentation,
    work: &mut TypeWorkBudget,
) -> Result<PreparedAbiResult, ForeignContractError> {
    match value {
        SurfaceForeignAbiRepresentation::Void(_) => Ok(PreparedAbiResult::Void),
        SurfaceForeignAbiRepresentation::Member(reference) => {
            representation(library, reference, work).map(PreparedAbiResult::Scalar)
        }
        SurfaceForeignAbiRepresentation::Pointer { span, .. } => {
            Err(failure(ForeignContractReason::UnimplementedContract, *span))
        }
    }
}
fn native_position(
    position: &SurfaceForeignNativePosition,
    work: &mut TypeWorkBudget,
) -> Result<PreparedNativePosition, ForeignContractError> {
    match position {
        SurfaceForeignNativePosition::Result(_) => Ok(PreparedNativePosition::Result),
        SurfaceForeignNativePosition::Argument(value) => {
            position_integer(value, work).map(PreparedNativePosition::Argument)
        }
    }
}
fn source_path(
    position: &SurfaceForeignSourcePosition,
    domain: &SurfaceType,
    work: &mut TypeWorkBudget,
) -> Result<Vec<usize>, ForeignContractError> {
    let mut path = Vec::new();
    charge(work, position.components.len(), position.span)?;
    reserve(&mut path, position.components.len(), position.span)?;
    for component in &position.components {
        path.push(position_integer(component, work)?);
    }
    let Some((first, rest)) = path.split_first() else {
        return Err(failure(
            ForeignContractReason::SourcePosition,
            position.span,
        ));
    };
    let mut selected = match &domain.kind {
        SurfaceTypeKind::Tuple(fields) => fields.get(*first),
        _ if *first == 0 => Some(domain),
        _ => None,
    }
    .ok_or_else(|| failure(ForeignContractReason::SourcePosition, position.span))?;
    for component in rest {
        selected = match &selected.kind {
            SurfaceTypeKind::Tuple(fields) => fields.get(*component),
            _ => None,
        }
        .ok_or_else(|| failure(ForeignContractReason::SourcePosition, position.span))?;
    }
    if !matches!(selected.kind, SurfaceTypeKind::Int) {
        return Err(failure(
            ForeignContractReason::SourcePosition,
            position.span,
        ));
    }
    Ok(path)
}

fn prepare_symbol(
    library: &PreparedForeignLibrary,
    source: &SurfaceForeignSymbol,
    work: &mut TypeWorkBudget,
) -> Result<PreparedForeignSymbol, ForeignContractError> {
    let SurfaceTypeKind::Function(function) = &source.ty.kind else {
        return Err(failure(
            ForeignContractReason::SourceSignature,
            source.ty.span,
        ));
    };
    if function
        .effects
        .as_ref()
        .is_some_and(|row| !row.effects.is_empty() || row.tail.is_some())
    {
        return Err(failure(
            ForeignContractReason::SourceSignature,
            source.ty.span,
        ));
    }
    charge(
        work,
        source.native_name.value.len(),
        source.native_name.span,
    )?;
    if source.native_name.value.is_empty() || source.native_name.value.contains('\0') {
        return Err(failure(
            ForeignContractReason::InvalidNativeName,
            source.native_name.span,
        ));
    }
    let mut symbol = PreparedForeignSymbol {
        name: text(&source.name.text, source.name.span, work)?,
        native_name: text(&source.native_name.value, source.native_name.span, work)?,
        parameters: Vec::new(),
        native_type_projection: Vec::new(),
        operands: Vec::new(),
        result: abi_result(library, &source.abi_result, work)?,
        outcomes: Vec::new(),
        origin: Origin::Source(source.span),
    };
    charge(work, source.parameters.len(), source.span)?;
    reserve(&mut symbol.parameters, source.parameters.len(), source.span)?;
    let type_parameter_count = source
        .parameters
        .iter()
        .filter(|parameter| {
            !matches!(
                parameter.kind.as_ref().map(|kind| &kind.kind),
                Some(SurfaceKindKind::EffectRow)
            )
        })
        .count();
    reserve(
        &mut symbol.native_type_projection,
        type_parameter_count,
        source.span,
    )?;
    for parameter in &source.parameters {
        charge(work, 1, parameter.span)?;
        for previous in &symbol.parameters {
            if names_equal(&previous.name, &parameter.name.text, parameter.span, work)? {
                return Err(failure(
                    ForeignContractReason::InvalidParameters,
                    parameter.span,
                ));
            }
        }
        let kind = match parameter.kind.as_ref().map(|kind| &kind.kind) {
            None | Some(SurfaceKindKind::Type) => Kind::Type,
            Some(SurfaceKindKind::EffectRow) => Kind::EffectRow,
            Some(SurfaceKindKind::Function { .. }) => {
                return Err(failure(
                    ForeignContractReason::UnimplementedContract,
                    parameter.span,
                ));
            }
        };
        if kind == Kind::Type {
            symbol.native_type_projection.push(symbol.parameters.len());
        }
        symbol.parameters.push(PreparedForeignParameter {
            name: text(&parameter.name.text, parameter.name.span, work)?,
            kind,
            origin: Origin::Source(parameter.span),
        });
    }
    charge(work, source.abi_operands.len(), source.span)?;
    reserve(&mut symbol.operands, source.abi_operands.len(), source.span)?;
    // This temporary index borrows authored mappings. Each native position is
    // narrowed once; source paths are projected once when its ABI slot is built.
    let mut mappings = Vec::new();
    reserve(&mut mappings, source.abi_operands.len(), source.span)?;
    mappings.resize_with(source.abi_operands.len(), || None);
    let mut outcome_count = 0;
    for contract in &source.contracts {
        charge(work, 1, source.span)?;
        match contract {
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
            SurfaceForeignContract::Outcome { .. } => outcome_count += 1,
            _ => {}
        }
    }
    for (index, operand) in source.abi_operands.iter().enumerate() {
        charge(work, 1, operand.span)?;
        if operand.output {
            return Err(failure(
                ForeignContractReason::UnimplementedContract,
                operand.span,
            ));
        }
        let PreparedAbiResult::Scalar(representation) =
            abi_result(library, &operand.representation, work)?
        else {
            return Err(failure(ForeignContractReason::VoidPosition, operand.span));
        };
        let input = mappings[index]
            .ok_or_else(|| failure(ForeignContractReason::OperandCoverage, operand.span))?;
        let mapping = match input {
            SurfaceForeignOperandSource::Source { position, role } => {
                if !matches!(role.kind, SurfaceForeignOperandRoleKind::Scalar) {
                    return Err(failure(
                        ForeignContractReason::UnimplementedContract,
                        role.span,
                    ));
                }
                PreparedOperandSource::Source(source_path(position, &function.domain, work)?)
            }
            SurfaceForeignOperandSource::Constant(reference) => {
                let (index, value) = constant(library, reference, work)?;
                if value.representation != representation {
                    return Err(failure(ForeignContractReason::OperandRole, reference.span));
                }
                PreparedOperandSource::Constant(index)
            }
            SurfaceForeignOperandSource::Null(span) => {
                return Err(failure(ForeignContractReason::OperandRole, *span));
            }
        };
        symbol.operands.push(PreparedForeignOperand {
            representation,
            source: mapping,
            origin: Origin::Source(operand.span),
        });
    }
    drop(mappings);
    let mut output = false;
    let mut otherwise = false;
    reserve(&mut symbol.outcomes, outcome_count, source.span)?;
    for contract in &source.contracts {
        charge(work, 1, source.span)?;
        match contract {
            SurfaceForeignContract::Operand { .. } => {}
            SurfaceForeignContract::Output {
                position,
                role,
                span,
            } => {
                if output
                    || symbol.result == PreparedAbiResult::Void
                    || native_position(position, work)? != PreparedNativePosition::Result
                {
                    return Err(failure(ForeignContractReason::OutputCoverage, *span));
                }
                if !matches!(role.kind, SurfaceForeignOutputRoleKind::Scalar) {
                    return Err(failure(
                        ForeignContractReason::UnimplementedContract,
                        role.span,
                    ));
                }
                output = true;
            }
            SurfaceForeignContract::RetainedDependentsBlock { span } => {
                return Err(failure(ForeignContractReason::UnimplementedContract, *span));
            }
            SurfaceForeignContract::Outcome { test, facts, span } => {
                if otherwise {
                    return Err(failure(ForeignContractReason::OutcomeCoverage, *span));
                }
                let mut predicates = Vec::new();
                match test {
                    SurfaceForeignOutcomeTest::Otherwise(_) => otherwise = true,
                    SurfaceForeignOutcomeTest::All(atoms) => {
                        if atoms.is_empty() {
                            return Err(failure(ForeignContractReason::OutcomeCoverage, *span));
                        }
                        charge(work, atoms.len(), *span)?;
                        reserve(&mut predicates, atoms.len(), *span)?;
                        for atom in atoms {
                            let position = native_position(&atom.position, work)?;
                            // Predicates may inspect raw results and output slots, not inputs.
                            let PreparedAbiResult::Scalar(representation) = symbol.result else {
                                return Err(failure(
                                    ForeignContractReason::OutcomeCoverage,
                                    atom.span,
                                ));
                            };
                            if position != PreparedNativePosition::Result {
                                return Err(failure(
                                    ForeignContractReason::OutcomeCoverage,
                                    atom.span,
                                ));
                            }
                            let SurfaceForeignOutcomeCondition::Equal(reference) = &atom.condition
                            else {
                                return Err(failure(
                                    ForeignContractReason::UnimplementedContract,
                                    atom.span,
                                ));
                            };
                            let (_, value) = constant(library, reference, work)?;
                            if value.representation != representation {
                                return Err(failure(
                                    ForeignContractReason::OperandRole,
                                    reference.span,
                                ));
                            }
                            charge(work, predicates.len(), atom.span)?;
                            if predicates
                                .iter()
                                .any(|previous: &PreparedOutcomePredicate| {
                                    previous.position == position
                                })
                            {
                                return Err(failure(
                                    ForeignContractReason::OverlappingOutcomes,
                                    atom.span,
                                ));
                            }
                            predicates.push(PreparedOutcomePredicate {
                                position,
                                value: value.value,
                            });
                        }
                        for previous in &symbol.outcomes {
                            charge(
                                work,
                                previous.predicates.len().saturating_mul(predicates.len()),
                                *span,
                            )?;
                            let disjoint = previous.predicates.iter().any(|left| {
                                predicates.iter().any(|right| {
                                    left.position == right.position && left.value != right.value
                                })
                            });
                            if !disjoint {
                                return Err(failure(
                                    ForeignContractReason::OverlappingOutcomes,
                                    *span,
                                ));
                            }
                        }
                    }
                }
                let mut readable = false;
                for fact in facts {
                    charge(work, 1, fact.span)?;
                    match &fact.kind {
                        SurfaceForeignOutcomeFactKind::Readable(position) => {
                            if readable
                                || symbol.result == PreparedAbiResult::Void
                                || native_position(position, work)?
                                    != PreparedNativePosition::Result
                            {
                                return Err(failure(ForeignContractReason::Readability, fact.span));
                            }
                            readable = true;
                        }
                        SurfaceForeignOutcomeFactKind::Unreadable(_) => {
                            return Err(failure(ForeignContractReason::Readability, fact.span));
                        }
                        _ => {
                            return Err(failure(
                                ForeignContractReason::UnimplementedContract,
                                fact.span,
                            ));
                        }
                    }
                }
                if readable != matches!(symbol.result, PreparedAbiResult::Scalar(_)) {
                    return Err(failure(ForeignContractReason::Readability, *span));
                }
                symbol.outcomes.push(PreparedForeignOutcome {
                    predicates,
                    origin: Origin::Source(*span),
                });
            }
        }
    }
    if output != matches!(symbol.result, PreparedAbiResult::Scalar(_)) {
        return Err(failure(ForeignContractReason::OutputCoverage, source.span));
    }
    if !otherwise {
        return Err(failure(ForeignContractReason::OutcomeCoverage, source.span));
    }
    Ok(symbol)
}

#[cfg(test)]
mod tests {
    use super::*;

    const SCALAR: &str = "foreign library C {\nprofile \"x86_64-unknown-linux-gnu\"\nrepr I32 = signed(32)\nconst Ok : I32 = 0\nsymbol Abs<T, Delta : EffectRow> : Int -> Foreign.Call<Int> {\nname \"abs\"\nabi (I32) -> I32\noperand 0 from 0 scalar\noutput result as scalar\noutcome result == Ok { readable result }\noutcome otherwise { readable result }\n}\n}\n";

    fn source_module(text: &str) -> (ModuleId, SurfaceModule) {
        let source = crate::source::SourceFile::new("bounded-foreign.ash", text).unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        let module = crate::parser::project_module(&source, &tree).unwrap();
        (ModuleId::from(source.id()), module)
    }

    fn measured(text: &str) -> usize {
        let (id, module) = source_module(text);
        let mut work = TypeWorkBudget::default();
        prepare_foreign_library_with_budget(id, &module.foreign_libraries[0], &mut work).unwrap();
        work.used()
    }

    #[test]
    fn exact_preparation_budget_one_short_partial_refusal_and_fresh_retry() {
        let prefix = format!("Q{}", "x".repeat(256));
        let long_names = SCALAR
            .replace("repr I32 = signed(32)", &format!("repr {prefix}0 = signed(32)\nrepr {prefix}1 = signed(32)\nrepr {prefix}2 = signed(32)"))
            .replace("I32", &format!("{prefix}2"))
            .replace("Ok", &format!("{prefix}3"))
            .replace("Abs<T, Delta", &format!("{prefix}4<{prefix}5, {prefix}6"));
        for text in [SCALAR, long_names.as_str()] {
            let (id, module) = source_module(text);
            let source = &module.foreign_libraries[0];
            let mut measured = TypeWorkBudget::default();
            let baseline = prepare_foreign_library_with_budget(id, source, &mut measured).unwrap();
            let exact = measured.used();
            assert!(
                prepare_foreign_library_with_budget(
                    id,
                    source,
                    &mut TypeWorkBudget::with_limit(exact)
                )
                .is_ok()
            );
            for limit in [0, exact / 2, exact - 1] {
                let refused = prepare_foreign_library_with_budget(
                    id,
                    source,
                    &mut TypeWorkBudget::with_limit(limit),
                )
                .unwrap_err();
                assert_eq!(refused.reason(), ForeignContractReason::WorkExhausted);
            }
            let mut retry_work = TypeWorkBudget::with_limit(exact);
            let retry = prepare_foreign_library_with_budget(id, source, &mut retry_work).unwrap();
            assert_eq!(retry_work.used(), exact);
            assert_eq!(
                retry.symbols()[0].native_name(),
                baseline.symbols()[0].native_name()
            );
            assert_eq!(
                retry.symbols()[0].native_type_projection(),
                baseline.symbols()[0].native_type_projection()
            );
        }
    }

    #[test]
    fn long_shared_names_and_late_nul_refuse_before_their_byte_scans() {
        let prefix = format!("Q{}", "x".repeat(512));
        let text = format!(
            "foreign library C {{\nprofile \"x86_64-unknown-linux-gnu\"\nrepr {prefix}0 = signed(32)\nrepr {prefix}1 = signed(32)\n}}\n"
        );
        let (id, module) = source_module(&text);
        let library = &module.foreign_libraries[0];
        let error = prepare_foreign_library_with_budget(
            id,
            library,
            &mut TypeWorkBudget::with_limit(library.members.len() + prefix.len()),
        )
        .unwrap_err();
        assert_eq!(error.reason(), ForeignContractReason::WorkExhausted);
        let SurfaceForeignMember::Representation(second) = &library.members[2] else {
            panic!("expected second representation");
        };
        assert_eq!(error.span(), second.name.span);

        let spelling = format!("{}\\0", "n".repeat(1024));
        let (id, module) =
            source_module(&SCALAR.replace("name \"abs\"", &format!("name \"{spelling}\"")));
        let library = &module.foreign_libraries[0];
        let SurfaceForeignMember::Symbol(symbol) = &library.members[3] else {
            panic!("expected symbol");
        };
        let error = prepare_foreign_library_with_budget(
            id,
            library,
            &mut TypeWorkBudget::with_limit(symbol.native_name.value.len() - 1),
        )
        .unwrap_err();
        assert_eq!(error.reason(), ForeignContractReason::WorkExhausted);
        assert_eq!(error.span(), symbol.native_name.span);
        assert_eq!(
            prepare_foreign_library(id, library).unwrap_err().reason(),
            ForeignContractReason::InvalidNativeName
        );
    }

    #[test]
    fn wide_scalar_mapping_work_grows_with_slots_and_contracts() {
        let wide = |width: usize| {
            let abi = vec!["I32"; width].join(", ");
            let operands = (0..width)
                .rev()
                .map(|position| format!("operand {position} from 0 scalar\n"))
                .collect::<String>();
            format!(
                "foreign library C {{\nprofile \"x86_64-unknown-linux-gnu\"\nrepr I32 = signed(32)\nsymbol Wide : Int -> Foreign.Call<Int> {{\nname \"wide\"\nabi ({abi}) -> I32\n{operands}output result as scalar\noutcome otherwise {{ readable result }}\n}}\n}}\n"
            )
        };
        let small = measured(&wide(32));
        let large = measured(&wide(64));
        assert!(large > small);
        assert!(large <= 2 * small, "small={small}, large={large}");
    }

    #[test]
    fn exhausted_preparation_cannot_publish_a_partial_library() {
        let source = crate::source::SourceFile::new(
            "bounded-foreign.ash",
            "foreign library C {\nprofile \"x86_64-unknown-linux-gnu\"\n}\n",
        )
        .unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        let module = crate::parser::project_module(&source, &tree).unwrap();
        let result = prepare_foreign_library_with_budget(
            ModuleId::from(source.id()),
            &module.foreign_libraries[0],
            &mut TypeWorkBudget::with_limit(0),
        );
        assert_eq!(
            result.unwrap_err().reason(),
            ForeignContractReason::WorkExhausted
        );
    }
}
