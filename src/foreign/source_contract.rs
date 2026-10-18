//! ABI preparation for source-authored foreign libraries.
//!
//! Prepared facts have no resolved operation or constructor authority. Ordinary
//! module checking must bind them to their defining identities and source types.
//! This preparation slice admits scalar calls and dependency-free owned byte/opaque
//! address contracts. Other forms reject explicitly. Resolved owner namespaces,
//! resource checking and runtime ownership remain separate admission phases.
//! Higher-kinded symbol parameters await the resolved binding phase; ordinary
//! Ash higher-kinded types are unaffected by this preparation subset.

use std::{error::Error, fmt};

use crate::{
    module::ModuleId,
    source::{Origin, Span},
    surface::{
        SurfaceForeignAbiRepresentation, SurfaceForeignContract, SurfaceForeignInteger,
        SurfaceForeignLibrary, SurfaceForeignMember, SurfaceForeignNativePosition,
        SurfaceForeignOperandRoleKind, SurfaceForeignOperandSource, SurfaceForeignOutcomeCondition,
        SurfaceForeignOutcomeFact, SurfaceForeignOutcomeFactKind, SurfaceForeignOutcomeTest,
        SurfaceForeignOutputRoleKind, SurfaceForeignOwner, SurfaceForeignReference,
        SurfaceForeignRepresentation, SurfaceForeignSourcePosition, SurfaceForeignSymbol,
        SurfaceKindKind, SurfaceType, SurfaceTypeKind, SurfaceTypeParameter,
    },
    types::{Kind, TypeWorkBudget},
};

#[path = "source_access_contract.rs"]
pub(crate) mod access_contract;
#[path = "source_access_image.rs"]
mod access_image;
#[path = "source_output_contract.rs"]
mod output_contract;
pub use access_contract::{
    PreparedAccessApplication, PreparedAccessResult, PreparedForeignAccess, PreparedForeignExtent,
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
                "foreign contract form is not implemented by this preparation slice"
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

/// Address ABI families never become ordinary Ash pointer values.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PreparedAddressRepresentation {
    Opaque,
    Bytes,
}

/// Position-independent representation facts, before resolved owner binding.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PreparedRepresentation {
    Scalar(PreparedScalarRepresentation),
    Address(PreparedAddressRepresentation),
    /// Function-address bits in a non-callable, fixed-operand role only.
    FunctionAddressSentinel,
}

/// A source-authored scalar value retained without mathematical narrowing.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PreparedScalarValue {
    pub negative: bool,
    pub magnitude: u64,
}

impl PreparedScalarValue {
    /// Exact mathematical value of an admitted scalar literal. This does not
    /// supply a representation, original member or execution permission.
    pub(crate) fn checked_integer(self) -> Option<crate::integer::Integer> {
        if self.negative {
            let value = if self.magnitude == 1_u64 << 63 {
                i64::MIN
            } else {
                -i64::try_from(self.magnitude).ok()?
            };
            Some(crate::integer::Integer::from_i64(value))
        } else {
            Some(crate::integer::Integer::from_u64(self.magnitude))
        }
    }
}

/// One unresolved representation declaration after profile checking.
#[derive(Debug)]
pub struct PreparedForeignRepresentation {
    member_index: usize,
    name: String,
    representation: PreparedRepresentation,
    origin: Origin,
}
impl PreparedForeignRepresentation {
    /// Zero-based coordinate in the original library member list.
    #[must_use]
    pub const fn member_index(&self) -> usize {
        self.member_index
    }
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
    #[must_use]
    pub const fn representation(&self) -> PreparedRepresentation {
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
    member_index: usize,
    name: String,
    representation: PreparedScalarRepresentation,
    value: PreparedScalarValue,
    origin: Origin,
}
impl PreparedForeignConstant {
    /// Zero-based coordinate in the original library member list.
    #[must_use]
    pub const fn member_index(&self) -> usize {
        self.member_index
    }
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

/// A checked all-bits-one literal. It is neither an ordinary value nor callable.
#[derive(Debug)]
pub struct PreparedForeignSentinel {
    member_index: usize,
    name: String,
    representation_index: usize,
    origin: Origin,
}
impl PreparedForeignSentinel {
    #[must_use]
    pub const fn member_index(&self) -> usize {
        self.member_index
    }
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }
    /// Exact declaration coordinate in the original representation table.
    #[must_use]
    pub const fn representation_index(&self) -> usize {
        self.representation_index
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
    /// Untrusted normalized image data, authenticated with its whole library
    /// and original nominal/symbol binding before any checked use.
    pub(crate) fn from_private_image(parts: PrivatePreparedParameterParts) -> Self {
        Self {
            name: parts.name,
            kind: match parts.kind {
                PrivatePreparedParameterKind::Type => Kind::Type,
                PrivatePreparedParameterKind::EffectRow => Kind::EffectRow,
            },
            origin: Origin::Source(parts.span),
        }
    }
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

/// Input selection, retaining scalar/current source paths separately from ABI positions.
#[derive(Debug)]
pub enum PreparedOperandSource {
    Source(Vec<usize>),
    Constant(usize),
    Sentinel(usize),
    Current(Vec<usize>),
    Enclosing(Vec<usize>),
    /// Stable copied String input, borrowed only until this native call returns.
    Nul(Vec<usize>),
    /// Independent temporary input with an explicit source byte extent. Both
    /// disciplines forbid retaining its address after the call; `copy` also
    /// records the authored independent-native-copy promise.
    Bytes {
        path: Vec<usize>,
        extent: Vec<usize>,
        copy: bool,
    },
    /// An explicitly authored optional null address, not an owner or sentinel.
    Null,
    /// A zero-initialized private owner-output slot at this ABI position.
    OwnerOutput,
    /// A separate initialized pointer slot read only by its exact offset rule.
    OffsetOutput,
}

/// One ABI input in exact native order.
#[derive(Debug)]
pub struct PreparedForeignOperand {
    representation: PreparedRepresentation,
    source: PreparedOperandSource,
    origin: Origin,
}
impl PreparedForeignOperand {
    #[must_use]
    pub const fn representation(&self) -> PreparedRepresentation {
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

/// The position-sensitive ABI result; Address denotes exactly one pointer level.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PreparedAbiResult {
    Void,
    Scalar(PreparedScalarRepresentation),
    Address(PreparedAddressRepresentation),
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

/// A source parameter selected with its original kind tag.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PreparedOwnerArgument {
    Type(usize),
    EffectRow(usize),
}
impl PreparedOwnerArgument {
    pub(crate) const fn parameter(self) -> usize {
        match self {
            Self::Type(index) | Self::EffectRow(index) => index,
        }
    }
}

/// An authored initialization promise with its checked integer source path.
#[derive(Debug)]
pub struct PreparedInitializedBytes {
    pub(crate) extent: Vec<usize>,
    pub(crate) span: Span,
}
impl PreparedInitializedBytes {
    #[must_use]
    pub fn extent(&self) -> &[usize] {
        &self.extent
    }
    #[must_use]
    pub const fn span(&self) -> Span {
        self.span
    }
}

/// A local owner application retaining every Type and EffectRow argument.
#[derive(Debug)]
pub struct PreparedOwnerApplication {
    pub(crate) owner: usize,
    pub(crate) arguments: Vec<PreparedOwnerArgument>,
    pub(crate) span: Span,
}
impl PreparedOwnerApplication {
    pub const fn owner(&self) -> usize {
        self.owner
    }
    pub fn arguments(&self) -> &[PreparedOwnerArgument] {
        &self.arguments
    }
    pub const fn span(&self) -> Span {
        self.span
    }
}

/// One total raw-status branch, retained with its source disposition/readability.
#[derive(Debug)]
pub struct PreparedOwnerStatusOutcome {
    pub(crate) predicates: Vec<PreparedOutcomePredicate>,
    pub(crate) consumes: bool,
    pub(crate) readable: bool,
    pub(crate) disposition_span: Span,
    pub(crate) readability_span: Span,
    pub(crate) outcome_span: Span,
}

/// An initialized pointer output extracted relative to one exact prepared NUL
/// input. The first scalar-equality outcome reads it; otherwise leaves it unread.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PreparedOffsetOutput {
    pub(crate) operand: usize,
    pub(crate) input_operand: usize,
    pub(crate) output_span: Span,
    pub(crate) status: PreparedScalarValue,
    pub(crate) condition_span: Span,
    pub(crate) readable_span: Span,
    pub(crate) otherwise_span: Span,
    pub(crate) otherwise_readable_spans: [Span; 3],
}

/// Complete facts for the admitted owner-producing or finishing call shape.
#[derive(Debug)]
pub enum PreparedOwnerCall {
    /// A guarded nonconsuming scalar call. No source owner is created or finished.
    Borrow {
        application: PreparedOwnerApplication,
        current_operand: usize,
        output_span: Span,
        outcome_span: Span,
        readable_span: Span,
    },
    Acquire {
        application: PreparedOwnerApplication,
        first_nonnull: bool,
        condition_span: Span,
        outcome_spans: [Span; 2],
        readable_spans: [Span; 2],
        initialized_bytes: Option<PreparedInitializedBytes>,
    },
    /// A readable scalar result followed by the nullable opaque owner and any
    /// offset output in ABI order. Private slots start null before entry.
    OutputAcquire {
        application: PreparedOwnerApplication,
        output_operand: usize,
        output_span: Span,
        scalar_output_span: Span,
        outcome_span: Span,
        readable_spans: [Span; 2],
        offset: Option<PreparedOffsetOutput>,
    },
    Teardown {
        application: PreparedOwnerApplication,
        current_operand: usize,
        consumes: bool,
        disposition_span: Span,
        block_span: Span,
        outcome_span: Span,
    },
    StatusTeardown {
        application: PreparedOwnerApplication,
        current_operand: usize,
        output_span: Span,
        block_span: Span,
        outcomes: Vec<PreparedOwnerStatusOutcome>,
    },
}

impl PreparedOwnerCall {
    /// Scalar status occupies field zero; the original output ABI coordinates
    /// determine the owner and optional offset fields that follow it.
    pub(crate) fn output_field_positions(&self) -> Option<(usize, Option<usize>)> {
        let Self::OutputAcquire {
            output_operand,
            offset,
            ..
        } = self
        else {
            return None;
        };
        let offset_first = offset.is_some_and(|offset| offset.operand < *output_operand);
        Some((
            1 + usize::from(offset_first),
            offset.map(|_| if offset_first { 1 } else { 2 }),
        ))
    }

    pub(crate) fn application(&self) -> &PreparedOwnerApplication {
        match self {
            Self::Acquire { application, .. }
            | Self::Borrow { application, .. }
            | Self::OutputAcquire { application, .. }
            | Self::Teardown { application, .. }
            | Self::StatusTeardown { application, .. } => application,
        }
    }
    pub(crate) fn current_operand(&self) -> Option<usize> {
        match self {
            Self::Acquire { .. } | Self::OutputAcquire { .. } => None,
            Self::Teardown {
                current_operand, ..
            }
            | Self::StatusTeardown {
                current_operand, ..
            }
            | Self::Borrow {
                current_operand, ..
            } => Some(*current_operand),
        }
    }
    pub(crate) fn dispositions(&self) -> impl Iterator<Item = (bool, bool)> + '_ {
        let void = match self {
            Self::Teardown { consumes, .. } => Some((*consumes, true)),
            _ => None,
        };
        let status = match self {
            Self::StatusTeardown { outcomes, .. } => outcomes.as_slice(),
            _ => &[],
        };
        void.into_iter().chain(
            status
                .iter()
                .map(|outcome| (outcome.consumes, outcome.readable)),
        )
    }
}

/// One dependency-free owner family. Teardown uses the original member
/// coordinate, without a back-reference into the owning library.
#[derive(Debug)]
pub struct PreparedForeignOwner {
    member_index: usize,
    name: String,
    parameters: Vec<PreparedForeignParameter>,
    owned_parameter: usize,
    retains: Vec<usize>,
    representation: PreparedAddressRepresentation,
    teardown_member: usize,
    representation_span: Span,
    owned_span: Span,
    teardown_span: Span,
    origin: Origin,
}
impl PreparedForeignOwner {
    /// Zero-based coordinate in the original library member list.
    #[must_use]
    pub const fn member_index(&self) -> usize {
        self.member_index
    }
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn parameters(&self) -> &[PreparedForeignParameter] {
        &self.parameters
    }
    pub const fn owned_parameter(&self) -> usize {
        self.owned_parameter
    }
    pub fn retained_parameters(&self) -> &[usize] {
        &self.retains
    }
    pub const fn representation(&self) -> PreparedAddressRepresentation {
        self.representation
    }
    #[must_use]
    pub const fn representation_span(&self) -> Span {
        self.representation_span
    }
    #[must_use]
    pub const fn owned_span(&self) -> Span {
        self.owned_span
    }
    #[must_use]
    pub const fn teardown_span(&self) -> Span {
        self.teardown_span
    }
    pub const fn teardown_member(&self) -> usize {
        self.teardown_member
    }
    pub const fn origin(&self) -> &Origin {
        &self.origin
    }
}

/// Mutually exclusive normalized scalar or owner call contracts.
#[derive(Debug)]
#[expect(
    clippy::large_enum_variant,
    reason = "keep normalized owner plans inline without an additional infallible allocation"
)]
pub enum PreparedForeignCall {
    Scalar {
        outcomes: Vec<PreparedForeignOutcome>,
    },
    Owner(PreparedOwnerCall),
}

impl PreparedForeignCall {
    fn outcomes(&self) -> &[PreparedForeignOutcome] {
        match self {
            Self::Scalar { outcomes } => outcomes,
            Self::Owner(_) => &[],
        }
    }
}

/// An immutable producer input mapped to the original destructor's ABI slot.
#[derive(Debug)]
pub struct PreparedDestructionOperand {
    position: usize,
    source: Vec<usize>,
    origin: Origin,
}

impl PreparedDestructionOperand {
    #[must_use]
    pub const fn position(&self) -> usize {
        self.position
    }
    #[must_use]
    pub fn source(&self) -> &[usize] {
        &self.source
    }
    #[must_use]
    pub const fn origin(&self) -> &Origin {
        &self.origin
    }
}

/// Prepared ABI facts for one symbol, before resolved type checking.
#[derive(Debug)]
pub struct PreparedForeignSymbol {
    member_index: usize,
    name: String,
    native_name: String,
    parameters: Vec<PreparedForeignParameter>,
    native_type_projection: Vec<usize>,
    operands: Vec<PreparedForeignOperand>,
    destruction_operands: Vec<PreparedDestructionOperand>,
    result: PreparedAbiResult,
    call: PreparedForeignCall,
    access_result: Option<PreparedAccessResult>,
    origin: Origin,
}
impl PreparedForeignSymbol {
    /// Zero-based coordinate in the original library member list.
    #[must_use]
    pub const fn member_index(&self) -> usize {
        self.member_index
    }
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
    pub fn destruction_operands(&self) -> &[PreparedDestructionOperand] {
        &self.destruction_operands
    }
    #[must_use]
    pub const fn result(&self) -> PreparedAbiResult {
        self.result
    }
    #[must_use]
    pub const fn owner_call(&self) -> Option<&PreparedOwnerCall> {
        match &self.call {
            PreparedForeignCall::Owner(call) => Some(call),
            _ => None,
        }
    }
    #[must_use]
    pub const fn call(&self) -> &PreparedForeignCall {
        &self.call
    }
    #[must_use]
    pub const fn access_result(&self) -> Option<&PreparedAccessResult> {
        self.access_result.as_ref()
    }
    #[must_use]
    pub fn outcomes(&self) -> &[PreparedForeignOutcome] {
        self.call.outcomes()
    }
    #[must_use]
    pub const fn origin(&self) -> &Origin {
        &self.origin
    }
}

/// Constructor-free source declarations remain distinct passive categories.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum PreparedForeignNominalRole {
    Owner(usize),
    Access(usize),
}
impl PreparedForeignNominalRole {
    pub(crate) fn declaration(
        self,
        library: &PreparedForeignLibrary,
    ) -> Option<(&str, &[PreparedForeignParameter], &Origin)> {
        match self {
            Self::Owner(index) => library
                .owners()
                .get(index)
                .map(|value| (value.name(), value.parameters(), value.origin())),
            Self::Access(index) => library
                .accesses()
                .get(index)
                .map(|value| (value.name(), value.parameters(), value.origin())),
        }
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
    sentinels: Vec<PreparedForeignSentinel>,
    owners: Vec<PreparedForeignOwner>,
    accesses: Vec<PreparedForeignAccess>,
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
    pub fn sentinels(&self) -> &[PreparedForeignSentinel] {
        &self.sentinels
    }
    #[must_use]
    pub fn owners(&self) -> &[PreparedForeignOwner] {
        &self.owners
    }
    #[must_use]
    pub fn accesses(&self) -> &[PreparedForeignAccess] {
        &self.accesses
    }
    pub(crate) fn access_result_owner(
        &self,
        application: &PreparedAccessApplication,
        work: &mut TypeWorkBudget,
    ) -> Result<(usize, Vec<PreparedOwnerArgument>), ForeignContractError> {
        access_contract::access_owner(self, application, work)
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
/// Rejects inconsistent admitted contracts, unsupported forms and exhausted work
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
    let mut sentinel_count = 0;
    let mut symbol_count = 0;
    let mut owner_count = 0;
    let mut access_count = 0;
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
            SurfaceForeignMember::Sentinel(value) => {
                sentinel_count += 1;
                &value.name
            }
            SurfaceForeignMember::Owner(value) => {
                owner_count += 1;
                &value.name
            }
            SurfaceForeignMember::Access(value) => {
                access_count += 1;
                &value.name
            }
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
        sentinels: Vec::new(),
        owners: Vec::new(),
        accesses: Vec::new(),
        symbols: Vec::new(),
        origin: Origin::Source(source.span),
    };
    reserve(
        &mut prepared.representations,
        representation_count,
        source.span,
    )?;
    reserve(&mut prepared.constants, constant_count, source.span)?;
    reserve(&mut prepared.sentinels, sentinel_count, source.span)?;
    reserve(&mut prepared.symbols, symbol_count, source.span)?;
    reserve(&mut prepared.owners, owner_count, source.span)?;
    reserve(&mut prepared.accesses, access_count, source.span)?;
    for (member_index, member) in source.members.iter().enumerate() {
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
                        PreparedRepresentation::Scalar(
                            if matches!(
                                &value.representation,
                                SurfaceForeignRepresentation::Signed(_)
                            ) {
                                PreparedScalarRepresentation::Signed(width_value as u8)
                            } else {
                                PreparedScalarRepresentation::Unsigned(width_value as u8)
                            },
                        )
                    }
                    SurfaceForeignRepresentation::SizeT(_) => {
                        PreparedRepresentation::Scalar(PreparedScalarRepresentation::SizeT)
                    }
                    SurfaceForeignRepresentation::Opaque(_) => {
                        PreparedRepresentation::Address(PreparedAddressRepresentation::Opaque)
                    }
                    SurfaceForeignRepresentation::Bytes(_) => {
                        PreparedRepresentation::Address(PreparedAddressRepresentation::Bytes)
                    }
                    SurfaceForeignRepresentation::FunctionAddress(_) => {
                        PreparedRepresentation::FunctionAddressSentinel
                    }
                };
                prepared
                    .representations
                    .push(PreparedForeignRepresentation {
                        member_index,
                        name: text(&value.name.text, value.name.span, work)?,
                        representation,
                        origin: Origin::Source(value.span),
                    });
            }
            SurfaceForeignMember::Sentinel(_) => {}
            SurfaceForeignMember::Owner(_) => {}
            SurfaceForeignMember::Access(_) => {}
            _ => {}
        }
    }
    for (member_index, member) in source.members.iter().enumerate() {
        charge(work, 1, source.span)?;
        if let SurfaceForeignMember::Sentinel(value) = member {
            let name = local_reference(&value.representation)?;
            let mut selected = None;
            for (index, declaration) in prepared.representations.iter().enumerate() {
                if names_equal(declaration.name(), name, value.representation.span, work)? {
                    if declaration.representation()
                        != PreparedRepresentation::FunctionAddressSentinel
                    {
                        return Err(failure(ForeignContractReason::OperandRole, value.span));
                    }
                    selected = Some(index);
                    break;
                }
            }
            let representation_index = selected
                .ok_or_else(|| failure(ForeignContractReason::UnknownMember, value.span))?;
            prepared.sentinels.push(PreparedForeignSentinel {
                member_index,
                name: text(&value.name.text, value.name.span, work)?,
                representation_index,
                origin: Origin::Source(value.span),
            });
        }
        if let SurfaceForeignMember::Constant(value) = member {
            let PreparedRepresentation::Scalar(representation) =
                representation(&prepared, &value.representation, work)?
            else {
                return Err(failure(ForeignContractReason::ConstantRange, value.span));
            };
            let scalar = scalar_value(&value.value, representation, work)?;
            prepared.constants.push(PreparedForeignConstant {
                member_index,
                name: text(&value.name.text, value.name.span, work)?,
                representation,
                value: scalar,
                origin: Origin::Source(value.span),
            });
        }
    }
    if owner_count != 0 {
        for (member_index, member) in source.members.iter().enumerate() {
            charge(work, 1, source.span)?;
            if let SurfaceForeignMember::Owner(owner) = member {
                let value = prepare_owner(&prepared, source, member_index, owner, work)?;
                prepared.owners.push(value);
            }
        }
    }
    for (member_index, member) in source.members.iter().enumerate() {
        charge(work, 1, source.span)?;
        if let SurfaceForeignMember::Access(value) = member {
            let access = access_contract::prepare(&prepared, source, member_index, value, work)?;
            prepared.accesses.push(access);
        }
    }
    for (member_index, member) in source.members.iter().enumerate() {
        charge(work, 1, source.span)?;
        if let SurfaceForeignMember::Symbol(value) = member {
            let symbol = prepare_symbol(&prepared, member_index, value, work)?;
            prepared.symbols.push(symbol);
        }
    }
    validate_owner_teardowns(&prepared, work)?;
    validate_destruction_operands(&prepared, work)?;
    access_contract::validate_preserving_symbols(&prepared, work)?;
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
) -> Result<PreparedRepresentation, ForeignContractError> {
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
fn sentinel_operand(
    library: &PreparedForeignLibrary,
    abi: &SurfaceForeignAbiRepresentation,
    input: Option<&SurfaceForeignOperandSource>,
    work: &mut TypeWorkBudget,
) -> Result<Option<PreparedOperandSource>, ForeignContractError> {
    let SurfaceForeignAbiRepresentation::Member(reference) = abi else {
        return Ok(None);
    };
    // Preserve existing scalar/owner ledger prefixes when this role is absent.
    if library.sentinels.is_empty() {
        return Ok(None);
    }
    let name = local_reference(reference)?;
    let mut representation_index = None;
    for (index, declaration) in library.representations.iter().enumerate() {
        if names_equal(declaration.name(), name, reference.span, work)? {
            if declaration.representation() != PreparedRepresentation::FunctionAddressSentinel {
                return Ok(None);
            }
            representation_index = Some(index);
            break;
        }
    }
    let Some(representation_index) = representation_index else {
        return Ok(None);
    };
    let Some(SurfaceForeignOperandSource::Constant(member)) = input else {
        return Err(failure(ForeignContractReason::OperandRole, reference.span));
    };
    let member_name = local_reference(member)?;
    for (index, sentinel) in library.sentinels.iter().enumerate() {
        if names_equal(sentinel.name(), member_name, member.span, work)? {
            if sentinel.representation_index != representation_index {
                return Err(failure(ForeignContractReason::OperandRole, member.span));
            }
            return Ok(Some(PreparedOperandSource::Sentinel(index)));
        }
    }
    Err(failure(ForeignContractReason::UnknownMember, member.span))
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
            match representation(library, reference, work)? {
                PreparedRepresentation::Scalar(value) => Ok(PreparedAbiResult::Scalar(value)),
                PreparedRepresentation::Address(_)
                | PreparedRepresentation::FunctionAddressSentinel => Err(failure(
                    ForeignContractReason::UnsupportedRepresentation,
                    reference.span,
                )),
            }
        }
        SurfaceForeignAbiRepresentation::Pointer {
            representation: reference,
            span,
        } => {
            if library.owners.is_empty() {
                return Err(failure(ForeignContractReason::UnimplementedContract, *span));
            }
            match representation(library, reference, work)? {
                PreparedRepresentation::Address(value) => Ok(PreparedAbiResult::Address(value)),
                PreparedRepresentation::Scalar(_)
                | PreparedRepresentation::FunctionAddressSentinel => {
                    Err(failure(ForeignContractReason::UnimplementedContract, *span))
                }
            }
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
    let (path, selected) = owner_source_path(position, domain, work)?;
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
    member_index: usize,
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
        member_index,
        name: text(&source.name.text, source.name.span, work)?,
        native_name: text(&source.native_name.value, source.native_name.span, work)?,
        parameters: Vec::new(),
        native_type_projection: Vec::new(),
        operands: Vec::new(),
        destruction_operands: Vec::new(),
        result: abi_result(library, &source.abi_result, work)?,
        call: PreparedForeignCall::Scalar {
            outcomes: Vec::new(),
        },
        access_result: None,
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
    charge(work, source.contracts.len(), source.span)?;
    let capture_count = source
        .contracts
        .iter()
        .filter(|contract| matches!(contract, SurfaceForeignContract::DestructionOperand { .. }))
        .count();
    reserve(&mut symbol.destruction_operands, capture_count, source.span)?;
    for contract in &source.contracts {
        charge(work, 1, source.span)?;
        if let SurfaceForeignContract::DestructionOperand {
            position,
            source,
            span,
        } = contract
        {
            let PreparedNativePosition::Argument(position) = native_position(position, work)?
            else {
                return Err(failure(ForeignContractReason::OperandCoverage, *span));
            };
            let path = source_path(source, &function.domain, work)?;
            // Pay both the search and shift before canonical target insertion.
            charge(
                work,
                symbol.destruction_operands.len().saturating_mul(2),
                *span,
            )?;
            let index = match symbol
                .destruction_operands
                .binary_search_by_key(&position, |value| value.position)
            {
                Ok(_) => return Err(failure(ForeignContractReason::OperandCoverage, *span)),
                Err(index) => index,
            };
            symbol.destruction_operands.insert(
                index,
                PreparedDestructionOperand {
                    position,
                    source: path,
                    origin: Origin::Source(*span),
                },
            );
        }
    }
    if !library.owners.is_empty() {
        charge(work, source.contracts.len(), source.span)?;
        let owner_contract = source.contracts.iter().find_map(|contract| match contract {
            SurfaceForeignContract::Operand {
                source: SurfaceForeignOperandSource::Source { role, .. },
                ..
            } if matches!(role.kind, SurfaceForeignOperandRoleKind::Current) => Some(false),
            SurfaceForeignContract::Output { position, role, .. }
                if matches!(role.kind, SurfaceForeignOutputRoleKind::Owner(_))
                    && matches!(position, SurfaceForeignNativePosition::Argument(_)) =>
            {
                Some(true)
            }
            _ => None,
        });
        if owner_contract == Some(true) {
            return output_contract::prepare(library, source, symbol, &function.domain, work);
        }
        let current = owner_contract.is_some();
        if current || matches!(symbol.result, PreparedAbiResult::Address(_)) {
            return prepare_owner_symbol_body(library, source, symbol, &function.domain, work);
        }
    }
    if matches!(symbol.result, PreparedAbiResult::Address(_)) {
        return Err(failure(ForeignContractReason::OutputRole, source.span));
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
        if let Some(mapping) =
            sentinel_operand(library, &operand.representation, mappings[index], work)?
        {
            symbol.operands.push(PreparedForeignOperand {
                representation: PreparedRepresentation::FunctionAddressSentinel,
                source: mapping,
                origin: Origin::Source(operand.span),
            });
            continue;
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
            representation: PreparedRepresentation::Scalar(representation),
            source: mapping,
            origin: Origin::Source(operand.span),
        });
    }
    drop(mappings);
    let mut output = false;
    let mut otherwise = false;
    let PreparedForeignCall::Scalar { outcomes } = &mut symbol.call else {
        return Err(failure(ForeignContractReason::OutputRole, source.span));
    };
    reserve(outcomes, outcome_count, source.span)?;
    for contract in &source.contracts {
        charge(work, 1, source.span)?;
        match contract {
            SurfaceForeignContract::Operand { .. }
            | SurfaceForeignContract::DestructionOperand { .. } => {}
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
                        for previous in outcomes.iter() {
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
                outcomes.push(PreparedForeignOutcome {
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

fn prepare_parameters(
    source: &[SurfaceTypeParameter],
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<Vec<PreparedForeignParameter>, ForeignContractError> {
    charge(work, source.len(), span)?;
    let mut result: Vec<PreparedForeignParameter> = Vec::new();
    reserve(&mut result, source.len(), span)?;
    for parameter in source {
        charge(work, 1, parameter.span)?;
        for previous in &result {
            if names_equal(&previous.name, &parameter.name.text, parameter.span, work)? {
                return Err(failure(
                    ForeignContractReason::InvalidParameters,
                    parameter.span,
                ));
            }
        }
        let kind = match parameter.kind.as_ref().map(|value| &value.kind) {
            None | Some(SurfaceKindKind::Type) => Kind::Type,
            Some(SurfaceKindKind::EffectRow) => Kind::EffectRow,
            _ => {
                return Err(failure(
                    ForeignContractReason::UnimplementedContract,
                    parameter.span,
                ));
            }
        };
        result.push(PreparedForeignParameter {
            name: text(&parameter.name.text, parameter.name.span, work)?,
            kind,
            origin: Origin::Source(parameter.span),
        });
    }
    Ok(result)
}

fn prepare_owner(
    library: &PreparedForeignLibrary,
    surface: &SurfaceForeignLibrary,
    member_index: usize,
    source: &SurfaceForeignOwner,
    work: &mut TypeWorkBudget,
) -> Result<PreparedForeignOwner, ForeignContractError> {
    let PreparedRepresentation::Address(representation) =
        representation(library, &source.representation, work)?
    else {
        return Err(failure(
            ForeignContractReason::OperandRole,
            source.representation.span,
        ));
    };
    let parameters = prepare_parameters(&source.parameters, source.span, work)?;
    let mut owned_parameter = None;
    for (index, parameter) in parameters.iter().enumerate() {
        if names_equal(&parameter.name, &source.owned.text, source.owned.span, work)? {
            if parameter.kind != Kind::Type {
                return Err(failure(
                    ForeignContractReason::InvalidParameters,
                    source.owned.span,
                ));
            }
            owned_parameter = Some(index);
        }
    }
    let owned_parameter = owned_parameter
        .ok_or_else(|| failure(ForeignContractReason::InvalidParameters, source.owned.span))?;
    let mut retains = Vec::new();
    reserve(&mut retains, source.retains.len(), source.span)?;
    for dependency in &source.retains {
        let mut selected = None;
        for (index, parameter) in parameters.iter().enumerate() {
            if names_equal(&parameter.name, &dependency.text, dependency.span, work)? {
                selected = Some(index);
            }
        }
        let index = selected
            .ok_or_else(|| failure(ForeignContractReason::InvalidParameters, dependency.span))?;
        charge(work, retains.len().saturating_add(1), dependency.span)?;
        if index == owned_parameter
            || parameters[index].kind != Kind::Type
            || retains.contains(&index)
        {
            return Err(failure(
                ForeignContractReason::InvalidParameters,
                dependency.span,
            ));
        }
        retains.push(index);
    }
    let teardown_name = local_reference(&source.teardown)?;
    let mut teardown_member = None;
    for (index, member) in surface.members.iter().enumerate() {
        charge(work, 1, source.teardown.span)?;
        if let SurfaceForeignMember::Symbol(symbol) = member
            && names_equal(&symbol.name.text, teardown_name, source.teardown.span, work)?
        {
            teardown_member = Some(index);
        }
    }
    Ok(PreparedForeignOwner {
        member_index,
        name: text(&source.name.text, source.name.span, work)?,
        parameters,
        owned_parameter,
        retains,
        representation,
        representation_span: source.representation.span,
        owned_span: source.owned.span,
        teardown_span: source.teardown.span,
        teardown_member: teardown_member
            .ok_or_else(|| failure(ForeignContractReason::UnknownMember, source.teardown.span))?,
        origin: Origin::Source(source.span),
    })
}

fn owner_application(
    library: &PreparedForeignLibrary,
    symbol: &PreparedForeignSymbol,
    ty: &SurfaceType,
    work: &mut TypeWorkBudget,
) -> Result<PreparedOwnerApplication, ForeignContractError> {
    owner_application_from_parameters(library, &symbol.parameters, ty, work)
}

fn owner_application_from_parameters(
    library: &PreparedForeignLibrary,
    parameters: &[PreparedForeignParameter],
    ty: &SurfaceType,
    work: &mut TypeWorkBudget,
) -> Result<PreparedOwnerApplication, ForeignContractError> {
    let SurfaceTypeKind::Application {
        constructor,
        arguments,
    } = &ty.kind
    else {
        return Err(failure(ForeignContractReason::OutputRole, ty.span));
    };
    if constructor.qualifier().is_some() {
        return Err(failure(
            ForeignContractReason::UnimplementedContract,
            ty.span,
        ));
    }
    let mut owner = None;
    for (index, candidate) in library.owners.iter().enumerate() {
        if names_equal(&candidate.name, &constructor.member().text, ty.span, work)? {
            owner = Some(index);
        }
    }
    let owner = owner.ok_or_else(|| failure(ForeignContractReason::UnknownMember, ty.span))?;
    let family = &library.owners[owner];
    let projection = project_arguments(parameters, arguments, &family.parameters, ty.span, work)?;
    Ok(PreparedOwnerApplication {
        owner,
        arguments: projection,
        span: ty.span,
    })
}

fn project_arguments(
    parameters: &[PreparedForeignParameter],
    arguments: &[SurfaceType],
    expected: &[PreparedForeignParameter],
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<Vec<PreparedOwnerArgument>, ForeignContractError> {
    charge(work, arguments.len(), span)?;
    if arguments.len() != expected.len() {
        return Err(failure(ForeignContractReason::InvalidParameters, span));
    }
    let mut projection = Vec::new();
    reserve(&mut projection, arguments.len(), span)?;
    for (argument, expected) in arguments.iter().zip(expected) {
        let name = match (&argument.kind, &expected.kind) {
            (SurfaceTypeKind::Named(reference), Kind::Type) if reference.qualifier().is_none() => {
                reference.member()
            }
            (SurfaceTypeKind::RowArgument(row), Kind::EffectRow) if row.effects.is_empty() => {
                row.tail.as_ref().ok_or_else(|| {
                    failure(ForeignContractReason::UnimplementedContract, argument.span)
                })?
            }
            _ => {
                return Err(failure(
                    ForeignContractReason::UnimplementedContract,
                    argument.span,
                ));
            }
        };
        let mut parameter = None;
        for (index, candidate) in parameters.iter().enumerate() {
            if names_equal(&candidate.name, &name.text, argument.span, work)?
                && candidate.kind == expected.kind
            {
                parameter = Some(index);
            }
        }
        let parameter = parameter
            .ok_or_else(|| failure(ForeignContractReason::InvalidParameters, argument.span))?;
        projection.push(match expected.kind {
            Kind::Type => PreparedOwnerArgument::Type(parameter),
            Kind::EffectRow => PreparedOwnerArgument::EffectRow(parameter),
            _ => {
                return Err(failure(
                    ForeignContractReason::InvalidParameters,
                    argument.span,
                ));
            }
        });
    }
    Ok(projection)
}

fn owner_source_path<'a>(
    position: &SurfaceForeignSourcePosition,
    domain: &'a SurfaceType,
    work: &mut TypeWorkBudget,
) -> Result<(Vec<usize>, &'a SurfaceType), ForeignContractError> {
    charge(work, position.components.len(), position.span)?;
    let mut path = Vec::new();
    reserve(&mut path, position.components.len(), position.span)?;
    for component in &position.components {
        path.push(position_integer(component, work)?);
    }
    let (first, rest) = path
        .split_first()
        .ok_or_else(|| failure(ForeignContractReason::SourcePosition, position.span))?;
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
    Ok((path, selected))
}

fn prepare_owner_symbol_body(
    library: &PreparedForeignLibrary,
    source: &SurfaceForeignSymbol,
    mut symbol: PreparedForeignSymbol,
    domain: &SurfaceType,
    work: &mut TypeWorkBudget,
) -> Result<PreparedForeignSymbol, ForeignContractError> {
    charge(work, source.abi_operands.len(), source.span)?;
    reserve(&mut symbol.operands, source.abi_operands.len(), source.span)?;
    let mut mappings = Vec::new();
    reserve(&mut mappings, source.abi_operands.len(), source.span)?;
    mappings.resize_with(source.abi_operands.len(), || None);
    let mut output = None;
    let mut scalar_output = None;
    let mut block = None;
    let mut cases = Vec::new();
    // This temporary stores borrowed source cases, never recursive owned syntax.
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
            } => {
                if output.is_some()
                    || scalar_output.is_some()
                    || symbol.access_result.is_some()
                    || native_position(position, work)? != PreparedNativePosition::Result
                {
                    return Err(failure(ForeignContractReason::OutputCoverage, *span));
                }
                match &role.kind {
                    SurfaceForeignOutputRoleKind::Owner(ty) => {
                        output = Some(owner_application(library, &symbol, ty, work)?);
                    }
                    SurfaceForeignOutputRoleKind::Scalar => scalar_output = Some(*span),
                    SurfaceForeignOutputRoleKind::View { .. }
                    | SurfaceForeignOutputRoleKind::ExtentOf { .. } => {
                        symbol.access_result = Some(access_contract::prepare_result(
                            library, &symbol, &role.kind, domain, *span, work,
                        )?);
                    }
                    _ => {
                        return Err(failure(
                            ForeignContractReason::UnimplementedContract,
                            role.span,
                        ));
                    }
                }
            }
            SurfaceForeignContract::RetainedDependentsBlock { span } => {
                if block.replace(*span).is_some() {
                    return Err(failure(ForeignContractReason::OutcomeCoverage, *span));
                }
            }
            SurfaceForeignContract::Outcome { test, facts, span } => {
                if cases.len() == cases.capacity() {
                    reserve(&mut cases, 1, *span)?;
                }
                cases.push((test, facts.as_slice(), *span));
            }
        }
    }
    let mut current = None;
    for (index, operand) in source.abi_operands.iter().enumerate() {
        charge(work, 1, operand.span)?;
        if operand.output {
            return Err(failure(
                ForeignContractReason::UnimplementedContract,
                operand.span,
            ));
        }
        let input = mappings[index]
            .ok_or_else(|| failure(ForeignContractReason::OperandCoverage, operand.span))?;
        if let Some(mapping) =
            sentinel_operand(library, &operand.representation, Some(input), work)?
        {
            symbol.operands.push(PreparedForeignOperand {
                representation: PreparedRepresentation::FunctionAddressSentinel,
                source: mapping,
                origin: Origin::Source(operand.span),
            });
            continue;
        }
        let (representation, mapping) =
            match (abi_result(library, &operand.representation, work)?, input) {
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
                    PreparedAbiResult::Address(representation),
                    SurfaceForeignOperandSource::Source { position, role },
                ) if matches!(role.kind, SurfaceForeignOperandRoleKind::Bytes { .. }) => {
                    let SurfaceForeignOperandRoleKind::Bytes { extent, discipline } = &role.kind
                    else {
                        unreachable!()
                    };
                    let (path, ty) = owner_source_path(position, domain, work)?;
                    if representation != PreparedAddressRepresentation::Bytes
                        || !matches!(ty.kind, SurfaceTypeKind::Bytes | SurfaceTypeKind::String)
                        || scalar_output.is_none()
                        || output.is_some()
                        || block.is_some()
                        || symbol.access_result.is_some()
                    {
                        return Err(failure(ForeignContractReason::OperandRole, role.span));
                    }
                    (
                        PreparedRepresentation::Address(representation),
                        PreparedOperandSource::Bytes {
                            path,
                            extent: source_path(extent, domain, work)?,
                            copy: matches!(
                                discipline,
                                crate::surface::SurfaceForeignInputDiscipline::Copy(_)
                            ),
                        },
                    )
                }
                (
                    PreparedAbiResult::Address(representation),
                    SurfaceForeignOperandSource::Source { position, role },
                ) if matches!(role.kind, SurfaceForeignOperandRoleKind::Current) => {
                    if current.is_some() {
                        return Err(failure(
                            ForeignContractReason::UnimplementedContract,
                            role.span,
                        ));
                    }
                    let (path, ty) = owner_source_path(position, domain, work)?;
                    let application = owner_application(library, &symbol, ty, work)?;
                    if library.owners[application.owner].representation != representation {
                        return Err(failure(ForeignContractReason::OperandRole, role.span));
                    }
                    current = Some((index, application));
                    (
                        PreparedRepresentation::Address(representation),
                        PreparedOperandSource::Current(path),
                    )
                }
                (
                    PreparedAbiResult::Address(representation),
                    SurfaceForeignOperandSource::Source { position, role },
                ) if matches!(role.kind, SurfaceForeignOperandRoleKind::Enclosing) => {
                    let (path, _ty) = owner_source_path(position, domain, work)?;
                    // Defining owner/type/kind and dependency-role correspondence
                    // is authenticated against the resolved original signature.
                    (
                        PreparedRepresentation::Address(representation),
                        PreparedOperandSource::Enclosing(path),
                    )
                }
                (PreparedAbiResult::Void, _) => {
                    return Err(failure(ForeignContractReason::VoidPosition, operand.span));
                }
                _ => {
                    return Err(failure(
                        ForeignContractReason::UnimplementedContract,
                        operand.span,
                    ));
                }
            };
        symbol.operands.push(PreparedForeignOperand {
            representation,
            source: mapping,
            origin: Origin::Source(operand.span),
        });
    }
    if let Some(application) = output {
        let PreparedAbiResult::Address(representation) = symbol.result else {
            return Err(failure(ForeignContractReason::OutputRole, source.span));
        };
        if representation != library.owners[application.owner].representation
            || current.is_some()
            || scalar_output.is_some()
            || block.is_some()
            || cases.len() != 2
        {
            return Err(failure(
                ForeignContractReason::UnimplementedContract,
                source.span,
            ));
        }
        let SurfaceForeignOutcomeTest::All(atoms) = cases[0].0 else {
            return Err(failure(ForeignContractReason::OutcomeCoverage, cases[0].2));
        };
        charge(work, atoms.len(), cases[0].2)?;
        if atoms.len() != 1
            || native_position(&atoms[0].position, work)? != PreparedNativePosition::Result
            || !matches!(cases[1].0, SurfaceForeignOutcomeTest::Otherwise(_))
        {
            return Err(failure(ForeignContractReason::OutcomeCoverage, source.span));
        }
        let first_nonnull = match atoms[0].condition {
            SurfaceForeignOutcomeCondition::NonNull(_) => true,
            SurfaceForeignOutcomeCondition::Null(_) => false,
            _ => {
                return Err(failure(
                    ForeignContractReason::UnimplementedContract,
                    atoms[0].span,
                ));
            }
        };
        let mut readable_spans = [source.span; 2];
        let mut initialized = None;
        for (index, (_, facts, span)) in cases.iter().enumerate() {
            let nonnull = if index == 0 {
                first_nonnull
            } else {
                !first_nonnull
            };
            let mut readable = false;
            for fact in *facts {
                charge(work, 1, fact.span)?;
                match &fact.kind {
                    SurfaceForeignOutcomeFactKind::Readable(position)
                        if !readable
                            && native_position(position, work)?
                                == PreparedNativePosition::Result =>
                    {
                        readable = true;
                        readable_spans[index] = fact.span;
                    }
                    SurfaceForeignOutcomeFactKind::InitializedBytes { position, extent }
                        if nonnull
                            && initialized.is_none()
                            && native_position(position, work)?
                                == PreparedNativePosition::Result =>
                    {
                        initialized = Some((source_path(extent, domain, work)?, fact.span));
                    }
                    _ => {
                        return Err(failure(
                            ForeignContractReason::UnimplementedContract,
                            fact.span,
                        ));
                    }
                }
            }
            if !readable
                || (nonnull
                    && representation == PreparedAddressRepresentation::Bytes
                    && initialized.is_none())
            {
                return Err(failure(ForeignContractReason::Readability, *span));
            }
        }
        let initialized_bytes =
            initialized.map(|(extent, span)| PreparedInitializedBytes { extent, span });
        symbol.call = PreparedForeignCall::Owner(PreparedOwnerCall::Acquire {
            application,
            first_nonnull,
            condition_span: atoms[0].span,
            outcome_spans: [cases[0].2, cases[1].2],
            readable_spans,
            initialized_bytes,
        });
    } else {
        let (current_operand, application) =
            current.ok_or_else(|| failure(ForeignContractReason::OperandCoverage, source.span))?;
        if let Some(access) = &symbol.access_result {
            let (expected_owner, expected_arguments) =
                access_contract::access_owner(library, access.application(), work)?;
            charge(work, expected_arguments.len(), source.span)?;
            if application.owner() != expected_owner
                || application.arguments() != expected_arguments
                || block.is_some()
                || scalar_output.is_some()
                || cases.len() != 1
                || !matches!(cases[0].0, SurfaceForeignOutcomeTest::Otherwise(_))
                || !matches!(
                    (access, symbol.result),
                    (
                        PreparedAccessResult::View { .. },
                        PreparedAbiResult::Address(PreparedAddressRepresentation::Bytes)
                    ) | (
                        PreparedAccessResult::Extent { .. },
                        PreparedAbiResult::Scalar(_)
                    )
                )
            {
                return Err(failure(ForeignContractReason::OutputRole, source.span));
            }
            charge(work, cases[0].1.len(), cases[0].2)?;
            let [fact] = cases[0].1 else {
                return Err(failure(ForeignContractReason::Readability, cases[0].2));
            };
            if !matches!(&fact.kind, SurfaceForeignOutcomeFactKind::Readable(position) if native_position(position, work)? == PreparedNativePosition::Result)
            {
                return Err(failure(ForeignContractReason::Readability, fact.span));
            }
            symbol.call = PreparedForeignCall::Owner(PreparedOwnerCall::Borrow {
                application,
                current_operand,
                output_span: access.span(),
                outcome_span: cases[0].2,
                readable_span: fact.span,
            });
            return Ok(symbol);
        }
        if let PreparedAbiResult::Scalar(representation) = symbol.result {
            let output_span = scalar_output
                .ok_or_else(|| failure(ForeignContractReason::OutputCoverage, source.span))?;
            if block.is_none() {
                if cases.len() != 1
                    || !matches!(cases[0].0, SurfaceForeignOutcomeTest::Otherwise(_))
                {
                    return Err(failure(ForeignContractReason::OutcomeCoverage, source.span));
                }
                charge(work, cases[0].1.len(), cases[0].2)?;
                let [fact] = cases[0].1 else {
                    return Err(failure(ForeignContractReason::Readability, cases[0].2));
                };
                if !matches!(&fact.kind, SurfaceForeignOutcomeFactKind::Readable(position) if native_position(position, work)? == PreparedNativePosition::Result)
                {
                    return Err(failure(ForeignContractReason::Readability, fact.span));
                }
                symbol.call = PreparedForeignCall::Owner(PreparedOwnerCall::Borrow {
                    application,
                    current_operand,
                    output_span,
                    outcome_span: cases[0].2,
                    readable_span: fact.span,
                });
                return Ok(symbol);
            }
            let block_span = block
                .ok_or_else(|| failure(ForeignContractReason::OutcomeCoverage, source.span))?;
            let PreparedOperandSource::Current(current_path) =
                &symbol.operands[current_operand].source
            else {
                return Err(failure(ForeignContractReason::OperandRole, source.span));
            };
            let outcomes = prepare_owner_status_outcomes(
                library,
                domain,
                representation,
                current_path,
                &cases,
                source.span,
                work,
            )?;
            symbol.call = PreparedForeignCall::Owner(PreparedOwnerCall::StatusTeardown {
                application,
                current_operand,
                output_span,
                block_span,
                outcomes,
            });
            return Ok(symbol);
        }
        if symbol.result != PreparedAbiResult::Void
            || scalar_output.is_some()
            || cases.len() != 1
            || !matches!(cases[0].0, SurfaceForeignOutcomeTest::Otherwise(_))
        {
            return Err(failure(
                ForeignContractReason::UnimplementedContract,
                source.span,
            ));
        }
        let block_span =
            block.ok_or_else(|| failure(ForeignContractReason::OutcomeCoverage, source.span))?;
        let facts = cases[0].1;
        charge(work, facts.len(), cases[0].2)?;
        if facts.len() != 1 {
            return Err(failure(ForeignContractReason::OutcomeCoverage, cases[0].2));
        }
        let (position, consumes) = match &facts[0].kind {
            SurfaceForeignOutcomeFactKind::Consumed(position) => (position, true),
            SurfaceForeignOutcomeFactKind::Retained(position) => (position, false),
            _ => {
                return Err(failure(
                    ForeignContractReason::OutcomeCoverage,
                    facts[0].span,
                ));
            }
        };
        let (disposition_path, _) = owner_source_path(position, domain, work)?;
        let PreparedOperandSource::Current(current_path) = &symbol.operands[current_operand].source
        else {
            return Err(failure(ForeignContractReason::OperandRole, source.span));
        };
        charge(work, current_path.len(), facts[0].span)?;
        if disposition_path != *current_path {
            return Err(failure(ForeignContractReason::OperandRole, facts[0].span));
        }
        symbol.call = PreparedForeignCall::Owner(PreparedOwnerCall::Teardown {
            application,
            current_operand,
            consumes,
            disposition_span: facts[0].span,
            block_span,
            outcome_span: cases[0].2,
        });
    }
    Ok(symbol)
}

#[allow(clippy::too_many_arguments)]
fn prepare_owner_status_outcomes(
    library: &PreparedForeignLibrary,
    domain: &SurfaceType,
    representation: PreparedScalarRepresentation,
    current_path: &[usize],
    cases: &[(
        &SurfaceForeignOutcomeTest,
        &[SurfaceForeignOutcomeFact],
        Span,
    )],
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<Vec<PreparedOwnerStatusOutcome>, ForeignContractError> {
    let mut outcomes: Vec<PreparedOwnerStatusOutcome> = Vec::new();
    charge(work, cases.len(), span)?;
    reserve(&mut outcomes, cases.len(), span)?;
    let mut otherwise = false;
    for (test, facts, outcome_span) in cases {
        charge(work, 1, *outcome_span)?;
        if otherwise {
            return Err(failure(
                ForeignContractReason::OutcomeCoverage,
                *outcome_span,
            ));
        }
        let mut predicates = Vec::new();
        match test {
            SurfaceForeignOutcomeTest::Otherwise(_) => otherwise = true,
            SurfaceForeignOutcomeTest::All(atoms) => {
                if atoms.is_empty() {
                    return Err(failure(
                        ForeignContractReason::OutcomeCoverage,
                        *outcome_span,
                    ));
                }
                charge(work, atoms.len(), *outcome_span)?;
                reserve(&mut predicates, atoms.len(), *outcome_span)?;
                for atom in atoms {
                    charge(work, 1, atom.span)?;
                    let position = native_position(&atom.position, work)?;
                    if position != PreparedNativePosition::Result {
                        return Err(failure(ForeignContractReason::OutcomeCoverage, atom.span));
                    }
                    let SurfaceForeignOutcomeCondition::Equal(reference) = &atom.condition else {
                        return Err(failure(
                            ForeignContractReason::UnimplementedContract,
                            atom.span,
                        ));
                    };
                    let (_, value) = constant(library, reference, work)?;
                    if value.representation != representation {
                        return Err(failure(ForeignContractReason::OperandRole, reference.span));
                    }
                    charge(work, predicates.len(), atom.span)?;
                    if predicates
                        .iter()
                        .any(|previous: &PreparedOutcomePredicate| previous.position == position)
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
                for previous in &outcomes {
                    charge(
                        work,
                        previous.predicates.len().saturating_mul(predicates.len()),
                        *outcome_span,
                    )?;
                    // This result-only profile has one scalar selector. Two
                    // equal selectors overlap regardless of their disposition.
                    if previous.predicates == predicates {
                        return Err(failure(
                            ForeignContractReason::OverlappingOutcomes,
                            *outcome_span,
                        ));
                    }
                }
            }
        }
        let mut disposition = None;
        let mut readability = None;
        charge(work, facts.len(), *outcome_span)?;
        for fact in *facts {
            match &fact.kind {
                SurfaceForeignOutcomeFactKind::Consumed(position)
                | SurfaceForeignOutcomeFactKind::Retained(position) => {
                    let (path, _) = owner_source_path(position, domain, work)?;
                    charge(work, current_path.len(), fact.span)?;
                    if path != current_path || disposition.is_some() {
                        return Err(failure(ForeignContractReason::OperandRole, fact.span));
                    }
                    disposition = Some((
                        matches!(fact.kind, SurfaceForeignOutcomeFactKind::Consumed(_)),
                        fact.span,
                    ));
                }
                SurfaceForeignOutcomeFactKind::Readable(position)
                | SurfaceForeignOutcomeFactKind::Unreadable(position) => {
                    if native_position(position, work)? != PreparedNativePosition::Result
                        || readability.is_some()
                    {
                        return Err(failure(ForeignContractReason::Readability, fact.span));
                    }
                    readability = Some((
                        matches!(fact.kind, SurfaceForeignOutcomeFactKind::Readable(_)),
                        fact.span,
                    ));
                }
                _ => {
                    return Err(failure(
                        ForeignContractReason::UnimplementedContract,
                        fact.span,
                    ));
                }
            }
        }
        let (consumes, disposition_span) = disposition
            .ok_or_else(|| failure(ForeignContractReason::OutcomeCoverage, *outcome_span))?;
        let (readable, readability_span) = readability
            .ok_or_else(|| failure(ForeignContractReason::Readability, *outcome_span))?;
        if !readable {
            return Err(failure(
                ForeignContractReason::Readability,
                readability_span,
            ));
        }
        outcomes.push(PreparedOwnerStatusOutcome {
            predicates,
            consumes,
            readable,
            disposition_span,
            readability_span,
            outcome_span: *outcome_span,
        });
    }
    if !otherwise {
        return Err(failure(ForeignContractReason::OutcomeCoverage, span));
    }
    Ok(outcomes)
}

fn validate_owner_teardowns(
    library: &PreparedForeignLibrary,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignContractError> {
    for (index, owner) in library.owners.iter().enumerate() {
        let span = owner.origin.primary_span();
        charge(work, library.symbols.len().saturating_add(1), span)?;
        let symbol = library
            .symbols
            .iter()
            .find(|symbol| symbol.member_index == owner.teardown_member)
            .ok_or_else(|| failure(ForeignContractReason::UnknownMember, span))?;
        if !matches!(&symbol.call, PreparedForeignCall::Owner(PreparedOwnerCall::Teardown { application, .. } | PreparedOwnerCall::StatusTeardown { application, .. }) if application.owner == index)
        {
            return Err(failure(ForeignContractReason::OperandRole, span));
        }
    }
    Ok(())
}

fn validate_destruction_operands(
    library: &PreparedForeignLibrary,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignContractError> {
    charge(work, library.symbols.len(), library.origin.primary_span())?;
    for producer in &library.symbols {
        let span = producer.origin.primary_span();
        let application = match producer.owner_call() {
            Some(
                PreparedOwnerCall::Acquire { application, .. }
                | PreparedOwnerCall::OutputAcquire { application, .. },
            ) => application,
            _ if producer.destruction_operands.is_empty() => continue,
            _ => return Err(failure(ForeignContractReason::OperandRole, span)),
        };
        charge(work, library.symbols.len().saturating_add(1), span)?;
        let owner = library
            .owners
            .get(application.owner)
            .ok_or_else(|| failure(ForeignContractReason::OperandRole, span))?;
        let destructor = library
            .symbols
            .iter()
            .find(|symbol| symbol.member_index == owner.teardown_member)
            .ok_or_else(|| failure(ForeignContractReason::UnknownMember, span))?;
        if !matches!(destructor.owner_call(), Some(PreparedOwnerCall::Teardown { application: actual, .. } | PreparedOwnerCall::StatusTeardown { application: actual, .. }) if actual.owner == application.owner)
        {
            return Err(failure(ForeignContractReason::OperandRole, span));
        }
        charge(
            work,
            destructor
                .operands
                .len()
                .saturating_add(producer.destruction_operands.len()),
            span,
        )?;
        let mut next = 0;
        for (position, operand) in destructor.operands.iter().enumerate() {
            let PreparedOperandSource::Source(original_path) = &operand.source else {
                continue;
            };
            if !matches!(operand.representation, PreparedRepresentation::Scalar(_)) {
                return Err(failure(ForeignContractReason::OperandRole, span));
            }
            let capture = producer
                .destruction_operands
                .get(next)
                .filter(|capture| capture.position == position)
                .ok_or_else(|| failure(ForeignContractReason::OperandCoverage, span))?;
            let capture_span = capture.origin.primary_span();
            if capture.source.is_empty() || !private_span_within(span, capture_span) {
                return Err(failure(ForeignContractReason::SourcePosition, capture_span));
            }
            for previous in &producer.destruction_operands[..next] {
                charge(work, 1, capture_span)?;
                let previous_operand = destructor
                    .operands
                    .get(previous.position)
                    .ok_or_else(|| failure(ForeignContractReason::OperandCoverage, capture_span))?;
                let PreparedOperandSource::Source(previous_path) = &previous_operand.source else {
                    return Err(failure(ForeignContractReason::OperandRole, capture_span));
                };
                charge(
                    work,
                    original_path
                        .len()
                        .saturating_add(previous_path.len())
                        .saturating_add(capture.source.len())
                        .saturating_add(previous.source.len()),
                    capture_span,
                )?;
                if original_path == previous_path && capture.source != previous.source {
                    return Err(failure(ForeignContractReason::SourcePosition, capture_span));
                }
            }
            next += 1;
        }
        if next != producer.destruction_operands.len() {
            return Err(failure(ForeignContractReason::OperandCoverage, span));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::surface::SurfaceModule;

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

// Compiler-private normalized construction data carries no checked source
// identity or native ownership capability.
// Every origin in this initial image subset is an original Source span; the
// encoder must refuse Generated/Related prepared origins rather than flattening.
pub(crate) struct PrivatePreparedLibraryParts {
    pub(crate) module: ModuleId,
    pub(crate) name: String,
    pub(crate) public: bool,
    pub(crate) representations: Vec<PrivatePreparedRepresentationParts>,
    pub(crate) constants: Vec<PrivatePreparedConstantParts>,
    pub(crate) sentinels: Vec<PrivatePreparedSentinelParts>,
    pub(crate) owners: Vec<PrivatePreparedOwnerParts>,
    pub(crate) accesses: Vec<PreparedForeignAccess>,
    pub(crate) symbols: Vec<PrivatePreparedSymbolParts>,
    pub(crate) span: Span,
}

pub(crate) struct PrivatePreparedRepresentationParts {
    pub(crate) member_index: usize,
    pub(crate) name: String,
    pub(crate) representation: PreparedRepresentation,
    pub(crate) span: Span,
}

pub(crate) struct PrivatePreparedConstantParts {
    pub(crate) member_index: usize,
    pub(crate) name: String,
    pub(crate) representation: PreparedScalarRepresentation,
    pub(crate) value: PreparedScalarValue,
    pub(crate) span: Span,
}

pub(crate) struct PrivatePreparedSentinelParts {
    pub(crate) member_index: usize,
    pub(crate) name: String,
    pub(crate) representation_index: usize,
    pub(crate) span: Span,
}

#[derive(Clone, Copy)]
pub(crate) enum PrivatePreparedParameterKind {
    Type,
    EffectRow,
}

pub(crate) struct PrivatePreparedParameterParts {
    pub(crate) name: String,
    pub(crate) kind: PrivatePreparedParameterKind,
    pub(crate) span: Span,
}

pub(crate) struct PrivatePreparedOwnerParts {
    pub(crate) member_index: usize,
    pub(crate) name: String,
    pub(crate) parameters: Vec<PrivatePreparedParameterParts>,
    pub(crate) owned_parameter: usize,
    pub(crate) retains: Vec<usize>,
    pub(crate) representation: PreparedAddressRepresentation,
    pub(crate) teardown_member: usize,
    pub(crate) representation_span: Span,
    pub(crate) owned_span: Span,
    pub(crate) teardown_span: Span,
    pub(crate) span: Span,
}

pub(crate) struct PrivatePreparedOperandParts {
    pub(crate) representation: PreparedRepresentation,
    pub(crate) source: PreparedOperandSource,
    pub(crate) span: Span,
}

pub(crate) struct PrivatePreparedDestructionOperandParts {
    pub(crate) position: usize,
    pub(crate) source: Vec<usize>,
    pub(crate) span: Span,
}

pub(crate) struct PrivatePreparedOutcomeParts {
    pub(crate) predicates: Vec<PreparedOutcomePredicate>,
    pub(crate) span: Span,
}

#[expect(
    clippy::large_enum_variant,
    reason = "keep normalized owner plans inline without an additional infallible allocation"
)]
pub(crate) enum PrivatePreparedCall {
    Scalar {
        outcomes: Vec<PrivatePreparedOutcomeParts>,
    },
    Owner(PreparedOwnerCall),
}
impl PrivatePreparedCall {
    pub(crate) fn outcomes(&self) -> &[PrivatePreparedOutcomeParts] {
        match self {
            Self::Scalar { outcomes } => outcomes,
            Self::Owner(_) => &[],
        }
    }
}

pub(crate) struct PrivatePreparedSymbolParts {
    pub(crate) member_index: usize,
    pub(crate) name: String,
    pub(crate) native_name: String,
    pub(crate) parameters: Vec<PrivatePreparedParameterParts>,
    pub(crate) native_type_projection: Vec<usize>,
    pub(crate) operands: Vec<PrivatePreparedOperandParts>,
    pub(crate) destruction_operands: Vec<PrivatePreparedDestructionOperandParts>,
    pub(crate) result: PreparedAbiResult,
    pub(crate) call: PrivatePreparedCall,
    pub(crate) access_result: Option<PreparedAccessResult>,
    pub(crate) span: Span,
}

fn private_member_order(
    members: impl Iterator<Item = (usize, Span)>,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignContractError> {
    let mut previous = None;
    for (index, span) in members {
        charge(work, 1, span)?;
        if previous.is_some_and(|previous| previous >= index) {
            return Err(failure(ForeignContractReason::DuplicateMember, span));
        }
        previous = Some(index);
    }
    Ok(())
}

fn private_representation(
    value: PreparedRepresentation,
    span: Span,
) -> Result<(), ForeignContractError> {
    match value {
        PreparedRepresentation::Scalar(value) => private_scalar_representation(value, span),
        PreparedRepresentation::Address(_) | PreparedRepresentation::FunctionAddressSentinel => {
            Ok(())
        }
    }
}

fn private_owner_application<'a>(
    parts: &'a PrivatePreparedLibraryParts,
    symbol: &PrivatePreparedSymbolParts,
    application: &PreparedOwnerApplication,
    work: &mut TypeWorkBudget,
) -> Result<&'a PrivatePreparedOwnerParts, ForeignContractError> {
    charge(
        work,
        application
            .arguments
            .len()
            .checked_add(1)
            .ok_or_else(|| failure(ForeignContractReason::WorkExhausted, application.span))?,
        application.span,
    )?;
    let owner = parts
        .owners
        .get(application.owner)
        .ok_or_else(|| failure(ForeignContractReason::UnknownMember, application.span))?;
    if !private_span_within(symbol.span, application.span)
        || application.arguments.len() != owner.parameters.len()
    {
        return Err(failure(
            ForeignContractReason::InvalidParameters,
            application.span,
        ));
    }
    for (argument, expected) in application.arguments.iter().zip(&owner.parameters) {
        let parameter = symbol
            .parameters
            .get(argument.parameter())
            .ok_or_else(|| failure(ForeignContractReason::InvalidParameters, application.span))?;
        if !matches!(
            (argument, parameter.kind, expected.kind),
            (
                PreparedOwnerArgument::Type(_),
                PrivatePreparedParameterKind::Type,
                PrivatePreparedParameterKind::Type
            ) | (
                PreparedOwnerArgument::EffectRow(_),
                PrivatePreparedParameterKind::EffectRow,
                PrivatePreparedParameterKind::EffectRow
            )
        ) {
            return Err(failure(
                ForeignContractReason::InvalidParameters,
                application.span,
            ));
        }
    }
    Ok(owner)
}

fn private_owner_call(
    parts: &PrivatePreparedLibraryParts,
    symbol: &PrivatePreparedSymbolParts,
    call: &PreparedOwnerCall,
    work: &mut TypeWorkBudget,
) -> Result<(), ForeignContractError> {
    match call {
        PreparedOwnerCall::Borrow {
            application,
            current_operand,
            output_span,
            outcome_span,
            readable_span,
        } => {
            let owner = private_owner_application(parts, symbol, application, work)?;
            charge(work, symbol.operands.len().saturating_add(6), symbol.span)?;
            if !(matches!(symbol.result, PreparedAbiResult::Scalar(_))
                || matches!(
                    symbol.access_result,
                    Some(PreparedAccessResult::View { .. })
                ) && symbol.result
                    == PreparedAbiResult::Address(PreparedAddressRepresentation::Bytes))
                || !symbol
                    .operands
                    .get(*current_operand)
                    .is_some_and(|operand| {
                        matches!(operand.source, PreparedOperandSource::Current(_))
                            && operand.representation
                                == PreparedRepresentation::Address(owner.representation)
                    })
                || symbol
                    .operands
                    .iter()
                    .filter(|operand| matches!(operand.source, PreparedOperandSource::Current(_)))
                    .count()
                    != 1
                || symbol.operands.iter().any(|operand| {
                    matches!(
                        operand.source,
                        PreparedOperandSource::OwnerOutput | PreparedOperandSource::OffsetOutput
                    )
                })
                || !private_span_within(symbol.span, *output_span)
                || !private_span_within(symbol.span, *outcome_span)
                || !private_span_within(*outcome_span, *readable_span)
            {
                return Err(failure(ForeignContractReason::OutputRole, symbol.span));
            }
        }
        PreparedOwnerCall::OutputAcquire {
            application,
            output_operand,
            output_span,
            scalar_output_span,
            outcome_span,
            readable_spans,
            offset,
        } => {
            let owner = private_owner_application(parts, symbol, application, work)?;
            charge(work, symbol.operands.len().saturating_add(9), symbol.span)?;
            let slot = symbol
                .operands
                .get(*output_operand)
                .ok_or_else(|| failure(ForeignContractReason::OutputCoverage, *output_span))?;
            if owner.representation != PreparedAddressRepresentation::Opaque
                || !matches!(symbol.result, PreparedAbiResult::Scalar(_))
                || slot.representation != PreparedRepresentation::Address(owner.representation)
                || !matches!(slot.source, PreparedOperandSource::OwnerOutput)
                || symbol
                    .operands
                    .iter()
                    .filter(|operand| matches!(operand.source, PreparedOperandSource::OwnerOutput))
                    .count()
                    != 1
                || symbol
                    .operands
                    .iter()
                    .any(|operand| matches!(operand.source, PreparedOperandSource::Current(_)))
                || !private_span_within(symbol.span, *output_span)
                || !private_span_within(*output_span, application.span)
                || !private_span_within(symbol.span, *scalar_output_span)
                || output_span == scalar_output_span
                || !private_span_within(symbol.span, *outcome_span)
                || readable_spans[0] == readable_spans[1]
            {
                return Err(failure(ForeignContractReason::OutputRole, symbol.span));
            }
            for span in readable_spans {
                if !private_span_within(*outcome_span, *span) {
                    return Err(failure(ForeignContractReason::Readability, *span));
                }
            }
            match offset {
                None if symbol.operands.iter().all(|operand| {
                    !matches!(operand.source, PreparedOperandSource::OffsetOutput)
                }) => {}
                Some(offset) => {
                    charge(
                        work,
                        symbol.operands.len().saturating_add(13),
                        offset.output_span,
                    )?;
                    let valid_input =
                        symbol
                            .operands
                            .get(offset.input_operand)
                            .is_some_and(|operand| {
                                matches!(operand.source, PreparedOperandSource::Nul(_))
                            });
                    let valid_output = symbol.operands.get(offset.operand).is_some_and(|operand| {
                        matches!(operand.source, PreparedOperandSource::OffsetOutput)
                            && operand.representation
                                == PreparedRepresentation::Address(
                                    PreparedAddressRepresentation::Bytes,
                                )
                    });
                    let PreparedAbiResult::Scalar(representation) = symbol.result else {
                        return Err(failure(ForeignContractReason::OutputRole, symbol.span));
                    };
                    private_scalar_value(offset.status, representation, offset.condition_span)?;
                    if !valid_input
                        || !valid_output
                        || offset.operand == *output_operand
                        || symbol
                            .operands
                            .iter()
                            .filter(|operand| {
                                matches!(operand.source, PreparedOperandSource::OffsetOutput)
                            })
                            .count()
                            != 1
                        || !private_span_within(symbol.span, offset.output_span)
                        || offset.output_span == *output_span
                        || offset.output_span == *scalar_output_span
                        || !private_span_within(*outcome_span, offset.condition_span)
                        || !private_span_within(*outcome_span, offset.readable_span)
                        || readable_spans.contains(&offset.readable_span)
                        || !private_span_within(symbol.span, offset.otherwise_span)
                        || offset.otherwise_span == *outcome_span
                    {
                        return Err(failure(ForeignContractReason::OutputRole, symbol.span));
                    }
                    for (index, span) in offset.otherwise_readable_spans.iter().enumerate() {
                        if !private_span_within(offset.otherwise_span, *span)
                            || offset.otherwise_readable_spans[..index].contains(span)
                        {
                            return Err(failure(ForeignContractReason::Readability, *span));
                        }
                    }
                }
                _ => return Err(failure(ForeignContractReason::OutputRole, symbol.span)),
            }
        }
        PreparedOwnerCall::Acquire {
            application,
            first_nonnull,
            condition_span,
            outcome_spans,
            readable_spans,
            initialized_bytes,
        } => {
            let owner = private_owner_application(parts, symbol, application, work)?;
            charge(
                work,
                symbol
                    .operands
                    .len()
                    .checked_add(
                        initialized_bytes
                            .as_ref()
                            .map_or(0, |value| value.extent.len()),
                    )
                    .and_then(|count| count.checked_add(9))
                    .ok_or_else(|| failure(ForeignContractReason::WorkExhausted, symbol.span))?,
                symbol.span,
            )?;
            if symbol.result != PreparedAbiResult::Address(owner.representation)
                || symbol
                    .operands
                    .iter()
                    .any(|operand| matches!(operand.source, PreparedOperandSource::Current(_)))
                || (owner.representation == PreparedAddressRepresentation::Bytes
                    && initialized_bytes.is_none())
                || !private_span_within(outcome_spans[0], *condition_span)
                || outcome_spans[0].range().end() > outcome_spans[1].range().start()
            {
                return Err(failure(ForeignContractReason::OutputRole, symbol.span));
            }
            if let Some(initialized) = initialized_bytes
                && (initialized.extent.is_empty()
                    || !private_span_within(
                        outcome_spans[usize::from(!*first_nonnull)],
                        initialized.span,
                    ))
            {
                return Err(failure(ForeignContractReason::Readability, symbol.span));
            }
            for (outcome, readable) in outcome_spans.iter().zip(readable_spans) {
                if !private_span_within(symbol.span, *outcome)
                    || !private_span_within(*outcome, *readable)
                {
                    return Err(failure(ForeignContractReason::Readability, symbol.span));
                }
            }
        }
        PreparedOwnerCall::Teardown {
            application,
            current_operand,
            consumes: _,
            disposition_span,
            block_span,
            outcome_span,
        } => {
            let owner = private_owner_application(parts, symbol, application, work)?;
            charge(
                work,
                symbol
                    .operands
                    .len()
                    .checked_add(5)
                    .ok_or_else(|| failure(ForeignContractReason::WorkExhausted, symbol.span))?,
                symbol.span,
            )?;
            let current = symbol
                .operands
                .get(*current_operand)
                .ok_or_else(|| failure(ForeignContractReason::OperandCoverage, symbol.span))?;
            if symbol.result != PreparedAbiResult::Void
                || current.representation != PreparedRepresentation::Address(owner.representation)
                || !matches!(current.source, PreparedOperandSource::Current(_))
                || symbol
                    .operands
                    .iter()
                    .filter(|operand| matches!(operand.source, PreparedOperandSource::Current(_)))
                    .count()
                    != 1
                || !private_span_within(symbol.span, *block_span)
                || !private_span_within(symbol.span, *outcome_span)
                || !private_span_within(*outcome_span, *disposition_span)
            {
                return Err(failure(ForeignContractReason::OperandRole, symbol.span));
            }
        }
        PreparedOwnerCall::StatusTeardown {
            application,
            current_operand,
            output_span,
            block_span,
            outcomes,
        } => {
            let owner = private_owner_application(parts, symbol, application, work)?;
            charge(work, symbol.operands.len().saturating_add(6), symbol.span)?;
            let PreparedAbiResult::Scalar(representation) = symbol.result else {
                return Err(failure(ForeignContractReason::OutputRole, symbol.span));
            };
            let current = symbol
                .operands
                .get(*current_operand)
                .ok_or_else(|| failure(ForeignContractReason::OperandCoverage, symbol.span))?;
            if current.representation != PreparedRepresentation::Address(owner.representation)
                || !matches!(current.source, PreparedOperandSource::Current(_))
                || symbol
                    .operands
                    .iter()
                    .filter(|operand| matches!(operand.source, PreparedOperandSource::Current(_)))
                    .count()
                    != 1
                || !private_span_within(symbol.span, *output_span)
                || !private_span_within(symbol.span, *block_span)
                || outcomes.is_empty()
            {
                return Err(failure(ForeignContractReason::OperandRole, symbol.span));
            }
            for (index, outcome) in outcomes.iter().enumerate() {
                charge(
                    work,
                    outcome
                        .predicates
                        .len()
                        .saturating_add(parts.constants.len())
                        .saturating_add(index)
                        .saturating_add(5),
                    symbol.span,
                )?;
                if !outcome.readable {
                    return Err(failure(
                        ForeignContractReason::Readability,
                        outcome.readability_span,
                    ));
                }
                if !private_span_within(symbol.span, outcome.outcome_span)
                    || !private_span_within(outcome.outcome_span, outcome.disposition_span)
                    || !private_span_within(outcome.outcome_span, outcome.readability_span)
                    || outcome.predicates.is_empty() != (index + 1 == outcomes.len())
                    || (index > 0
                        && outcomes[index - 1].outcome_span.range().end()
                            > outcome.outcome_span.range().start())
                    || outcome.predicates.len() > 1
                    || outcomes[..index]
                        .iter()
                        .any(|previous| previous.predicates == outcome.predicates)
                {
                    return Err(failure(
                        ForeignContractReason::OutcomeCoverage,
                        outcome.outcome_span,
                    ));
                }
                for predicate in &outcome.predicates {
                    if predicate.position != PreparedNativePosition::Result
                        || !parts.constants.iter().any(|constant| {
                            constant.representation == representation
                                && constant.value == predicate.value
                        })
                    {
                        return Err(failure(
                            ForeignContractReason::OutcomeCoverage,
                            outcome.outcome_span,
                        ));
                    }
                    private_scalar_value(predicate.value, representation, outcome.outcome_span)?;
                }
            }
        }
    }
    Ok(())
}

fn same_owner_application(
    left: &PreparedOwnerApplication,
    right: &PreparedOwnerApplication,
    work: &mut TypeWorkBudget,
) -> Result<bool, ForeignContractError> {
    charge(work, 3, right.span)?;
    if left.owner != right.owner
        || left.span != right.span
        || left.arguments.len() != right.arguments.len()
    {
        return Ok(false);
    }
    charge(work, right.arguments.len(), right.span)?;
    Ok(left.arguments == right.arguments)
}

fn same_owner_call(
    left: Option<&PreparedOwnerCall>,
    right: Option<&PreparedOwnerCall>,
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<bool, ForeignContractError> {
    if left.is_none() && right.is_none() {
        return Ok(true);
    }
    charge(work, 1, span)?;
    match (left, right) {
        (
            Some(PreparedOwnerCall::Borrow {
                application: la,
                current_operand: lc,
                output_span: lo,
                outcome_span: ls,
                readable_span: lr,
            }),
            Some(PreparedOwnerCall::Borrow {
                application: ra,
                current_operand: rc,
                output_span: ro,
                outcome_span: rs,
                readable_span: rr,
            }),
        ) => {
            charge(work, 5, span)?;
            Ok(lc == rc
                && lo == ro
                && ls == rs
                && lr == rr
                && same_owner_application(la, ra, work)?)
        }
        (
            Some(PreparedOwnerCall::OutputAcquire {
                application: la,
                output_operand: lp,
                output_span: lo,
                scalar_output_span: ls,
                outcome_span: lc,
                readable_spans: lr,
                offset: l_offset,
            }),
            Some(PreparedOwnerCall::OutputAcquire {
                application: ra,
                output_operand: rp,
                output_span: ro,
                scalar_output_span: rs,
                outcome_span: rc,
                readable_spans: rr,
                offset: r_offset,
            }),
        ) => {
            charge(work, 20, span)?;
            Ok(lp == rp
                && lo == ro
                && ls == rs
                && lc == rc
                && lr == rr
                && l_offset == r_offset
                && same_owner_application(la, ra, work)?)
        }
        (
            Some(PreparedOwnerCall::Acquire {
                application: la,
                first_nonnull: ln,
                condition_span: lc,
                outcome_spans: lo,
                readable_spans: lr,
                initialized_bytes: li,
            }),
            Some(PreparedOwnerCall::Acquire {
                application: ra,
                first_nonnull: rn,
                condition_span: rc,
                outcome_spans: ro,
                readable_spans: rr,
                initialized_bytes: ri,
            }),
        ) => {
            charge(work, 8, span)?;
            if ln != rn
                || lc != rc
                || lo != ro
                || lr != rr
                || li.is_some() != ri.is_some()
                || !same_owner_application(la, ra, work)?
            {
                return Ok(false);
            }
            match (li, ri) {
                (Some(left), Some(right)) => {
                    charge(work, right.extent.len().saturating_add(2), span)?;
                    Ok(left.span == right.span && left.extent == right.extent)
                }
                (None, None) => Ok(true),
                _ => Ok(false),
            }
        }
        (
            Some(PreparedOwnerCall::Teardown {
                application: la,
                current_operand: lp,
                consumes: ld,
                disposition_span: lc,
                block_span: lb,
                outcome_span: lo,
            }),
            Some(PreparedOwnerCall::Teardown {
                application: ra,
                current_operand: rp,
                consumes: rd,
                disposition_span: rc,
                block_span: rb,
                outcome_span: ro,
            }),
        ) => {
            charge(work, 5, span)?;
            Ok(lp == rp
                && ld == rd
                && lc == rc
                && lb == rb
                && lo == ro
                && same_owner_application(la, ra, work)?)
        }
        (
            Some(PreparedOwnerCall::StatusTeardown {
                application: la,
                current_operand: lp,
                output_span: ls,
                block_span: lb,
                outcomes: lo,
            }),
            Some(PreparedOwnerCall::StatusTeardown {
                application: ra,
                current_operand: rp,
                output_span: rs,
                block_span: rb,
                outcomes: ro,
            }),
        ) => {
            charge(work, 4, span)?;
            if lp != rp
                || ls != rs
                || lb != rb
                || lo.len() != ro.len()
                || !same_owner_application(la, ra, work)?
            {
                return Ok(false);
            }
            for (left, right) in lo.iter().zip(ro) {
                charge(work, right.predicates.len().saturating_add(6), span)?;
                if left.consumes != right.consumes
                    || left.readable != right.readable
                    || left.disposition_span != right.disposition_span
                    || left.readability_span != right.readability_span
                    || left.outcome_span != right.outcome_span
                    || left.predicates != right.predicates
                {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}

fn private_span_within(outer: Span, inner: Span) -> bool {
    outer.source() == inner.source()
        && outer.range().start() <= inner.range().start()
        && inner.range().end() <= outer.range().end()
}

fn private_scalar_representation(
    value: PreparedScalarRepresentation,
    span: Span,
) -> Result<(), ForeignContractError> {
    match value {
        PreparedScalarRepresentation::Signed(8 | 32 | 64)
        | PreparedScalarRepresentation::Unsigned(8 | 32 | 64)
        | PreparedScalarRepresentation::SizeT => Ok(()),
        _ => Err(failure(
            ForeignContractReason::UnsupportedRepresentation,
            span,
        )),
    }
}

fn private_scalar_value(
    value: PreparedScalarValue,
    representation: PreparedScalarRepresentation,
    span: Span,
) -> Result<(), ForeignContractError> {
    private_scalar_representation(representation, span)?;
    // Source preparation canonicalizes negative zero. Keep its exact normalized
    // identity rather than admitting two encodings of the same scalar.
    let admitted = !(value.negative && value.magnitude == 0)
        && match representation {
            PreparedScalarRepresentation::Signed(bits) => {
                let boundary = 1_u64 << (bits - 1);
                if value.negative {
                    value.magnitude <= boundary
                } else {
                    value.magnitude < boundary
                }
            }
            PreparedScalarRepresentation::Unsigned(bits) => {
                !value.negative && (bits == 64 || value.magnitude < (1_u64 << bits))
            }
            PreparedScalarRepresentation::SizeT => !value.negative,
        };
    if admitted {
        Ok(())
    } else {
        Err(failure(ForeignContractReason::ConstantRange, span))
    }
}

/// Rehydrates normalized scalar/owner ABI facts under the caller's meter.
/// This does not load source, create a manifest, resolve a name or install an
/// interpreter. Resolved binding and independent Core admission remain required.
pub(crate) fn restore_prepared_library(
    parts: PrivatePreparedLibraryParts,
    work: &mut TypeWorkBudget,
) -> Result<PreparedForeignLibrary, ForeignContractError> {
    let span = parts.span;
    let count = parts
        .representations
        .len()
        .checked_add(parts.constants.len())
        .and_then(|count| count.checked_add(parts.sentinels.len()))
        .and_then(|count| count.checked_add(parts.symbols.len()))
        .and_then(|count| count.checked_add(parts.owners.len()))
        .and_then(|count| count.checked_add(parts.accesses.len()))
        .ok_or_else(|| failure(ForeignContractReason::WorkExhausted, span))?;
    charge(
        work,
        count
            .checked_add(1)
            .ok_or_else(|| failure(ForeignContractReason::WorkExhausted, span))?,
        span,
    )?;
    let mut names: Vec<(&str, usize, Span)> = Vec::new();
    reserve(&mut names, count, span)?;
    for (name, member_index, member_span) in parts
        .representations
        .iter()
        .map(|value| (value.name.as_str(), value.member_index, value.span))
        .chain(
            parts
                .constants
                .iter()
                .map(|value| (value.name.as_str(), value.member_index, value.span)),
        )
        .chain(
            parts
                .sentinels
                .iter()
                .map(|value| (value.name.as_str(), value.member_index, value.span)),
        )
        .chain(
            parts
                .symbols
                .iter()
                .map(|value| (value.name.as_str(), value.member_index, value.span)),
        )
        .chain(
            parts
                .owners
                .iter()
                .map(|value| (value.name.as_str(), value.member_index, value.span)),
        )
        .chain(parts.accesses.iter().map(|value| {
            (
                value.name(),
                value.member_index(),
                value.origin().primary_span(),
            )
        }))
    {
        charge(work, 1, member_span)?;
        if name.is_empty() || !private_span_within(span, member_span) || member_index > count {
            return Err(failure(ForeignContractReason::DuplicateMember, member_span));
        }
        for (previous, previous_index, previous_span) in &names {
            charge(work, 2, member_span)?;
            let source_order = if *previous_index < member_index {
                previous_span.range().end() <= member_span.range().start()
            } else {
                member_span.range().end() <= previous_span.range().start()
            };
            if *previous_index == member_index
                || !source_order
                || names_equal(previous, name, member_span, work)?
            {
                return Err(failure(ForeignContractReason::DuplicateMember, member_span));
            }
        }
        names.push((name, member_index, member_span));
    }
    private_member_order(
        parts
            .representations
            .iter()
            .map(|value| (value.member_index, value.span)),
        work,
    )?;
    private_member_order(
        parts
            .constants
            .iter()
            .map(|value| (value.member_index, value.span)),
        work,
    )?;
    private_member_order(
        parts
            .owners
            .iter()
            .map(|value| (value.member_index, value.span)),
        work,
    )?;
    private_member_order(
        parts
            .symbols
            .iter()
            .map(|value| (value.member_index, value.span)),
        work,
    )?;
    private_member_order(
        parts
            .sentinels
            .iter()
            .map(|value| (value.member_index, value.span)),
        work,
    )?;
    private_member_order(
        parts
            .accesses
            .iter()
            .map(|value| (value.member_index(), value.origin().primary_span())),
        work,
    )?;
    access_image::validate_accesses(&parts, work)?;
    for representation in &parts.representations {
        charge(work, 1, representation.span)?;
        private_representation(representation.representation, representation.span)?;
    }
    for constant in &parts.constants {
        charge(
            work,
            parts
                .representations
                .len()
                .checked_add(1)
                .ok_or_else(|| failure(ForeignContractReason::WorkExhausted, constant.span))?,
            constant.span,
        )?;
        private_scalar_value(constant.value, constant.representation, constant.span)?;
        if !parts.representations.iter().any(|value| {
            value.representation == PreparedRepresentation::Scalar(constant.representation)
        }) {
            return Err(failure(ForeignContractReason::UnknownMember, constant.span));
        }
    }
    for sentinel in &parts.sentinels {
        charge(work, 1, sentinel.span)?;
        if parts
            .representations
            .get(sentinel.representation_index)
            .is_none_or(|value| {
                value.representation != PreparedRepresentation::FunctionAddressSentinel
            })
        {
            return Err(failure(ForeignContractReason::OperandRole, sentinel.span));
        }
    }
    for (owner_index, owner) in parts.owners.iter().enumerate() {
        charge(
            work,
            owner
                .parameters
                .len()
                .checked_add(parts.representations.len())
                .and_then(|count| count.checked_add(1))
                .ok_or_else(|| failure(ForeignContractReason::WorkExhausted, owner.span))?,
            owner.span,
        )?;
        if owner.owned_parameter >= owner.parameters.len()
            || !matches!(
                owner.parameters[owner.owned_parameter].kind,
                PrivatePreparedParameterKind::Type
            )
            || !parts.representations.iter().any(|value| {
                value.representation == PreparedRepresentation::Address(owner.representation)
            })
            || !private_span_within(owner.span, owner.representation_span)
            || !private_span_within(owner.span, owner.owned_span)
            || !private_span_within(owner.span, owner.teardown_span)
        {
            return Err(failure(ForeignContractReason::OperandRole, owner.span));
        }
        for (index, dependency) in owner.retains.iter().enumerate() {
            charge(work, index.saturating_add(1), owner.span)?;
            if *dependency == owner.owned_parameter
                || owner.parameters.get(*dependency).is_none_or(|parameter| {
                    !matches!(parameter.kind, PrivatePreparedParameterKind::Type)
                })
                || owner.retains[..index].contains(dependency)
            {
                return Err(failure(
                    ForeignContractReason::InvalidParameters,
                    owner.span,
                ));
            }
        }
        for (index, parameter) in owner.parameters.iter().enumerate() {
            charge(work, 1, parameter.span)?;
            if parameter.name.is_empty() || !private_span_within(owner.span, parameter.span) {
                return Err(failure(
                    ForeignContractReason::InvalidParameters,
                    parameter.span,
                ));
            }
            for previous in &owner.parameters[..index] {
                if names_equal(&previous.name, &parameter.name, parameter.span, work)? {
                    return Err(failure(
                        ForeignContractReason::InvalidParameters,
                        parameter.span,
                    ));
                }
            }
        }
        charge(work, parts.symbols.len(), owner.teardown_span)?;
        let teardown = parts
            .symbols
            .iter()
            .find(|symbol| symbol.member_index == owner.teardown_member);
        if !matches!(teardown.map(|symbol| &symbol.call),
            Some(PrivatePreparedCall::Owner(PreparedOwnerCall::Teardown { application, .. } | PreparedOwnerCall::StatusTeardown { application, .. })) if application.owner == owner_index)
        {
            return Err(failure(ForeignContractReason::OperandRole, owner.span));
        }
    }
    for symbol in &parts.symbols {
        charge(
            work,
            symbol
                .native_name
                .len()
                .checked_add(1)
                .ok_or_else(|| failure(ForeignContractReason::WorkExhausted, symbol.span))?,
            symbol.span,
        )?;
        if symbol.native_name.is_empty() || symbol.native_name.as_bytes().contains(&0) {
            return Err(failure(
                ForeignContractReason::InvalidNativeName,
                symbol.span,
            ));
        }
        charge(work, symbol.destruction_operands.len(), symbol.span)?;
        let mut previous_capture = None;
        for capture in &symbol.destruction_operands {
            charge(work, capture.source.len().saturating_add(1), capture.span)?;
            if !private_span_within(symbol.span, capture.span)
                || capture.source.is_empty()
                || previous_capture.is_some_and(|previous| previous >= capture.position)
            {
                return Err(failure(ForeignContractReason::SourcePosition, capture.span));
            }
            previous_capture = Some(capture.position);
        }
        charge(
            work,
            symbol
                .parameters
                .len()
                .checked_add(symbol.native_type_projection.len())
                .ok_or_else(|| failure(ForeignContractReason::WorkExhausted, symbol.span))?,
            symbol.span,
        )?;
        let mut type_index = 0;
        for (index, parameter) in symbol.parameters.iter().enumerate() {
            charge(work, 1, parameter.span)?;
            if parameter.name.is_empty() || !private_span_within(symbol.span, parameter.span) {
                return Err(failure(
                    ForeignContractReason::InvalidParameters,
                    parameter.span,
                ));
            }
            for previous in &symbol.parameters[..index] {
                if names_equal(&previous.name, &parameter.name, parameter.span, work)? {
                    return Err(failure(
                        ForeignContractReason::InvalidParameters,
                        parameter.span,
                    ));
                }
            }
            if matches!(parameter.kind, PrivatePreparedParameterKind::Type) {
                if symbol.native_type_projection.get(type_index) != Some(&index) {
                    return Err(failure(
                        ForeignContractReason::InvalidParameters,
                        parameter.span,
                    ));
                }
                type_index += 1;
            }
        }
        if type_index != symbol.native_type_projection.len() {
            return Err(failure(
                ForeignContractReason::InvalidParameters,
                symbol.span,
            ));
        }
        for (operand_index, operand) in symbol.operands.iter().enumerate() {
            charge(
                work,
                parts
                    .representations
                    .len()
                    .checked_add(1)
                    .ok_or_else(|| failure(ForeignContractReason::WorkExhausted, operand.span))?,
                operand.span,
            )?;
            private_representation(operand.representation, operand.span)?;
            if !private_span_within(symbol.span, operand.span)
                || !parts
                    .representations
                    .iter()
                    .any(|value| value.representation == operand.representation)
            {
                return Err(failure(ForeignContractReason::OperandRole, operand.span));
            }
            match &operand.source {
                PreparedOperandSource::Bytes { path, extent, .. } => {
                    charge(
                        work,
                        path.len().saturating_add(extent.len()).saturating_add(1),
                        operand.span,
                    )?;
                    if path.is_empty()
                        || extent.is_empty()
                        || operand.representation
                            != PreparedRepresentation::Address(PreparedAddressRepresentation::Bytes)
                        || !matches!(
                            symbol.call,
                            PrivatePreparedCall::Owner(PreparedOwnerCall::Borrow { .. })
                        )
                    {
                        return Err(failure(ForeignContractReason::OperandRole, operand.span));
                    }
                }
                PreparedOperandSource::Nul(path) => {
                    charge(work, path.len().saturating_add(1), operand.span)?;
                    if path.is_empty()
                        || operand.representation
                            != PreparedRepresentation::Address(PreparedAddressRepresentation::Bytes)
                        || !matches!(
                            symbol.call,
                            PrivatePreparedCall::Owner(PreparedOwnerCall::OutputAcquire { .. })
                        )
                    {
                        return Err(failure(ForeignContractReason::OperandRole, operand.span));
                    }
                }
                PreparedOperandSource::Null => {
                    if !matches!(operand.representation, PreparedRepresentation::Address(_))
                        || !matches!(
                            symbol.call,
                            PrivatePreparedCall::Owner(PreparedOwnerCall::OutputAcquire { .. })
                        )
                    {
                        return Err(failure(ForeignContractReason::OperandRole, operand.span));
                    }
                }
                PreparedOperandSource::OwnerOutput => {
                    if operand.representation
                        != PreparedRepresentation::Address(PreparedAddressRepresentation::Opaque)
                        || !matches!(symbol.call, PrivatePreparedCall::Owner(PreparedOwnerCall::OutputAcquire { output_operand, .. }) if output_operand == operand_index)
                    {
                        return Err(failure(ForeignContractReason::OutputRole, operand.span));
                    }
                }
                PreparedOperandSource::OffsetOutput => {
                    if operand.representation
                        != PreparedRepresentation::Address(PreparedAddressRepresentation::Bytes)
                        || !matches!(&symbol.call, PrivatePreparedCall::Owner(PreparedOwnerCall::OutputAcquire { offset: Some(offset), .. }) if offset.operand == operand_index)
                    {
                        return Err(failure(ForeignContractReason::OperandRole, operand.span));
                    }
                }
                PreparedOperandSource::Constant(index) => {
                    let constant = parts.constants.get(*index).ok_or_else(|| {
                        failure(ForeignContractReason::UnknownMember, operand.span)
                    })?;
                    if PreparedRepresentation::Scalar(constant.representation)
                        != operand.representation
                    {
                        return Err(failure(ForeignContractReason::OperandRole, operand.span));
                    }
                }
                PreparedOperandSource::Sentinel(index) => {
                    if parts.sentinels.get(*index).is_none()
                        || operand.representation != PreparedRepresentation::FunctionAddressSentinel
                    {
                        return Err(failure(ForeignContractReason::OperandRole, operand.span));
                    }
                }
                PreparedOperandSource::Enclosing(path) => {
                    charge(work, path.len().saturating_add(1), operand.span)?;
                    if path.is_empty()
                        || !matches!(operand.representation, PreparedRepresentation::Address(_))
                        || !matches!(symbol.call, PrivatePreparedCall::Owner(_))
                    {
                        return Err(failure(ForeignContractReason::OperandRole, operand.span));
                    }
                }
                PreparedOperandSource::Current(path) => {
                    charge(
                        work,
                        path.len().checked_add(1).ok_or_else(|| {
                            failure(ForeignContractReason::WorkExhausted, operand.span)
                        })?,
                        operand.span,
                    )?;
                    if path.is_empty()
                        || !matches!(operand.representation, PreparedRepresentation::Address(_))
                        || !matches!(
                            symbol.call,
                            PrivatePreparedCall::Owner(
                                PreparedOwnerCall::Teardown { .. }
                                    | PreparedOwnerCall::Borrow { .. }
                                    | PreparedOwnerCall::StatusTeardown { .. }
                            )
                        )
                    {
                        return Err(failure(ForeignContractReason::OperandRole, operand.span));
                    }
                }
                PreparedOperandSource::Source(path) => {
                    if !matches!(operand.representation, PreparedRepresentation::Scalar(_)) {
                        return Err(failure(ForeignContractReason::OperandRole, operand.span));
                    }
                    // The existing resolved binding pass checks each complete
                    // path against the retained source signature, including Int.
                    charge(
                        work,
                        path.len().checked_add(1).ok_or_else(|| {
                            failure(ForeignContractReason::WorkExhausted, operand.span)
                        })?,
                        operand.span,
                    )?;
                    if path.is_empty() {
                        return Err(failure(ForeignContractReason::SourcePosition, operand.span));
                    }
                }
            }
        }
        if let PreparedAbiResult::Scalar(representation) = symbol.result {
            charge(
                work,
                parts
                    .representations
                    .len()
                    .checked_add(1)
                    .ok_or_else(|| failure(ForeignContractReason::WorkExhausted, symbol.span))?,
                symbol.span,
            )?;
            private_scalar_representation(representation, symbol.span)?;
            if !parts
                .representations
                .iter()
                .any(|value| value.representation == PreparedRepresentation::Scalar(representation))
            {
                return Err(failure(ForeignContractReason::UnknownMember, symbol.span));
            }
        }
        access_image::validate_result(&parts, symbol, work)?;
        if let PrivatePreparedCall::Owner(owner_call) = &symbol.call {
            private_owner_call(&parts, symbol, owner_call, work)?;
            continue;
        }
        let outcomes = symbol.call.outcomes();
        if matches!(symbol.result, PreparedAbiResult::Address(_)) {
            return Err(failure(ForeignContractReason::OutputRole, symbol.span));
        }
        charge(work, outcomes.len(), symbol.span)?;
        let Some(last) = outcomes.last() else {
            return Err(failure(ForeignContractReason::OutcomeCoverage, symbol.span));
        };
        if !last.predicates.is_empty() {
            return Err(failure(ForeignContractReason::OutcomeCoverage, last.span));
        }
        for (index, outcome) in outcomes.iter().enumerate() {
            charge(
                work,
                outcome
                    .predicates
                    .len()
                    .checked_add(1)
                    .ok_or_else(|| failure(ForeignContractReason::WorkExhausted, outcome.span))?,
                outcome.span,
            )?;
            if !private_span_within(symbol.span, outcome.span)
                || (index + 1 != outcomes.len() && outcome.predicates.is_empty())
            {
                return Err(failure(
                    ForeignContractReason::OutcomeCoverage,
                    outcome.span,
                ));
            }
            for (position, predicate) in outcome.predicates.iter().enumerate() {
                let PreparedAbiResult::Scalar(representation) = symbol.result else {
                    return Err(failure(
                        ForeignContractReason::OutcomeCoverage,
                        outcome.span,
                    ));
                };
                if predicate.position != PreparedNativePosition::Result {
                    return Err(failure(
                        ForeignContractReason::OutcomeCoverage,
                        outcome.span,
                    ));
                }
                private_scalar_value(predicate.value, representation, outcome.span)?;
                charge(work, parts.constants.len(), outcome.span)?;
                if !parts.constants.iter().any(|constant| {
                    constant.representation == representation && constant.value == predicate.value
                }) {
                    return Err(failure(ForeignContractReason::UnknownMember, outcome.span));
                }
                charge(work, position, outcome.span)?;
                if outcome.predicates[..position]
                    .iter()
                    .any(|previous| previous.position == predicate.position)
                {
                    return Err(failure(
                        ForeignContractReason::OverlappingOutcomes,
                        outcome.span,
                    ));
                }
            }
            if !outcome.predicates.is_empty() {
                for previous in &outcomes[..index] {
                    let comparisons = previous
                        .predicates
                        .len()
                        .checked_mul(outcome.predicates.len())
                        .ok_or_else(|| {
                            failure(ForeignContractReason::WorkExhausted, outcome.span)
                        })?;
                    charge(work, comparisons, outcome.span)?;
                    if !previous.predicates.iter().any(|left| {
                        outcome.predicates.iter().any(|right| {
                            left.position == right.position && left.value != right.value
                        })
                    }) {
                        return Err(failure(
                            ForeignContractReason::OverlappingOutcomes,
                            outcome.span,
                        ));
                    }
                }
            }
        }
    }
    drop(names);
    // Conversion moves decoded strings/vectors; it performs no new byte copy.
    // Reserve every owned staging row before moving any of its records.
    let mut result = PreparedForeignLibrary {
        module: parts.module,
        name: parts.name,
        public: parts.public,
        representations: Vec::new(),
        constants: Vec::new(),
        sentinels: Vec::new(),
        owners: Vec::new(),
        accesses: parts.accesses,
        symbols: Vec::new(),
        origin: Origin::Source(span),
    };
    charge(work, count, span)?;
    reserve(
        &mut result.representations,
        parts.representations.len(),
        span,
    )?;
    reserve(&mut result.constants, parts.constants.len(), span)?;
    reserve(&mut result.sentinels, parts.sentinels.len(), span)?;
    reserve(&mut result.symbols, parts.symbols.len(), span)?;
    reserve(&mut result.owners, parts.owners.len(), span)?;
    for value in parts.representations {
        result.representations.push(PreparedForeignRepresentation {
            member_index: value.member_index,
            name: value.name,
            representation: value.representation,
            origin: Origin::Source(value.span),
        });
    }
    for value in parts.constants {
        result.constants.push(PreparedForeignConstant {
            member_index: value.member_index,
            name: value.name,
            representation: value.representation,
            value: value.value,
            origin: Origin::Source(value.span),
        });
    }
    for value in parts.sentinels {
        result.sentinels.push(PreparedForeignSentinel {
            member_index: value.member_index,
            name: value.name,
            representation_index: value.representation_index,
            origin: Origin::Source(value.span),
        });
    }
    for value in parts.owners {
        charge(work, value.parameters.len(), value.span)?;
        let mut parameters = Vec::new();
        reserve(&mut parameters, value.parameters.len(), value.span)?;
        for parameter in value.parameters {
            parameters.push(PreparedForeignParameter {
                name: parameter.name,
                kind: match parameter.kind {
                    PrivatePreparedParameterKind::Type => Kind::Type,
                    PrivatePreparedParameterKind::EffectRow => Kind::EffectRow,
                },
                origin: Origin::Source(parameter.span),
            });
        }
        result.owners.push(PreparedForeignOwner {
            member_index: value.member_index,
            name: value.name,
            parameters,
            owned_parameter: value.owned_parameter,
            retains: value.retains,
            representation: value.representation,
            teardown_member: value.teardown_member,
            representation_span: value.representation_span,
            owned_span: value.owned_span,
            teardown_span: value.teardown_span,
            origin: Origin::Source(value.span),
        });
    }
    for value in parts.symbols {
        let count = value
            .parameters
            .len()
            .checked_add(value.operands.len())
            .and_then(|count| count.checked_add(value.destruction_operands.len()))
            .and_then(|count| count.checked_add(value.call.outcomes().len()))
            .ok_or_else(|| failure(ForeignContractReason::WorkExhausted, value.span))?;
        charge(work, count, value.span)?;
        let mut parameters = Vec::new();
        let mut operands = Vec::new();
        let mut destruction_operands = Vec::new();
        let mut outcomes = Vec::new();
        reserve(&mut parameters, value.parameters.len(), value.span)?;
        reserve(&mut operands, value.operands.len(), value.span)?;
        reserve(
            &mut destruction_operands,
            value.destruction_operands.len(),
            value.span,
        )?;
        reserve(&mut outcomes, value.call.outcomes().len(), value.span)?;
        for parameter in value.parameters {
            parameters.push(PreparedForeignParameter {
                name: parameter.name,
                kind: match parameter.kind {
                    PrivatePreparedParameterKind::Type => Kind::Type,
                    PrivatePreparedParameterKind::EffectRow => Kind::EffectRow,
                },
                origin: Origin::Source(parameter.span),
            });
        }
        for operand in value.operands {
            operands.push(PreparedForeignOperand {
                representation: operand.representation,
                source: operand.source,
                origin: Origin::Source(operand.span),
            });
        }
        for capture in value.destruction_operands {
            destruction_operands.push(PreparedDestructionOperand {
                position: capture.position,
                source: capture.source,
                origin: Origin::Source(capture.span),
            });
        }
        let call = match value.call {
            PrivatePreparedCall::Scalar {
                outcomes: source_outcomes,
            } => {
                for outcome in source_outcomes {
                    outcomes.push(PreparedForeignOutcome {
                        predicates: outcome.predicates,
                        origin: Origin::Source(outcome.span),
                    });
                }
                PreparedForeignCall::Scalar { outcomes }
            }
            PrivatePreparedCall::Owner(call) => PreparedForeignCall::Owner(call),
        };
        result.symbols.push(PreparedForeignSymbol {
            member_index: value.member_index,
            name: value.name,
            native_name: value.native_name,
            parameters,
            native_type_projection: value.native_type_projection,
            operands,
            destruction_operands,
            result: value.result,
            call,
            access_result: value.access_result,
            origin: Origin::Source(value.span),
        });
    }
    validate_destruction_operands(&result, work)?;
    Ok(result)
}

// Generated bridge facts are untrusted construction data: compare the complete normalized
// library, not only the symbol's linker spelling or apparent C signature.
fn private_same_source_origin(
    origin: &Origin,
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<bool, ForeignContractError> {
    charge(work, 1, span)?;
    Ok(matches!(origin, Origin::Source(original) if *original == span))
}

pub(crate) fn same_prepared_library_parts(
    original: &PreparedForeignLibrary,
    candidate: &PrivatePreparedLibraryParts,
    work: &mut TypeWorkBudget,
) -> Result<bool, ForeignContractError> {
    let span = candidate.span;
    charge(work, 5, span)?;
    if !access_image::same_accesses(&original.accesses, &candidate.accesses, span, work)? {
        return Ok(false);
    }
    if !original.owners.is_empty() || !candidate.owners.is_empty() {
        charge(work, 1, span)?;
        if original.owners.len() != candidate.owners.len() {
            return Ok(false);
        }
    }
    if !original.sentinels.is_empty() || !candidate.sentinels.is_empty() {
        charge(work, 1, span)?;
        if original.sentinels.len() != candidate.sentinels.len() {
            return Ok(false);
        }
    }
    if original.module != candidate.module
        || original.public != candidate.public
        || original.representations.len() != candidate.representations.len()
        || original.constants.len() != candidate.constants.len()
        || original.symbols.len() != candidate.symbols.len()
        || !names_equal(&original.name, &candidate.name, span, work)?
        || !private_same_source_origin(&original.origin, span, work)?
    {
        return Ok(false);
    }
    for (left, right) in original
        .representations
        .iter()
        .zip(&candidate.representations)
    {
        charge(work, 2, right.span)?;
        if left.member_index != right.member_index
            || left.representation != right.representation
            || !names_equal(&left.name, &right.name, right.span, work)?
            || !private_same_source_origin(&left.origin, right.span, work)?
        {
            return Ok(false);
        }
    }
    for (left, right) in original.constants.iter().zip(&candidate.constants) {
        charge(work, 3, right.span)?;
        if left.member_index != right.member_index
            || left.representation != right.representation
            || left.value != right.value
            || !names_equal(&left.name, &right.name, right.span, work)?
            || !private_same_source_origin(&left.origin, right.span, work)?
        {
            return Ok(false);
        }
    }
    for (left, right) in original.sentinels.iter().zip(&candidate.sentinels) {
        charge(work, 2, right.span)?;
        if left.member_index != right.member_index
            || left.representation_index != right.representation_index
            || !names_equal(&left.name, &right.name, right.span, work)?
            || !private_same_source_origin(&left.origin, right.span, work)?
        {
            return Ok(false);
        }
    }
    for (left, right) in original.owners.iter().zip(&candidate.owners) {
        charge(work, right.retains.len().saturating_add(8), right.span)?;
        if left.retains != right.retains
            || left.member_index != right.member_index
            || left.owned_parameter != right.owned_parameter
            || left.representation_span != right.representation_span
            || left.owned_span != right.owned_span
            || left.teardown_span != right.teardown_span
            || left.teardown_member != right.teardown_member
            || left.representation != right.representation
            || left.parameters.len() != right.parameters.len()
            || !names_equal(&left.name, &right.name, right.span, work)?
            || !private_same_source_origin(&left.origin, right.span, work)?
        {
            return Ok(false);
        }
        for (left, right) in left.parameters.iter().zip(&right.parameters) {
            charge(work, 1, right.span)?;
            if !matches!(
                (&left.kind, right.kind),
                (Kind::Type, PrivatePreparedParameterKind::Type)
                    | (Kind::EffectRow, PrivatePreparedParameterKind::EffectRow)
            ) || !names_equal(&left.name, &right.name, right.span, work)?
                || !private_same_source_origin(&left.origin, right.span, work)?
            {
                return Ok(false);
            }
        }
    }
    for (left, right) in original.symbols.iter().zip(&candidate.symbols) {
        charge(work, 6, right.span)?;
        if left.member_index != right.member_index
            || left.result != right.result
            || left.parameters.len() != right.parameters.len()
            || left.native_type_projection.len() != right.native_type_projection.len()
            || left.operands.len() != right.operands.len()
            || left.destruction_operands.len() != right.destruction_operands.len()
            || left.outcomes().len() != right.call.outcomes().len()
            || !names_equal(&left.name, &right.name, right.span, work)?
            || !names_equal(&left.native_name, &right.native_name, right.span, work)?
            || !private_same_source_origin(&left.origin, right.span, work)?
        {
            return Ok(false);
        }
        if !access_image::same_result(
            left.access_result(),
            right.access_result.as_ref(),
            right.span,
            work,
        )? {
            return Ok(false);
        }
        if !same_owner_call(
            left.owner_call(),
            match &right.call {
                PrivatePreparedCall::Owner(call) => Some(call),
                _ => None,
            },
            right.span,
            work,
        )? {
            return Ok(false);
        }
        charge(work, right.native_type_projection.len(), right.span)?;
        if left.native_type_projection != right.native_type_projection {
            return Ok(false);
        }
        for (left, right) in left
            .destruction_operands
            .iter()
            .zip(&right.destruction_operands)
        {
            charge(
                work,
                left.source
                    .len()
                    .saturating_add(right.source.len())
                    .saturating_add(1),
                right.span,
            )?;
            if left.position != right.position
                || left.source != right.source
                || !private_same_source_origin(&left.origin, right.span, work)?
            {
                return Ok(false);
            }
        }
        for (left, right) in left.parameters.iter().zip(&right.parameters) {
            charge(work, 1, right.span)?;
            let kinds_match = matches!(
                (&left.kind, right.kind),
                (Kind::Type, PrivatePreparedParameterKind::Type)
                    | (Kind::EffectRow, PrivatePreparedParameterKind::EffectRow)
            );
            if !kinds_match
                || !names_equal(&left.name, &right.name, right.span, work)?
                || !private_same_source_origin(&left.origin, right.span, work)?
            {
                return Ok(false);
            }
        }
        for (left, right) in left.operands.iter().zip(&right.operands) {
            charge(work, 2, right.span)?;
            if left.representation != right.representation
                || !private_same_source_origin(&left.origin, right.span, work)?
            {
                return Ok(false);
            }
            let operand_span = right.span;
            let matches = match (&left.source, &right.source) {
                (
                    PreparedOperandSource::Bytes {
                        path: lp,
                        extent: le,
                        copy: lc,
                    },
                    PreparedOperandSource::Bytes {
                        path: rp,
                        extent: re,
                        copy: rc,
                    },
                ) => {
                    if lc != rc || lp.len() != rp.len() || le.len() != re.len() {
                        false
                    } else {
                        charge(work, lp.len().saturating_add(le.len()), operand_span)?;
                        lp == rp && le == re
                    }
                }
                (PreparedOperandSource::Sentinel(left), PreparedOperandSource::Sentinel(right))
                | (PreparedOperandSource::Constant(left), PreparedOperandSource::Constant(right)) => {
                    left == right
                }
                (PreparedOperandSource::Source(left), PreparedOperandSource::Source(right))
                | (PreparedOperandSource::Nul(left), PreparedOperandSource::Nul(right))
                | (PreparedOperandSource::Current(left), PreparedOperandSource::Current(right))
                | (
                    PreparedOperandSource::Enclosing(left),
                    PreparedOperandSource::Enclosing(right),
                ) => {
                    if left.len() != right.len() {
                        false
                    } else {
                        charge(work, left.len(), operand_span)?;
                        left == right
                    }
                }
                (PreparedOperandSource::Null, PreparedOperandSource::Null)
                | (PreparedOperandSource::OwnerOutput, PreparedOperandSource::OwnerOutput)
                | (PreparedOperandSource::OffsetOutput, PreparedOperandSource::OffsetOutput) => {
                    true
                }
                _ => false,
            };
            if !matches {
                return Ok(false);
            }
        }
        for (left, right) in left.outcomes().iter().zip(right.call.outcomes()) {
            charge(work, 1, right.span)?;
            if left.predicates.len() != right.predicates.len()
                || !private_same_source_origin(&left.origin, right.span, work)?
            {
                return Ok(false);
            }
            charge(work, right.predicates.len(), right.span)?;
            if left.predicates != right.predicates {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

#[cfg(test)]
mod owner_normalization_tests {
    use super::*;

    const OWNED_BYTES: &str = r#"foreign library Memory {
    profile "x86_64-unknown-linux-gnu"
    repr Size = size_t
    repr Address = bytes
    const One : Size = 1
    owner State<R> {
        representation Address
        owned R
        teardown Free
    }
    symbol Allocate<R> : Int -> Foreign.Call<Foreign.Output<Foreign.Nullable<State<R>>>> {
        name "calloc"
        abi (Size, Size) -> pointer(Address)
        operand 0 from 0 scalar
        operand 1 from constant One
        output result as owner(State<R>)
        outcome result nonnull { readable result, initialized_bytes result from 0 }
        outcome otherwise { readable result }
    }
    symbol Free<R> : State<R> -> Foreign.Call<Foreign.Disposition<Unit>> {
        name "free"
        abi (pointer(Address)) -> void
        operand 0 from 0 current
        outcome otherwise { consumed 0 }
        retained_dependents block
    }
}
"#;

    pub(super) fn source(text: &str) -> (ModuleId, crate::surface::SurfaceModule) {
        let source = crate::source::SourceFile::new("owner-normalization.ash", text).unwrap();
        let tree = crate::parser::parse(crate::lexer::lex(&source).unwrap());
        (
            ModuleId::from(source.id()),
            crate::parser::project_module(&source, &tree).unwrap(),
        )
    }

    fn destruction_capture_source() -> String {
        OWNED_BYTES
            .replace("Allocate<R> : Int ->", "Allocate<R> : (Int, (Int, Int)) ->")
            .replace("operand 1 from constant One", "operand 1 from constant One\n        destruction_operand 2 from 1.0 scalar\n        destruction_operand 0 from 1.1 scalar")
            .replace("Free<R> : State<R> ->", "Free<R> : (Int, State<R>, Int) ->")
            .replace("abi (pointer(Address)) -> void", "abi (Size, pointer(Address), Size) -> void")
            .replace("operand 0 from 0 current", "operand 0 from 2 scalar\n        operand 1 from 1 current\n        operand 2 from 0 scalar")
            .replace("consumed 0", "consumed 1")
    }

    #[test]
    fn destruction_capture_preparation_and_original_facts_keep_complete_paid_correspondence() {
        let text = destruction_capture_source();
        let (module, surface) = source(&text);
        let authored = &surface.foreign_libraries[0];
        let mut work = TypeWorkBudget::default();
        let prepared = prepare_foreign_library_with_budget(module, authored, &mut work).unwrap();
        let exact = work.used();
        let captures = prepared.symbols()[0].destruction_operands();
        assert_eq!(captures.len(), 2);
        assert_eq!(
            (captures[0].position(), captures[0].source()),
            (0, &[1, 1][..])
        );
        assert_eq!(
            (captures[1].position(), captures[1].source()),
            (2, &[1, 0][..])
        );
        for prefix in [0, 13] {
            let mut short = TypeWorkBudget::with_limit(prefix + exact - 1);
            short.charge(prefix).unwrap();
            assert_eq!(
                prepare_foreign_library_with_budget(module, authored, &mut short)
                    .unwrap_err()
                    .reason(),
                ForeignContractReason::WorkExhausted
            );
            for _ in 0..2 {
                let mut retry = TypeWorkBudget::with_limit(prefix + exact);
                retry.charge(prefix).unwrap();
                prepare_foreign_library_with_budget(module, authored, &mut retry).unwrap();
                assert_eq!(retry.used(), prefix + exact);
            }
        }
        let mut restore = TypeWorkBudget::default();
        restore_prepared_library(parts(&prepared), &mut restore).unwrap();
        let mut compare = TypeWorkBudget::default();
        assert!(same_prepared_library_parts(&prepared, &parts(&prepared), &mut compare).unwrap());
        for (is_restore, required) in [(true, restore.used()), (false, compare.used())] {
            for prefix in [0, 13] {
                let mut short = TypeWorkBudget::with_limit(prefix + required - 1);
                short.charge(prefix).unwrap();
                let reason = if is_restore {
                    restore_prepared_library(parts(&prepared), &mut short)
                        .unwrap_err()
                        .reason()
                } else {
                    same_prepared_library_parts(&prepared, &parts(&prepared), &mut short)
                        .unwrap_err()
                        .reason()
                };
                assert_eq!(reason, ForeignContractReason::WorkExhausted);
                let mut exact = TypeWorkBudget::with_limit(prefix + required);
                exact.charge(prefix).unwrap();
                if is_restore {
                    restore_prepared_library(parts(&prepared), &mut exact).unwrap();
                } else {
                    assert!(
                        same_prepared_library_parts(&prepared, &parts(&prepared), &mut exact)
                            .unwrap()
                    );
                }
                assert_eq!(exact.used(), prefix + required);
            }
        }
        for change in 0..5 {
            let mut forged = parts(&prepared);
            match change {
                0 => forged.symbols[0].destruction_operands[0].source = vec![1, 0],
                1 => forged.symbols[0].destruction_operands[0].position = 1,
                2 => {
                    forged.symbols[0].destruction_operands[0].span =
                        forged.symbols[0].destruction_operands[1].span
                }
                3 => forged.symbols[0].destruction_operands[0].source.clear(),
                _ => forged.symbols[0].destruction_operands[1].position = 0,
            }
            assert!(
                !same_prepared_library_parts(&prepared, &forged, &mut TypeWorkBudget::default())
                    .unwrap(),
                "original record mutation {change}"
            );
            if matches!(change, 1 | 3 | 4) {
                assert!(restore_prepared_library(forged, &mut TypeWorkBudget::default()).is_err());
            }
        }
        for (invalid, expected) in [
            (
                text.replace("        destruction_operand 2 from 1.0 scalar\n", ""),
                ForeignContractReason::OperandCoverage,
            ),
            (
                text.replace("destruction_operand 2 from", "destruction_operand 0 from"),
                ForeignContractReason::OperandCoverage,
            ),
            (
                text.replace(
                    "destruction_operand 0 from",
                    "destruction_operand result from",
                ),
                ForeignContractReason::OperandCoverage,
            ),
            (
                text.replace("destruction_operand 0 from", "destruction_operand 1 from"),
                ForeignContractReason::OperandCoverage,
            ),
            (
                text.replace("(Int, (Int, Int)) ->", "(Int, (Int, Bool)) ->"),
                ForeignContractReason::SourcePosition,
            ),
            (
                text.replace("operand 0 from 2 scalar", "operand 0 from 0 scalar"),
                ForeignContractReason::SourcePosition,
            ),
        ] {
            let (module, surface) = source(&invalid);
            assert_eq!(
                prepare_foreign_library_with_budget(
                    module,
                    &surface.foreign_libraries[0],
                    &mut TypeWorkBudget::default()
                )
                .unwrap_err()
                .reason(),
                expected
            );
        }
    }

    #[test]
    fn temporary_bytes_preserve_source_extent_discipline_and_exact_preparation_budget() {
        let symbol = r#"    symbol Hash<R> : (State<R>, Bytes, Int) -> Foreign.Call<Int> {
        name "hash_bytes"
        abi (pointer(Address), pointer(Address), Size) -> Size
        operand 0 from 0 current
        operand 1 from 1 bytes(2) copy
        operand 2 from 2 scalar
        output result as scalar
        outcome otherwise { readable result }
    }
"#;
        let text = OWNED_BYTES.replace("    symbol Free", &format!("{symbol}    symbol Free"));
        let (module, surface) = source(&text);
        let original = &surface.foreign_libraries[0];
        let mut measured = TypeWorkBudget::default();
        let prepared =
            prepare_foreign_library_with_budget(module, original, &mut measured).unwrap();
        assert!(matches!(&prepared.symbols()[1].operands()[1].source,
            PreparedOperandSource::Bytes { path, extent, copy: true } if path == &[1] && extent == &[2]));
        let required = measured.used();
        for prefix in [0, 11] {
            let mut short = TypeWorkBudget::with_limit(prefix + required - 1);
            short.charge(prefix).unwrap();
            assert!(
                prepare_foreign_library_with_budget(module, original, &mut short)
                    .unwrap_err()
                    .is_resource_exhaustion()
            );
            for _ in 0..2 {
                let mut exact = TypeWorkBudget::with_limit(prefix + required);
                exact.charge(prefix).unwrap();
                prepare_foreign_library_with_budget(module, original, &mut exact).unwrap();
                assert_eq!(exact.used(), prefix + required);
            }
        }
        let mut changed = parts(&prepared);
        let PreparedOperandSource::Bytes { copy, .. } = &mut changed.symbols[1].operands[1].source
        else {
            panic!("bytes role");
        };
        *copy = false;
        assert!(
            !same_prepared_library_parts(&prepared, &changed, &mut TypeWorkBudget::default())
                .unwrap()
        );
        restore_prepared_library(changed, &mut TypeWorkBudget::default()).unwrap();
        for text in [
            text.replace("bytes(2)", "bytes(1)"),
            text.replace("Bytes, Int)", "Bytes, Bool)"),
            text.replace("bytes(2) copy", "nul copy"),
        ] {
            let (module, surface) = source(&text);
            assert!(prepare_foreign_library(module, &surface.foreign_libraries[0]).is_err());
        }
        let string = text
            .replace("Bytes, Int)", "String, Int)")
            .replace("bytes(2) copy", "bytes(2) call_borrow");
        let (module, surface) = source(&string);
        let prepared = prepare_foreign_library(module, &surface.foreign_libraries[0]).unwrap();
        assert!(matches!(
            prepared.symbols()[1].operands()[1].source(),
            PreparedOperandSource::Bytes { copy: false, .. }
        ));
    }

    // Construction data is deliberately rebuilt from immutable prepared facts.
    // This test helper has no product authority and is never a manifest adapter.
    fn parameters(values: &[PreparedForeignParameter]) -> Vec<PrivatePreparedParameterParts> {
        values
            .iter()
            .map(|value| PrivatePreparedParameterParts {
                name: value.name.clone(),
                kind: match value.kind {
                    Kind::Type => PrivatePreparedParameterKind::Type,
                    Kind::EffectRow => PrivatePreparedParameterKind::EffectRow,
                    _ => panic!("unsupported prepared kind"),
                },
                span: value.origin.primary_span(),
            })
            .collect()
    }
    fn application(value: &PreparedOwnerApplication) -> PreparedOwnerApplication {
        PreparedOwnerApplication {
            owner: value.owner,
            arguments: value.arguments.clone(),
            span: value.span,
        }
    }
    fn call(value: &PreparedOwnerCall) -> PreparedOwnerCall {
        match value {
            PreparedOwnerCall::Borrow {
                application: value,
                current_operand,
                output_span,
                outcome_span,
                readable_span,
            } => PreparedOwnerCall::Borrow {
                application: application(value),
                current_operand: *current_operand,
                output_span: *output_span,
                outcome_span: *outcome_span,
                readable_span: *readable_span,
            },
            PreparedOwnerCall::OutputAcquire {
                application: value,
                output_operand,
                output_span,
                scalar_output_span,
                outcome_span,
                readable_spans,
                offset,
            } => PreparedOwnerCall::OutputAcquire {
                application: application(value),
                output_operand: *output_operand,
                output_span: *output_span,
                scalar_output_span: *scalar_output_span,
                outcome_span: *outcome_span,
                readable_spans: *readable_spans,
                offset: *offset,
            },
            PreparedOwnerCall::Acquire {
                application: value,
                first_nonnull,
                condition_span,
                outcome_spans,
                readable_spans,
                initialized_bytes,
            } => PreparedOwnerCall::Acquire {
                application: application(value),
                first_nonnull: *first_nonnull,
                condition_span: *condition_span,
                outcome_spans: *outcome_spans,
                readable_spans: *readable_spans,
                initialized_bytes: initialized_bytes.as_ref().map(|value| {
                    PreparedInitializedBytes {
                        extent: value.extent.clone(),
                        span: value.span,
                    }
                }),
            },
            PreparedOwnerCall::Teardown {
                application: value,
                current_operand,
                consumes,
                disposition_span,
                block_span,
                outcome_span,
            } => PreparedOwnerCall::Teardown {
                application: application(value),
                current_operand: *current_operand,
                consumes: *consumes,
                disposition_span: *disposition_span,
                block_span: *block_span,
                outcome_span: *outcome_span,
            },
            PreparedOwnerCall::StatusTeardown {
                application: value,
                current_operand,
                output_span,
                block_span,
                outcomes,
            } => PreparedOwnerCall::StatusTeardown {
                application: application(value),
                current_operand: *current_operand,
                output_span: *output_span,
                block_span: *block_span,
                outcomes: outcomes
                    .iter()
                    .map(|value| PreparedOwnerStatusOutcome {
                        predicates: value.predicates.clone(),
                        consumes: value.consumes,
                        readable: value.readable,
                        disposition_span: value.disposition_span,
                        readability_span: value.readability_span,
                        outcome_span: value.outcome_span,
                    })
                    .collect(),
            },
        }
    }
    pub(super) fn parts(value: &PreparedForeignLibrary) -> PrivatePreparedLibraryParts {
        PrivatePreparedLibraryParts {
            accesses: value
                .accesses
                .iter()
                .map(|access| PreparedForeignAccess {
                    member_index: access.member_index(),
                    name: access.name().to_owned(),
                    parameters: access
                        .parameters()
                        .iter()
                        .map(|parameter| PreparedForeignParameter {
                            name: parameter.name().to_owned(),
                            kind: parameter.kind().clone(),
                            origin: parameter.origin().clone(),
                        })
                        .collect(),
                    window_parameter: access.window_parameter(),
                    window_span: access.window_span(),
                    owner: application(access.owner()),
                    extent: access.extent(),
                    extent_span: access.extent_span(),
                    preserving_members: access.preserving_members().to_vec(),
                    origin: access.origin().clone(),
                })
                .collect(),
            module: value.module,
            name: value.name.clone(),
            public: value.public,
            span: value.origin.primary_span(),
            representations: value
                .representations
                .iter()
                .map(|value| PrivatePreparedRepresentationParts {
                    member_index: value.member_index,
                    name: value.name.clone(),
                    representation: value.representation,
                    span: value.origin.primary_span(),
                })
                .collect(),
            constants: value
                .constants
                .iter()
                .map(|value| PrivatePreparedConstantParts {
                    member_index: value.member_index,
                    name: value.name.clone(),
                    representation: value.representation,
                    value: value.value,
                    span: value.origin.primary_span(),
                })
                .collect(),
            sentinels: value
                .sentinels
                .iter()
                .map(|value| PrivatePreparedSentinelParts {
                    member_index: value.member_index,
                    name: value.name.clone(),
                    representation_index: value.representation_index,
                    span: value.origin.primary_span(),
                })
                .collect(),
            owners: value
                .owners
                .iter()
                .map(|value| PrivatePreparedOwnerParts {
                    member_index: value.member_index,
                    name: value.name.clone(),
                    parameters: parameters(&value.parameters),
                    owned_parameter: value.owned_parameter,
                    retains: value.retains.clone(),
                    representation: value.representation,
                    teardown_member: value.teardown_member,
                    representation_span: value.representation_span,
                    owned_span: value.owned_span,
                    teardown_span: value.teardown_span,
                    span: value.origin.primary_span(),
                })
                .collect(),
            symbols: value
                .symbols
                .iter()
                .map(|value| PrivatePreparedSymbolParts {
                    access_result: value.access_result().map(|result| {
                        let original = result.application();
                        let application = PreparedAccessApplication {
                            family: original.family(),
                            arguments: original.arguments().to_vec(),
                            span: original.span(),
                        };
                        match result {
                            PreparedAccessResult::View { keys, span, .. } => {
                                PreparedAccessResult::View {
                                    application,
                                    keys: keys.clone(),
                                    span: *span,
                                }
                            }
                            PreparedAccessResult::Extent {
                                view, keys, span, ..
                            } => PreparedAccessResult::Extent {
                                application,
                                view: view.clone(),
                                keys: keys.clone(),
                                span: *span,
                            },
                        }
                    }),
                    member_index: value.member_index,
                    name: value.name.clone(),
                    native_name: value.native_name.clone(),
                    parameters: parameters(&value.parameters),
                    native_type_projection: value.native_type_projection.clone(),
                    destruction_operands: value
                        .destruction_operands
                        .iter()
                        .map(|capture| PrivatePreparedDestructionOperandParts {
                            position: capture.position,
                            source: capture.source.clone(),
                            span: capture.origin.primary_span(),
                        })
                        .collect(),
                    result: value.result,
                    span: value.origin.primary_span(),
                    operands: value
                        .operands
                        .iter()
                        .map(|value| PrivatePreparedOperandParts {
                            representation: value.representation,
                            span: value.origin.primary_span(),
                            source: match &value.source {
                                PreparedOperandSource::Source(value) => {
                                    PreparedOperandSource::Source(value.clone())
                                }
                                PreparedOperandSource::Bytes { path, extent, copy } => {
                                    PreparedOperandSource::Bytes {
                                        path: path.clone(),
                                        extent: extent.clone(),
                                        copy: *copy,
                                    }
                                }
                                PreparedOperandSource::Nul(value) => {
                                    PreparedOperandSource::Nul(value.clone())
                                }
                                PreparedOperandSource::Null => PreparedOperandSource::Null,
                                PreparedOperandSource::OwnerOutput => {
                                    PreparedOperandSource::OwnerOutput
                                }
                                PreparedOperandSource::OffsetOutput => {
                                    PreparedOperandSource::OffsetOutput
                                }
                                PreparedOperandSource::Current(value) => {
                                    PreparedOperandSource::Current(value.clone())
                                }
                                PreparedOperandSource::Enclosing(value) => {
                                    PreparedOperandSource::Enclosing(value.clone())
                                }
                                PreparedOperandSource::Sentinel(value) => {
                                    PreparedOperandSource::Sentinel(*value)
                                }
                                PreparedOperandSource::Constant(value) => {
                                    PreparedOperandSource::Constant(*value)
                                }
                            },
                        })
                        .collect(),
                    call: match &value.call {
                        PreparedForeignCall::Owner(value) => {
                            PrivatePreparedCall::Owner(call(value))
                        }
                        PreparedForeignCall::Scalar { outcomes } => PrivatePreparedCall::Scalar {
                            outcomes: outcomes
                                .iter()
                                .map(|value| PrivatePreparedOutcomeParts {
                                    predicates: value.predicates.clone(),
                                    span: value.origin.primary_span(),
                                })
                                .collect(),
                        },
                    },
                })
                .collect(),
        }
    }

    fn status_owner_source() -> String {
        OWNED_BYTES.replace("    repr Size = size_t", "    repr Size = size_t\n    repr Status = signed(32)\n    const Held : Status = 7")
            .replace("Foreign.Disposition<Unit>", "Foreign.Disposition<Int>")
            .replace("abi (pointer(Address)) -> void", "abi (pointer(Address)) -> Status")
            .replace("outcome otherwise { consumed 0 }", "output result as scalar\n        outcome result == Held { readable result, retained 0 }\n        outcome otherwise { readable result, consumed 0 }")
    }

    #[test]
    fn status_owner_original_branches_restore_with_exact_budgets_and_reject_forged_outcomes() {
        let text = status_owner_source();
        let (module, surface) = source(&text);
        let authored = &surface.foreign_libraries[0];
        let mut measured = TypeWorkBudget::default();
        let original =
            prepare_foreign_library_with_budget(module, authored, &mut measured).unwrap();
        let exact = measured.used();
        let mut restore_work = TypeWorkBudget::default();
        restore_prepared_library(parts(&original), &mut restore_work).unwrap();
        let restore_exact = restore_work.used();
        for _ in 0..2 {
            for prefix in [0, 19] {
                let mut work = TypeWorkBudget::with_limit(prefix + exact);
                work.charge(prefix).unwrap();
                prepare_foreign_library_with_budget(module, authored, &mut work).unwrap();
                assert_eq!(work.used(), prefix + exact);
                let mut short = TypeWorkBudget::with_limit(prefix + exact - 1);
                short.charge(prefix).unwrap();
                assert_eq!(
                    prepare_foreign_library_with_budget(module, authored, &mut short)
                        .unwrap_err()
                        .reason(),
                    ForeignContractReason::WorkExhausted
                );
                assert!(short.used() < prefix + exact);
                let mut work = TypeWorkBudget::with_limit(prefix + restore_exact);
                work.charge(prefix).unwrap();
                restore_prepared_library(parts(&original), &mut work).unwrap();
                assert_eq!(work.used(), prefix + restore_exact);
                let mut short = TypeWorkBudget::with_limit(prefix + restore_exact - 1);
                short.charge(prefix).unwrap();
                assert_eq!(
                    restore_prepared_library(parts(&original), &mut short)
                        .unwrap_err()
                        .reason(),
                    ForeignContractReason::WorkExhausted
                );
            }
        }
        for field in 0..5 {
            let mut forged = parts(&original);
            let PrivatePreparedCall::Owner(PreparedOwnerCall::StatusTeardown {
                application,
                outcomes,
                ..
            }) = &mut forged.symbols[1].call
            else {
                panic!("status call");
            };
            match field {
                0 => outcomes[0].consumes = !outcomes[0].consumes,
                1 => outcomes[0].readable = !outcomes[0].readable,
                2 => outcomes[0].predicates[0].value.magnitude += 1,
                3 => application.arguments[0] = PreparedOwnerArgument::Type(99),
                4 => outcomes.swap(0, 1),
                _ => unreachable!(),
            }
            assert!(
                !same_prepared_library_parts(&original, &forged, &mut TypeWorkBudget::default())
                    .unwrap()
            );
            if field >= 1 {
                assert!(restore_prepared_library(forged, &mut TypeWorkBudget::default()).is_err());
            }
        }
    }

    #[test]
    fn status_owner_outcomes_require_total_unambiguous_original_result_facts() {
        let text = status_owner_source();
        for malformed in [
            text.replace("        outcome otherwise { readable result, consumed 0 }\n", ""),
            text.replace("outcome otherwise { readable result, consumed 0 }", "outcome result == Held { readable result, consumed 0 }\n        outcome otherwise { readable result, consumed 0 }"),
            text.replace("readable result, retained 0", "unreadable result, retained 0"),
            text.replace("readable result, consumed 0", "unreadable result, consumed 0"),
            text.replace("readable result, retained 0", "retained 0"),
            text.replace("retained 0", "retained 1"),
            text.replace("result == Held", "result == One"),
        ] {
            let (module, surface) = source(&malformed);
            assert!(prepare_foreign_library_with_budget(module, &surface.foreign_libraries[0], &mut TypeWorkBudget::default()).is_err());
        }
    }

    #[test]
    fn owner_source_preparation_restore_and_correspondence_are_bounded_and_do_not_resolve_identity()
    {
        let (module, surface) = source(OWNED_BYTES);
        let authored = &surface.foreign_libraries[0];
        let mut measured = TypeWorkBudget::default();
        let prepared =
            prepare_foreign_library_with_budget(module, authored, &mut measured).unwrap();
        assert_eq!(prepared.owners()[0].member_index(), 4);
        assert_eq!(prepared.owners()[0].teardown_member(), 6);
        assert_eq!(prepared.symbols()[0].member_index(), 5);
        assert!(
            matches!(prepared.symbols()[0].owner_call(), Some(PreparedOwnerCall::Acquire { initialized_bytes: Some(initialized), first_nonnull: true, .. }) if initialized.extent() == [0])
        );
        assert!(matches!(
            prepared.symbols()[1].owner_call(),
            Some(PreparedOwnerCall::Teardown {
                current_operand: 0,
                ..
            })
        ));
        let mixed = OWNED_BYTES
            .replace(
                "owner State<R>",
                "owner State<Before : EffectRow, R, After : EffectRow, T>",
            )
            .replace(
                "Allocate<R>",
                "Allocate<Before : EffectRow, R, After : EffectRow, T>",
            )
            .replace(
                "Free<R>",
                "Free<Before : EffectRow, R, After : EffectRow, T>",
            )
            .replace("State<R>", "State<{| Before}, R, {| After}, T>");
        let (mixed_module, mixed_surface) = source(&mixed);
        let mixed_prepared = prepare_foreign_library_with_budget(
            mixed_module,
            &mixed_surface.foreign_libraries[0],
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        assert_eq!(mixed_prepared.owners()[0].owned_parameter(), 1);
        assert_eq!(
            mixed_prepared.symbols()[0].native_type_projection(),
            &[1, 3]
        );
        assert!(
            matches!(mixed_prepared.symbols()[0].owner_call(), Some(PreparedOwnerCall::Acquire { application, .. }) if application.arguments() == [PreparedOwnerArgument::EffectRow(0), PreparedOwnerArgument::Type(1), PreparedOwnerArgument::EffectRow(2), PreparedOwnerArgument::Type(3)])
        );
        let exact = measured.used();
        for limit in [0, exact / 2, exact - 1] {
            assert_eq!(
                prepare_foreign_library_with_budget(
                    module,
                    authored,
                    &mut TypeWorkBudget::with_limit(limit)
                )
                .unwrap_err()
                .reason(),
                ForeignContractReason::WorkExhausted
            );
        }
        assert!(
            prepare_foreign_library_with_budget(
                module,
                authored,
                &mut TypeWorkBudget::with_limit(exact)
            )
            .is_ok()
        );
        let mut restore_work = TypeWorkBudget::default();
        let restored = restore_prepared_library(parts(&prepared), &mut restore_work).unwrap();
        let restore_exact = restore_work.used();
        for limit in [0, restore_exact / 2, restore_exact - 1] {
            assert_eq!(
                restore_prepared_library(parts(&prepared), &mut TypeWorkBudget::with_limit(limit))
                    .unwrap_err()
                    .reason(),
                ForeignContractReason::WorkExhausted
            );
        }
        assert!(
            restore_prepared_library(
                parts(&prepared),
                &mut TypeWorkBudget::with_limit(restore_exact)
            )
            .is_ok()
        );
        assert!(
            same_prepared_library_parts(
                &restored,
                &parts(&prepared),
                &mut TypeWorkBudget::default()
            )
            .unwrap()
        );
        let prefix = 23;
        let mut cumulative = TypeWorkBudget::with_limit(prefix + exact);
        cumulative.charge(prefix).unwrap();
        prepare_foreign_library_with_budget(module, authored, &mut cumulative).unwrap();
        assert_eq!(cumulative.used(), prefix + exact);
        let mut cumulative = TypeWorkBudget::with_limit(prefix + restore_exact);
        cumulative.charge(prefix).unwrap();
        restore_prepared_library(parts(&prepared), &mut cumulative).unwrap();
        assert_eq!(cumulative.used(), prefix + restore_exact);
        let mut correspondence = TypeWorkBudget::default();
        assert!(
            same_prepared_library_parts(&prepared, &parts(&prepared), &mut correspondence).unwrap()
        );
        let correspondence_exact = correspondence.used();
        for limit in [0, correspondence_exact / 2, correspondence_exact - 1] {
            let mut cumulative = TypeWorkBudget::with_limit(prefix + limit);
            cumulative.charge(prefix).unwrap();
            assert_eq!(
                same_prepared_library_parts(&prepared, &parts(&prepared), &mut cumulative)
                    .unwrap_err()
                    .reason(),
                ForeignContractReason::WorkExhausted
            );
            assert!(cumulative.used() >= prefix);
        }
        let mut cumulative = TypeWorkBudget::with_limit(prefix + correspondence_exact);
        cumulative.charge(prefix).unwrap();
        assert!(
            same_prepared_library_parts(&prepared, &parts(&prepared), &mut cumulative).unwrap()
        );
        assert_eq!(cumulative.used(), prefix + correspondence_exact);
        let mut changed = parts(&prepared);
        changed.owners[0].teardown_member = prepared.symbols[0].member_index;
        assert!(
            !same_prepared_library_parts(&prepared, &changed, &mut TypeWorkBudget::default())
                .unwrap()
        );
        assert_eq!(
            restore_prepared_library(changed, &mut TypeWorkBudget::default())
                .unwrap_err()
                .reason(),
            ForeignContractReason::OperandRole
        );
        let mut changed = parts(&prepared);
        let PrivatePreparedCall::Owner(PreparedOwnerCall::Acquire {
            initialized_bytes: Some(initialized),
            ..
        }) = &mut changed.symbols[0].call
        else {
            panic!("acquire");
        };
        initialized.extent[0] = 1;
        // Restoration has no resolved source signature. Correspondence must
        // still reject replacement of the originally checked integer path.
        assert!(
            !same_prepared_library_parts(&prepared, &changed, &mut TypeWorkBudget::default())
                .unwrap()
        );
    }

    #[test]
    fn incomplete_initialization_self_dependency_and_invalid_teardown_refuse() {
        for text in [
            OWNED_BYTES.replace(", initialized_bytes result from 0", ""),
            OWNED_BYTES.replace("owned R", "owned R\n        retains R"),
            OWNED_BYTES.replace("        retained_dependents block\n", ""),
            OWNED_BYTES.replace("-> pointer(Address)", "-> Address"),
            OWNED_BYTES.replace(
                "initialized_bytes result from 0",
                "initialized_bytes result from 1",
            ),
        ] {
            let (module, surface) = source(&text);
            assert!(
                prepare_foreign_library_with_budget(
                    module,
                    &surface.foreign_libraries[0],
                    &mut TypeWorkBudget::default()
                )
                .is_err()
            );
        }
    }

    #[test]
    fn unconditional_retained_teardown_prepares_and_restores_passive_disposition() {
        let text = OWNED_BYTES.replace("consumed 0", "retained 0");
        let (module, surface) = source(&text);
        let prepared = prepare_foreign_library_with_budget(
            module,
            &surface.foreign_libraries[0],
            &mut TypeWorkBudget::default(),
        )
        .unwrap();
        let retained = |library: &PreparedForeignLibrary| {
            assert!(matches!(
                library.symbols()[1].call(),
                PreparedForeignCall::Owner(PreparedOwnerCall::Teardown {
                    consumes: false,
                    ..
                })
            ));
        };
        retained(&prepared);
        let restored =
            restore_prepared_library(parts(&prepared), &mut TypeWorkBudget::default()).unwrap();
        retained(&restored);
        // Preparation and restoration retain the promised disposition; they
        // do not supply an executable callback or witnessed native retention.
        assert!(
            same_prepared_library_parts(
                &prepared,
                &parts(&restored),
                &mut TypeWorkBudget::default()
            )
            .unwrap()
        );
    }
    #[test]
    fn opaque_acquisition_requires_no_byte_extent_and_restores_without_authority() {
        let text = OWNED_BYTES
            .replace("repr Address = bytes", "repr Address = opaque")
            .replace(", initialized_bytes result from 0", "");
        let (module, surface) = source(&text);
        let prepared = prepare_foreign_library(module, &surface.foreign_libraries[0]).unwrap();
        assert!(matches!(
            prepared.symbols()[0].call(),
            PreparedForeignCall::Owner(PreparedOwnerCall::Acquire {
                initialized_bytes: None,
                ..
            })
        ));
        assert!(restore_prepared_library(parts(&prepared), &mut TypeWorkBudget::default()).is_ok());
    }

    #[test]
    fn restore_rejects_wrong_phase_coordinate_argument_tag_and_missing_extent() {
        let (module, surface) = source(OWNED_BYTES);
        let prepared = prepare_foreign_library(module, &surface.foreign_libraries[0]).unwrap();
        let mut wrong_phase = parts(&prepared);
        wrong_phase.symbols[0].call = PrivatePreparedCall::Scalar {
            outcomes: Vec::new(),
        };
        assert!(restore_prepared_library(wrong_phase, &mut TypeWorkBudget::default()).is_err());
        let mut duplicate = parts(&prepared);
        duplicate.symbols[0].member_index = duplicate.owners[0].member_index;
        assert!(restore_prepared_library(duplicate, &mut TypeWorkBudget::default()).is_err());
        let mut wrong_tag = parts(&prepared);
        let PrivatePreparedCall::Owner(PreparedOwnerCall::Acquire { application, .. }) =
            &mut wrong_tag.symbols[0].call
        else {
            panic!("acquire")
        };
        application.arguments[0] = PreparedOwnerArgument::EffectRow(0);
        assert!(restore_prepared_library(wrong_tag, &mut TypeWorkBudget::default()).is_err());
        let mut no_extent = parts(&prepared);
        let PrivatePreparedCall::Owner(PreparedOwnerCall::Acquire {
            initialized_bytes, ..
        }) = &mut no_extent.symbols[0].call
        else {
            panic!("acquire")
        };
        *initialized_bytes = None;
        assert!(restore_prepared_library(no_extent, &mut TypeWorkBudget::default()).is_err());
    }

    const SENTINELS: &str = r#"foreign library Sentinels {
    profile "x86_64-unknown-linux-gnu"
    repr I32 = signed(32)
    repr Destructor = function_address
    repr OtherDestructor = function_address
    sentinel Transient : Destructor = all_bits_one
    sentinel SameBits : Destructor = all_bits_one
    sentinel OtherRole : OtherDestructor = all_bits_one
    symbol Check<Before : EffectRow, T, After : EffectRow> : Unit -> Foreign.Call<Int> {
        name "ash_counter_noncallable_sentinel"
        abi (Destructor) -> I32
        operand 0 from constant Transient
        output result as scalar
        outcome otherwise { readable result }
    }
}
"#;

    #[test]
    fn sentinel_original_tables_have_exact_short_prefix_retry_and_donor_correspondence() {
        let (module, surface) = source(SENTINELS);
        let authored = &surface.foreign_libraries[0];
        let mut measured = TypeWorkBudget::default();
        let original =
            prepare_foreign_library_with_budget(module, authored, &mut measured).unwrap();
        assert!(original.constants().is_empty());
        assert_eq!(original.sentinels().len(), 3);
        let prepare_work = measured.used();
        let mut restored_work = TypeWorkBudget::default();
        restore_prepared_library(parts(&original), &mut restored_work).unwrap();
        let restore_work = restored_work.used();
        let mut correspondence = TypeWorkBudget::default();
        assert!(
            same_prepared_library_parts(&original, &parts(&original), &mut correspondence).unwrap()
        );
        for prefix in [0, 13] {
            for (operation, exact) in [
                (0, prepare_work),
                (1, restore_work),
                (2, correspondence.used()),
            ] {
                let mut short = TypeWorkBudget::with_limit(prefix + exact - 1);
                short.charge(prefix).unwrap();
                let error = match operation {
                    0 => prepare_foreign_library_with_budget(module, authored, &mut short)
                        .unwrap_err(),
                    1 => restore_prepared_library(parts(&original), &mut short).unwrap_err(),
                    _ => same_prepared_library_parts(&original, &parts(&original), &mut short)
                        .unwrap_err(),
                };
                assert_eq!(error.reason(), ForeignContractReason::WorkExhausted);
                assert!(short.used() >= prefix && short.used() < prefix + exact);
                let refused_usage = short.used();
                // The failing charge was atomic, with no ledger overshoot.
                assert!(refused_usage < prefix + exact);
                for _ in 0..2 {
                    let mut work = TypeWorkBudget::with_limit(prefix + exact);
                    work.charge(prefix).unwrap();
                    match operation {
                        0 => {
                            prepare_foreign_library_with_budget(module, authored, &mut work)
                                .unwrap();
                        }
                        1 => {
                            restore_prepared_library(parts(&original), &mut work).unwrap();
                        }
                        _ => {
                            assert!(
                                same_prepared_library_parts(
                                    &original,
                                    &parts(&original),
                                    &mut work
                                )
                                .unwrap()
                            );
                        }
                    }
                    assert_eq!(work.used(), prefix + exact);
                }
            }
        }
        for mutation in 0..5 {
            let mut changed = parts(&original);
            match mutation {
                0 => changed.symbols[0].operands[0].source = PreparedOperandSource::Sentinel(1), // same bits, distinct original member
                1 => {
                    changed.sentinels[0].representation_index =
                        changed.sentinels[2].representation_index
                }
                2 => changed.symbols[0].operands[0].source = PreparedOperandSource::Constant(0),
                3 => {
                    changed.symbols[0].operands[0].representation =
                        PreparedRepresentation::Address(PreparedAddressRepresentation::Opaque)
                }
                _ => changed.sentinels[0].member_index = changed.sentinels[1].member_index,
            }
            assert!(
                !same_prepared_library_parts(&original, &changed, &mut TypeWorkBudget::default())
                    .unwrap()
            );
            if mutation >= 2 {
                assert!(restore_prepared_library(changed, &mut TypeWorkBudget::default()).is_err());
            }
        }
    }

    #[test]
    fn sentinel_role_rejects_scalar_null_source_pointer_result_and_wrong_representation() {
        for text in [
            SENTINELS.replace("from constant Transient", "from constant OtherRole"),
            SENTINELS.replace("from constant Transient", "from null"),
            SENTINELS.replace("from constant Transient", "from 0 scalar"),
            SENTINELS.replace(
                "abi (Destructor) -> I32",
                "abi (pointer(Destructor)) -> I32",
            ),
            SENTINELS.replace("abi (Destructor) -> I32", "abi (Destructor) -> Destructor"),
            SENTINELS.replace(
                "sentinel Transient : Destructor",
                "sentinel Transient : I32",
            ),
            SENTINELS.replace(
                "sentinel Transient : Destructor = all_bits_one",
                "const Transient : Destructor = -1",
            ),
        ] {
            let (module, surface) = source(&text);
            assert!(
                prepare_foreign_library(module, &surface.foreign_libraries[0]).is_err(),
                "{text}"
            );
        }
    }
}
