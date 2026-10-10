//! Source-spanned foreign contracts before identity resolution or admission.

use super::{SurfaceName, SurfaceType, SurfaceTypeParameter};
use crate::{integer::Integer, source::Span};

/// One passive native-library declaration inside an ordinary source module.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignLibrary {
    pub public: bool,
    pub name: SurfaceName,
    pub members: Vec<SurfaceForeignMember>,
    pub span: Span,
}

/// A foreign member in defining source order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceForeignMember {
    Profile(SurfaceForeignProfile),
    Representation(SurfaceForeignRepresentationDeclaration),
    Constant(SurfaceForeignConstant),
    Sentinel(SurfaceForeignSentinel),
    Owner(Box<SurfaceForeignOwner>),
    Access(Box<SurfaceForeignAccess>),
    Symbol(Box<SurfaceForeignSymbol>),
}

/// A literal's decoded value and complete source spelling.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignString {
    pub value: String,
    pub span: Span,
}

/// Sign and arbitrary-precision magnitude; admission checks positional ranges.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignInteger {
    pub negative: bool,
    pub magnitude: Integer,
    pub span: Span,
}

/// A defining member, optionally selected through one module alias.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignReference {
    pub module: Option<SurfaceName>,
    pub name: SurfaceName,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignProfile {
    pub target: SurfaceForeignString,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignRepresentationDeclaration {
    pub name: SurfaceName,
    pub representation: SurfaceForeignRepresentation,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceForeignRepresentation {
    Signed(SurfaceForeignInteger),
    Unsigned(SurfaceForeignInteger),
    SizeT(Span),
    Opaque(Span),
    Bytes(Span),
    FunctionAddress(Span),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignConstant {
    pub name: SurfaceName,
    pub representation: SurfaceForeignReference,
    pub value: SurfaceForeignInteger,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignSentinel {
    pub name: SurfaceName,
    pub representation: SurfaceForeignReference,
    pub bits: Span,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignOwner {
    pub name: SurfaceName,
    pub parameters: Vec<SurfaceTypeParameter>,
    pub representation: SurfaceForeignReference,
    pub owned: SurfaceName,
    pub retains: Vec<SurfaceName>,
    pub teardown: SurfaceForeignReference,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignAccess {
    pub name: SurfaceName,
    pub parameters: Vec<SurfaceTypeParameter>,
    pub window: SurfaceName,
    pub owner: SurfaceType,
    pub extent: SurfaceForeignExtent,
    pub preserves: Vec<SurfaceForeignReference>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SurfaceForeignExtent {
    Bytes(Span),
    Nul(Span),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignSymbol {
    pub name: SurfaceName,
    pub parameters: Vec<SurfaceTypeParameter>,
    pub ty: SurfaceType,
    pub native_name: SurfaceForeignString,
    pub abi_operands: Vec<SurfaceForeignAbiOperand>,
    pub abi_result: SurfaceForeignAbiRepresentation,
    pub contracts: Vec<SurfaceForeignContract>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignAbiOperand {
    pub output: bool,
    pub representation: SurfaceForeignAbiRepresentation,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceForeignAbiRepresentation {
    Member(SurfaceForeignReference),
    Void(Span),
    Pointer {
        representation: SurfaceForeignReference,
        span: Span,
    },
}

/// A dotted zero-based path retained without host narrowing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignSourcePosition {
    pub components: Vec<SurfaceForeignInteger>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceForeignNativePosition {
    Argument(SurfaceForeignInteger),
    Result(Span),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceForeignContract {
    Operand {
        position: SurfaceForeignNativePosition,
        source: SurfaceForeignOperandSource,
        span: Span,
    },
    Output {
        position: SurfaceForeignNativePosition,
        role: SurfaceForeignOutputRole,
        span: Span,
    },
    Outcome {
        test: SurfaceForeignOutcomeTest,
        facts: Vec<SurfaceForeignOutcomeFact>,
        span: Span,
    },
    RetainedDependentsBlock {
        span: Span,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceForeignOperandSource {
    Source {
        position: SurfaceForeignSourcePosition,
        role: SurfaceForeignOperandRole,
    },
    Constant(SurfaceForeignReference),
    Null(Span),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignOperandRole {
    pub kind: SurfaceForeignOperandRoleKind,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceForeignOperandRoleKind {
    Scalar,
    Current,
    Enclosing,
    View,
    Bytes {
        extent: SurfaceForeignSourcePosition,
        discipline: SurfaceForeignInputDiscipline,
    },
    Nul(SurfaceForeignInputDiscipline),
    Sentinel,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SurfaceForeignInputDiscipline {
    CallBorrow(Span),
    Copy(Span),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignOutputRole {
    pub kind: SurfaceForeignOutputRoleKind,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceForeignOutputRoleKind {
    Scalar,
    Owner(SurfaceType),
    View {
        ty: SurfaceType,
        keys: Vec<SurfaceForeignSourcePosition>,
    },
    ExtentOf {
        view: SurfaceForeignSourcePosition,
        keys: Vec<SurfaceForeignSourcePosition>,
    },
    OffsetInto(SurfaceForeignSourcePosition),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceForeignOutcomeTest {
    Otherwise(Span),
    All(Vec<SurfaceForeignOutcomeAtom>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignOutcomeAtom {
    pub position: SurfaceForeignNativePosition,
    pub condition: SurfaceForeignOutcomeCondition,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceForeignOutcomeCondition {
    Equal(SurfaceForeignReference),
    Null(Span),
    NonNull(Span),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignOutcomeFact {
    pub kind: SurfaceForeignOutcomeFactKind,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceForeignOutcomeFactKind {
    Readable(SurfaceForeignNativePosition),
    Unreadable(SurfaceForeignNativePosition),
    Consumed(SurfaceForeignSourcePosition),
    Retained(SurfaceForeignSourcePosition),
    InitializedBytes {
        position: SurfaceForeignNativePosition,
        extent: SurfaceForeignSourcePosition,
    },
}
