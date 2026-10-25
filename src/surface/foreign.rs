//! Passive source declarations for signature-directed pointer calls.
use super::{SurfaceName, SurfaceType};
use crate::source::Span;
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignLibrary {
    pub public: bool,
    pub name: SurfaceName,
    pub members: Vec<SurfaceForeignMember>,
    pub span: Span,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SurfaceForeignMember {
    Profile(SurfaceForeignProfile),
    Symbol(Box<SurfaceForeignSymbol>),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignString {
    pub value: String,
    pub span: Span,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignProfile {
    pub target: SurfaceForeignString,
    pub span: Span,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SurfaceForeignSymbol {
    pub name: SurfaceName,
    pub ty: SurfaceType,
    pub native_name: SurfaceForeignString,
    pub span: Span,
}
