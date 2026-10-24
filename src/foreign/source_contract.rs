//! Passive source declarations for byte/address native calls.
use crate::{
    module::ModuleId,
    source::{Origin, Span},
    surface::{SurfaceForeignLibrary, SurfaceForeignMember},
    types::TypeWorkBudget,
};
use std::{error::Error, fmt};

pub(crate) const PROFILE: &str = "x86_64-unknown-linux-gnu";

/// A source declaration rejected before native linking or entry.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ForeignContractError {
    span: Span,
    message: &'static str,
    resource: bool,
}
impl ForeignContractError {
    pub(crate) const fn new(span: Span, message: &'static str) -> Self {
        Self {
            span,
            message,
            resource: false,
        }
    }
    pub const fn span(self) -> Span {
        self.span
    }
    pub const fn is_resource_exhaustion(self) -> bool {
        self.resource
    }
}
impl fmt::Display for ForeignContractError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.message)
    }
}
impl Error for ForeignContractError {}
fn paid(work: &mut TypeWorkBudget, n: usize, span: Span) -> Result<(), ForeignContractError> {
    work.charge(n).map_err(|()| ForeignContractError {
        span,
        message: "foreign declaration work exhausted",
        resource: true,
    })
}
fn text(
    value: &str,
    span: Span,
    work: &mut TypeWorkBudget,
) -> Result<String, ForeignContractError> {
    paid(work, value.len(), span)?;
    let mut copy = String::new();
    copy.try_reserve_exact(value.len())
        .map_err(|_| ForeignContractError {
            span,
            message: "foreign declaration storage exhausted",
            resource: true,
        })?;
    copy.push_str(value);
    Ok(copy)
}

/// A declared C link name; the resolved signature supplies its pointer/void ABI.
#[derive(Debug)]
pub struct PreparedForeignSymbol {
    pub(crate) member_index: usize,
    pub(crate) name: String,
    pub(crate) native_name: String,
    pub(crate) origin: Origin,
}
impl PreparedForeignSymbol {
    pub const fn member_index(&self) -> usize {
        self.member_index
    }
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn native_name(&self) -> &str {
        &self.native_name
    }
    pub const fn origin(&self) -> &Origin {
        &self.origin
    }
}

/// One passive library. No foreign lifecycle or behavior policy is interpreted.
#[derive(Debug)]
pub struct PreparedForeignLibrary {
    pub(crate) module: ModuleId,
    pub(crate) name: String,
    pub(crate) public: bool,
    pub(crate) symbols: Vec<PreparedForeignSymbol>,
    pub(crate) origin: Origin,
}
impl PreparedForeignLibrary {
    pub const fn module(&self) -> ModuleId {
        self.module
    }
    pub fn name(&self) -> &str {
        &self.name
    }
    pub const fn public(&self) -> bool {
        self.public
    }
    pub fn symbols(&self) -> &[PreparedForeignSymbol] {
        &self.symbols
    }
    pub const fn origin(&self) -> &Origin {
        &self.origin
    }
}

/// Checks supported library syntax without loading or running native code.
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
    paid(work, source.members.len(), source.span)?;
    let mut profile = false;
    let mut symbols = Vec::new();
    symbols
        .try_reserve_exact(source.members.len())
        .map_err(|_| ForeignContractError {
            span: source.span,
            message: "foreign declaration storage exhausted",
            resource: true,
        })?;
    for (member_index, member) in source.members.iter().enumerate() {
        match member {
            SurfaceForeignMember::Profile(value) if !profile && value.target.value == PROFILE => {
                profile = true;
            }
            SurfaceForeignMember::Symbol(symbol) => {
                if symbol.native_name.value.is_empty() || symbol.native_name.value.contains('\0') {
                    return Err(ForeignContractError::new(
                        symbol.native_name.span,
                        "invalid native symbol name",
                    ));
                }
                paid(work, symbols.len(), symbol.span)?;
                if symbols
                    .iter()
                    .any(|value: &PreparedForeignSymbol| value.name == symbol.name.text)
                {
                    return Err(ForeignContractError::new(
                        symbol.span,
                        "duplicate foreign symbol",
                    ));
                }
                symbols.push(PreparedForeignSymbol {
                    member_index,
                    name: text(&symbol.name.text, symbol.name.span, work)?,
                    native_name: text(&symbol.native_name.value, symbol.native_name.span, work)?,
                    origin: Origin::Source(symbol.span),
                });
            }
            _ => {
                return Err(ForeignContractError::new(
                    source.span,
                    "unsupported foreign library member",
                ));
            }
        }
    }
    if !profile {
        return Err(ForeignContractError::new(
            source.span,
            "one supported foreign profile is required",
        ));
    }
    Ok(PreparedForeignLibrary {
        module,
        name: text(&source.name.text, source.name.span, work)?,
        public: source.public,
        symbols,
        origin: Origin::Source(source.span),
    })
}
