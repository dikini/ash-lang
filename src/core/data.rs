//! Typed tuple, constructor, pattern, and structured-match Core payloads.

use super::{NodeId, TypedBinder};
use crate::{
    source::Origin,
    types::{ConstructorId, Type},
};

/// A strict structural tuple construction.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TupleNode {
    elements: Box<[NodeId]>,
}

impl TupleNode {
    pub(crate) fn new(elements: Vec<NodeId>) -> Self {
        Self {
            elements: elements.into_boxed_slice(),
        }
    }

    /// Returns tuple elements in evaluation order.
    #[must_use]
    pub fn elements(&self) -> &[NodeId] {
        &self.elements
    }
}

/// A nullary constructor value or unary payload-constructor function.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ConstructorNode {
    constructor: ConstructorId,
}

impl ConstructorNode {
    pub(crate) const fn new(constructor: ConstructorId) -> Self {
        Self { constructor }
    }

    /// Returns the stable constructor identity.
    #[must_use]
    pub const fn constructor(self) -> ConstructorId {
        self.constructor
    }
}

/// A typed structured pattern retained in Core.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CorePattern {
    /// Expected scrutinee type.
    pub ty: Type,
    /// Causal pattern provenance.
    pub origin: Origin,
    /// Structured pattern payload.
    pub kind: CorePatternKind,
}

impl CorePattern {
    /// Constructs an unchecked typed pattern for independent validation.
    #[must_use]
    pub const fn new(ty: Type, origin: Origin, kind: CorePatternKind) -> Self {
        Self { ty, origin, kind }
    }

    /// Visits every binder definition in deterministic left-to-right order.
    pub(crate) fn binders<'a>(&'a self, output: &mut Vec<&'a TypedBinder>) {
        let mut work = vec![self];
        while let Some(pattern) = work.pop() {
            match &pattern.kind {
                CorePatternKind::Binder(binder) => output.push(binder),
                CorePatternKind::Tuple(elements) => work.extend(elements.iter().rev()),
                CorePatternKind::Constructor { payload, .. } => {
                    if let Some(payload) = payload.as_deref() {
                        work.push(payload);
                    }
                }
                CorePatternKind::Wildcard | CorePatternKind::Boolean(_) | CorePatternKind::Unit => {
                }
            }
        }
    }

    pub(super) fn rewrite_types<F>(&mut self, rewrite: &mut F) -> Result<(), super::BuildError>
    where
        F: FnMut(&Type) -> Result<Type, super::BuildError>,
    {
        let mut work = vec![self];
        while let Some(pattern) = work.pop() {
            pattern.ty = rewrite(&pattern.ty)?;
            match &mut pattern.kind {
                CorePatternKind::Binder(binder) => binder.rewrite_type(rewrite)?,
                CorePatternKind::Tuple(elements) => work.extend(elements.iter_mut()),
                CorePatternKind::Constructor { payload, .. } => {
                    if let Some(payload) = payload.as_deref_mut() {
                        work.push(payload);
                    }
                }
                CorePatternKind::Wildcard | CorePatternKind::Boolean(_) | CorePatternKind::Unit => {
                }
            }
        }
        Ok(())
    }
}

/// The closed typed-pattern family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CorePatternKind {
    /// A stable binder definition.
    Binder(TypedBinder),
    /// A nonbinding wildcard.
    Wildcard,
    /// A Boolean literal pattern.
    Boolean(bool),
    /// Unit.
    Unit,
    /// A structural tuple pattern.
    Tuple(Box<[CorePattern]>),
    /// A nominal constructor and optional payload pattern.
    Constructor {
        /// Stable constructor identity.
        constructor: ConstructorId,
        /// Optional semantic payload pattern.
        payload: Option<Box<CorePattern>>,
    },
}

/// One source-ordered structured-match arm.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CoreMatchArm {
    pattern: CorePattern,
    body: NodeId,
    origin: Origin,
}

impl CoreMatchArm {
    /// Constructs one unchecked match arm.
    #[must_use]
    pub const fn new(pattern: CorePattern, body: NodeId, origin: Origin) -> Self {
        Self {
            pattern,
            body,
            origin,
        }
    }

    /// Returns the arm pattern.
    #[must_use]
    pub const fn pattern(&self) -> &CorePattern {
        &self.pattern
    }

    /// Returns the selected body handle.
    #[must_use]
    pub const fn body(&self) -> NodeId {
        self.body
    }

    /// Returns arm provenance.
    #[must_use]
    pub const fn origin(&self) -> &Origin {
        &self.origin
    }

    pub(super) fn into_parts(self) -> (CorePattern, NodeId, Origin) {
        (self.pattern, self.body, self.origin)
    }

    pub(super) fn pattern_mut(&mut self) -> &mut CorePattern {
        &mut self.pattern
    }
}

/// A structured match whose scrutinee is evaluated once.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MatchNode {
    scrutinee: NodeId,
    arms: Box<[CoreMatchArm]>,
}

impl MatchNode {
    pub(crate) fn new(scrutinee: NodeId, arms: Vec<CoreMatchArm>) -> Self {
        Self {
            scrutinee,
            arms: arms.into_boxed_slice(),
        }
    }

    /// Returns the scrutinee handle.
    #[must_use]
    pub const fn scrutinee(&self) -> NodeId {
        self.scrutinee
    }

    /// Returns arms in selection order.
    #[must_use]
    pub fn arms(&self) -> &[CoreMatchArm] {
        &self.arms
    }

    pub(super) fn arms_mut(&mut self) -> &mut [CoreMatchArm] {
        &mut self.arms
    }
}
