//! Binder definitions and variable occurrences in typed Core.

use super::dialect::{ArenaId, NodeId};
use crate::{resolved::BinderId, source::Origin, types::Type};

/// A typed Core binder definition and opaque capability for its owning arena.
///
/// A binder may be cloned for multiple same-arena occurrences, but only the
/// [`super::dialect::CoreBuilder`] that produced it can place it at a
/// definition site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TypedBinder {
    arena: ArenaId,
    id: BinderId,
    ty: Type,
    origin: Origin,
}

impl TypedBinder {
    pub(super) const fn new(arena: ArenaId, id: BinderId, ty: Type, origin: Origin) -> Self {
        Self {
            arena,
            id,
            ty,
            origin,
        }
    }

    pub(super) const fn arena(&self) -> ArenaId {
        self.arena
    }

    /// Returns the resolver identity retained by this binder.
    #[must_use]
    pub const fn id(&self) -> BinderId {
        self.id
    }

    /// Returns the binder's structural type.
    #[must_use]
    pub const fn ty(&self) -> &Type {
        &self.ty
    }

    /// Returns the binder's causal provenance.
    #[must_use]
    pub const fn origin(&self) -> &Origin {
        &self.origin
    }
}

/// A resolved variable occurrence payload.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct VariableNode {
    binder: BinderId,
}

impl VariableNode {
    pub(super) const fn new(binder: BinderId) -> Self {
        Self { binder }
    }

    /// Returns the selected binder identity.
    #[must_use]
    pub const fn binder(self) -> BinderId {
        self.binder
    }

    pub(super) const fn children(self) -> [Option<NodeId>; 2] {
        [None, None]
    }
}
