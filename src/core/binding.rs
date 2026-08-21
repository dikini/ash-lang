//! Sequential nonrecursive bindings in typed Core.

use super::{dialect::NodeId, variable::TypedBinder};

/// A nonrecursive binding payload.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BindingNode {
    binder: TypedBinder,
    initializer: NodeId,
    body: NodeId,
}

impl BindingNode {
    pub(super) const fn new(binder: TypedBinder, initializer: NodeId, body: NodeId) -> Self {
        Self {
            binder,
            initializer,
            body,
        }
    }

    /// Returns the introduced binder.
    #[must_use]
    pub const fn binder(&self) -> &TypedBinder {
        &self.binder
    }

    /// Returns the initializer evaluated in the incoming scope.
    #[must_use]
    pub const fn initializer(&self) -> NodeId {
        self.initializer
    }

    /// Returns the body evaluated with the binder in scope.
    #[must_use]
    pub const fn body(&self) -> NodeId {
        self.body
    }
}
