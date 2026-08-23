//! Simultaneous recursive bindings in typed Core.

use super::{dialect::NodeId, variable::TypedBinder};

/// One typed initializer in a recursive binding group.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecursiveBindingMember {
    binder: TypedBinder,
    initializer: NodeId,
}

impl RecursiveBindingMember {
    pub(super) const fn new(binder: TypedBinder, initializer: NodeId) -> Self {
        Self {
            binder,
            initializer,
        }
    }

    /// Returns the binder visible throughout the recursive group.
    #[must_use]
    pub const fn binder(&self) -> &TypedBinder {
        &self.binder
    }

    /// Returns the function or guarded-data node that initializes this member.
    #[must_use]
    pub const fn initializer(&self) -> NodeId {
        self.initializer
    }

    pub(super) fn binder_mut(&mut self) -> &mut TypedBinder {
        &mut self.binder
    }

    fn discard_metadata(self) {
        self.binder.discard_metadata();
    }
}

/// A simultaneous recursive binding group followed by its lexical body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecursiveBindingNode {
    members: Box<[RecursiveBindingMember]>,
    body: NodeId,
}

impl RecursiveBindingNode {
    pub(super) fn new(members: Vec<RecursiveBindingMember>, body: NodeId) -> Self {
        Self {
            members: members.into_boxed_slice(),
            body,
        }
    }

    /// Returns the members in source order.
    #[must_use]
    pub const fn members(&self) -> &[RecursiveBindingMember] {
        &self.members
    }

    pub(super) fn members_mut(&mut self) -> &mut [RecursiveBindingMember] {
        &mut self.members
    }

    /// Returns the body evaluated with every member in scope.
    #[must_use]
    pub const fn body(&self) -> NodeId {
        self.body
    }

    pub(super) const fn child_count(&self) -> usize {
        self.members.len() + 1
    }

    pub(super) fn child_at(&self, index: usize) -> Option<NodeId> {
        if index == self.members.len() {
            return Some(self.body);
        }
        self.members
            .get(index)
            .map(RecursiveBindingMember::initializer)
    }

    pub(super) fn discard_metadata(self) {
        for member in self.members.into_vec() {
            member.discard_metadata();
        }
    }
}
