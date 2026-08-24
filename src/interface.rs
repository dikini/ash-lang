//! Stable typed identities for resolved interfaces and implementations.

use crate::{module::ModuleId, resolved::BinderId};

/// Stable identity of one interface declaration.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InterfaceId {
    module: ModuleId,
    declaration: u32,
}

impl InterfaceId {
    /// Creates the identity for one interface declaration in an admitted module.
    #[must_use]
    pub const fn new(module: ModuleId, declaration: u32) -> Self {
        Self {
            module,
            declaration,
        }
    }

    /// Returns the canonical module that owns the declaration.
    #[must_use]
    pub const fn module(self) -> ModuleId {
        self.module
    }

    /// Returns the source-order interface declaration index.
    #[must_use]
    pub const fn declaration(self) -> u32 {
        self.declaration
    }
}

/// Stable identity of one method declared by an interface.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MethodId {
    interface: InterfaceId,
    declaration: u32,
}

impl MethodId {
    /// Creates the identity for one method in its interface declaration.
    #[must_use]
    pub const fn new(interface: InterfaceId, declaration: u32) -> Self {
        Self {
            interface,
            declaration,
        }
    }

    /// Returns the interface that owns the method.
    #[must_use]
    pub const fn interface(self) -> InterfaceId {
        self.interface
    }

    /// Returns the source-order method declaration index.
    #[must_use]
    pub const fn declaration(self) -> u32 {
        self.declaration
    }
}

/// Stable identity of one implementation declaration.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ImplId {
    module: ModuleId,
    declaration: u32,
}

impl ImplId {
    /// Creates the identity for one implementation declaration in an admitted module.
    #[must_use]
    pub const fn new(module: ModuleId, declaration: u32) -> Self {
        Self {
            module,
            declaration,
        }
    }

    /// Returns the canonical module that owns the declaration.
    #[must_use]
    pub const fn module(self) -> ModuleId {
        self.module
    }

    /// Returns the source-order implementation declaration index.
    #[must_use]
    pub const fn declaration(self) -> u32 {
        self.declaration
    }
}

/// Stable identity of one interface method supplied by an implementation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ImplMethodId {
    implementation: ImplId,
    method: MethodId,
}

impl ImplMethodId {
    /// Creates the identity for one implemented interface method.
    #[must_use]
    pub const fn new(implementation: ImplId, method: MethodId) -> Self {
        Self {
            implementation,
            method,
        }
    }

    /// Returns the implementation that supplies the method.
    #[must_use]
    pub const fn implementation(self) -> ImplId {
        self.implementation
    }

    /// Returns the interface method supplied by the implementation.
    #[must_use]
    pub const fn method(self) -> MethodId {
        self.method
    }
}

/// Declaration that owns one ordered interface requirement.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RequirementOwner {
    /// A requirement declared by a module-level global.
    Global(BinderId),
    /// A prerequisite declared by an implementation.
    Impl(ImplId),
}

/// Stable identity of one ordered interface requirement.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RequirementId {
    owner: RequirementOwner,
    declaration: u32,
}

impl RequirementId {
    /// Creates the identity for one requirement under its declaring owner.
    #[must_use]
    pub const fn new(owner: RequirementOwner, declaration: u32) -> Self {
        Self { owner, declaration }
    }

    /// Returns the global or implementation that owns the requirement.
    #[must_use]
    pub const fn owner(self) -> RequirementOwner {
        self.owner
    }

    /// Returns the source-order requirement declaration index.
    #[must_use]
    pub const fn declaration(self) -> u32 {
        self.declaration
    }
}

/// Structural evidence state owned by one resolved constrained occurrence.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum EvidenceSlot {
    /// Resolution has retained the slot, but checking has not selected evidence.
    Empty,
}

#[cfg(test)]
mod tests {
    use std::any::TypeId;

    use super::*;
    use crate::{module::ModuleId, resolved::BinderId};

    #[test]
    fn interface_and_method_identities_preserve_their_components() {
        let module = ModuleId::new(7);
        let interface = InterfaceId::new(module, 3);
        let method = MethodId::new(interface, 5);

        assert_eq!(interface.module(), module);
        assert_eq!(interface.declaration(), 3);
        assert_eq!(method.interface(), interface);
        assert_eq!(method.declaration(), 5);
    }

    #[test]
    fn implementation_and_method_identities_preserve_their_components() {
        let module = ModuleId::new(11);
        let implementation = ImplId::new(module, 13);
        let interface = InterfaceId::new(module, 17);
        let method = MethodId::new(interface, 19);
        let implementation_method = ImplMethodId::new(implementation, method);

        assert_eq!(implementation.module(), module);
        assert_eq!(implementation.declaration(), 13);
        assert_eq!(implementation_method.implementation(), implementation);
        assert_eq!(implementation_method.method(), method);
    }

    #[test]
    fn requirement_identities_preserve_owner_and_declaration_order() {
        let module = ModuleId::new(23);
        let global = RequirementOwner::Global(BinderId::resolved(module, 29));
        let implementation = RequirementOwner::Impl(ImplId::new(module, 31));
        let first = RequirementId::new(global, 0);
        let second = RequirementId::new(global, 1);
        let prerequisite = RequirementId::new(implementation, 0);

        assert_eq!(first.owner(), global);
        assert_eq!(first.declaration(), 0);
        assert_eq!(second.owner(), global);
        assert_eq!(second.declaration(), 1);
        assert_ne!(first, second);
        assert_eq!(prerequisite.owner(), implementation);
        assert_eq!(prerequisite.declaration(), 0);
    }

    #[test]
    fn semantic_identity_categories_remain_distinct_types() {
        assert_ne!(TypeId::of::<InterfaceId>(), TypeId::of::<ImplId>());
        assert_ne!(TypeId::of::<MethodId>(), TypeId::of::<ImplMethodId>());
        assert_ne!(TypeId::of::<RequirementId>(), TypeId::of::<MethodId>());
        assert_eq!(EvidenceSlot::Empty, EvidenceSlot::Empty);
    }
}
