//! Exact lexical copy-window metadata. Passive facts do not grant a live loan.

use std::sync::Arc;

use super::{NativeInterpretation, NodeId};
use crate::{
    foreign::source_access::CheckedForeignAccess,
    types::{EffectRow, KindedArgument, Type, TypeVariableId, TypeWorkBudget},
};

#[derive(Debug)]
struct WindowDescriptor {
    family: Arc<CheckedForeignAccess>,
    arguments: Box<[KindedArgument]>,
    identity: TypeVariableId,
    interpretations: Box<[NativeInterpretation]>,
}
impl Drop for WindowDescriptor {
    fn drop(&mut self) {
        for argument in std::mem::take(&mut self.arguments).into_vec() {
            crate::types::discard_kinded_argument_iteratively(argument);
        }
    }
}
impl PartialEq for WindowDescriptor {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self, other)
    }
}
impl Eq for WindowDescriptor {}

/// A finite fresh-window boundary. Independent original/copy/phase and lifetime
/// checks are required before this node can enter an executable program.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceCopyWindowNode {
    descriptor: Arc<WindowDescriptor>,
    pub(crate) state: NodeId,
    pub(crate) body: NodeId,
}
impl SourceCopyWindowNode {
    pub(crate) fn new(
        family: Arc<CheckedForeignAccess>,
        arguments: Box<[KindedArgument]>,
        identity: TypeVariableId,
        interpretations: Box<[NativeInterpretation]>,
        state: NodeId,
        body: NodeId,
    ) -> Self {
        Self {
            descriptor: Arc::new(WindowDescriptor {
                family,
                arguments,
                identity,
                interpretations,
            }),
            state,
            body,
        }
    }
    pub(crate) fn family(&self) -> &Arc<CheckedForeignAccess> {
        &self.descriptor.family
    }
    pub(crate) fn matches_view_type(
        &self,
        ty: &Type,
        work: &mut TypeWorkBudget,
    ) -> Result<bool, ()> {
        matches_view_type(self.family(), self.arguments(), ty, work)
    }
    pub(crate) fn arguments(&self) -> &[KindedArgument] {
        &self.descriptor.arguments
    }
    pub(crate) fn identity(&self) -> TypeVariableId {
        self.descriptor.identity
    }
    pub(crate) fn identity_kind(&self) -> &'static crate::types::Kind {
        static KIND: crate::types::Kind = crate::types::Kind::Type;
        &KIND
    }
    pub(crate) fn interpretations(&self) -> &[NativeInterpretation] {
        &self.descriptor.interpretations
    }
    pub(crate) fn state(&self) -> NodeId {
        self.state
    }
    pub(crate) fn body(&self) -> NodeId {
        self.body
    }
}

impl SourceCopyWindowNode {
    /// Rewriting a copied descriptor never changes another retained occurrence.
    pub(crate) fn finalize_instantiation(
        &mut self,
        rewrite: &mut dyn FnMut(&Type) -> Result<Type, super::BuildError>,
        rewrite_row: &mut dyn FnMut(&EffectRow) -> Result<EffectRow, super::BuildError>,
        work: &mut TypeWorkBudget,
    ) -> Result<(), super::BuildError> {
        if Arc::get_mut(&mut self.descriptor).is_none() {
            let arguments =
                crate::types::clone_kinded_arguments_with_budget(self.arguments().iter(), work)
                    .map_err(|()| super::BuildError::TypeWorkExceeded)?;
            let interpretations = super::effect::copy_native_interpretations_with_budget(
                self.interpretations(),
                work,
            )?;
            work.charge(1)
                .map_err(|()| super::BuildError::TypeWorkExceeded)?;
            self.descriptor = Arc::new(WindowDescriptor {
                family: Arc::clone(self.family()),
                arguments,
                identity: self.identity(),
                interpretations,
            });
        }
        let descriptor =
            Arc::get_mut(&mut self.descriptor).ok_or(super::BuildError::InvalidPayload)?;
        super::source_resource::finalize_arguments(
            &mut descriptor.arguments,
            rewrite,
            rewrite_row,
            work,
        )?;
        for interpretation in &mut descriptor.interpretations {
            super::source_resource::finalize_instance(
                &mut interpretation.effect,
                rewrite,
                rewrite_row,
                work,
            )?;
        }
        Ok(())
    }
}

/// Compare the saturated family application without erasing ordered kind tags.
/// This bounded family profile has Type arguments; row-bearing applications do
/// not gain an implicit encoding by dropping those arguments.
pub(crate) fn matches_view_type(
    family: &CheckedForeignAccess,
    arguments: &[KindedArgument],
    ty: &Type,
    work: &mut TypeWorkBudget,
) -> Result<bool, ()> {
    let mut head = ty;
    for argument in arguments.iter().rev() {
        work.charge(1)?;
        let (KindedArgument::TypeArg(expected), Type::Application(function, actual)) =
            (argument, head)
        else {
            return Ok(false);
        };
        if !crate::types::same_type_with_budget(expected, actual, work)? {
            return Ok(false);
        }
        head = function;
    }
    Ok(*head == Type::Nominal(family.nominal()))
}
