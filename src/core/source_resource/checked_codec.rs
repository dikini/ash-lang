//! Canonical checked lifecycle codec roles, without execution authority.
//!
//! The caller's module/source admission authenticates actual immutable builtin
//! bytes. This reconstruction checks the retained registry's original roles and
//! every resource application independently; a matching shape is insufficient.

use super::{
    SourceResourceCodec, SourceResourceReportCodec, ValidationError, acquire_codec, application,
    charge, constructors, invalid, resource, same, variable,
};
use crate::{
    foreign::checked_builtins::authenticate_checked_builtins,
    module::{FOREIGN_NATIVE_HOST_LOCAL, ForeignCheckedNominalRole as Role},
    resolved::{ResolvedRegistry, SourceResourceTypeFact},
    surface::SurfaceResourceReportCodecKind,
    types::{EffectId, NominalTypeId, TypeWorkBudget},
};

pub(super) fn authenticate(
    header: &SourceResourceTypeFact,
    registry: &ResolvedRegistry,
    work: &mut TypeWorkBudget,
) -> Result<SourceResourceCodec, ValidationError> {
    charge(work, 1)?;
    if header.codec.kind != SurfaceResourceReportCodecKind::CheckedScope {
        return Err(invalid());
    }
    let (acquisition, acquisition_arguments) = application(&header.acquisition.ty, work)?;
    let (finish, finish_arguments) = application(&header.completion.ty, work)?;
    let (scope, scope_arguments) = application(&header.result.ty, work)?;
    let module = finish.module();
    charge(work, 4)?;
    if !module.is_builtin_foreign()
        || finish != NominalTypeId::new(module, Role::CheckedFinish.local())
        || scope != NominalTypeId::new(module, Role::CheckedScope.local())
        || acquisition_arguments.len() != 3
        || finish_arguments.len() != 2
        || scope_arguments.len() != 3
    {
        return Err(invalid());
    }

    // The synthetic NativeHost declaration's full-source causal span is the
    // original coordinate anchor. It grants no byte or native authority here.
    charge(work, 1)?;
    let host = registry
        .effect(EffectId::new(module, FOREIGN_NATIVE_HOST_LOCAL))
        .ok_or_else(invalid)?;
    authenticate_checked_builtins(registry, module, host.span, work).map_err(|error| {
        if error.is_resource_exhaustion() {
            resource()
        } else {
            invalid()
        }
    })?;

    // CheckedScope orders its actuals as Answer, I, E, unlike legacy Scope.
    charge(work, 1)?;
    if !same(acquisition_arguments[0], &header.state.ty, work)?
        || !same(acquisition_arguments[1], &header.data.ty, work)?
        || !same(finish_arguments[0], &header.state.ty, work)?
        || !variable(scope_arguments[0], header.answer.id)
        || !same(scope_arguments[1], acquisition_arguments[2], work)?
        || !same(scope_arguments[2], finish_arguments[1], work)?
    {
        return Err(invalid());
    }

    // Full builtin reconstruction above includes FinishResult (role 13), the
    // exact CheckedFinish/CheckedCompletion payloads (14/15), and CheckedScope
    // (16). These paid row reads retain only their original constructor IDs.
    Ok(SourceResourceCodec {
        acquire: acquire_codec(acquisition, registry, work)?,
        finish: constructors::<3>(finish, 2, registry, work)?,
        report: SourceResourceReportCodec::CheckedScope {
            report: constructors::<2>(scope, 3, registry, work)?,
            completion: constructors::<3>(
                NominalTypeId::new(module, Role::CheckedCompletion.local()),
                1,
                registry,
                work,
            )?,
        },
    })
}
