//! Bounded inventory of original source occurrences for final provider copying.

use super::{EvidenceValidationFailure, invalid_root, type_resource};
use crate::{
    resolved::{
        ResolvedDefinitionKind, ResolvedExpr, ResolvedExprKind, ResolvedLocalDeclaration,
        ResolvedModuleProgram,
    },
    source::Span,
    types::TypeWorkBudget,
};
use std::collections::HashSet;

enum SourceItem<'a> {
    Expression(&'a ResolvedExpr),
    Block(&'a crate::resolved::ResolvedBlock),
}

pub(super) struct SourceScopeOccurrences<'a> {
    pub(super) resources: Vec<SourceProviderOccurrence<'a>>,
    pub(super) hosts: Vec<(&'a crate::resolved::ResolvedForeignHostExpr, Span)>,
}

fn push<'a>(
    pending: &mut Vec<SourceItem<'a>>,
    item: SourceItem<'a>,
    work: &mut TypeWorkBudget,
    span: Span,
) -> Result<(), EvidenceValidationFailure> {
    work.charge(1).map_err(|()| type_resource(span))?;
    pending.try_reserve(1).map_err(|_| type_resource(span))?;
    pending.push(item);
    Ok(())
}
